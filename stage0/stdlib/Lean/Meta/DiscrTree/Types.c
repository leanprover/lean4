// Lean compiler output
// Module: Lean.Meta.DiscrTree.Types
// Imports: public import Lean.Expr
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
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey_default;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instBEqKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DiscrTree_instBEqKey = (const lean_object*)&l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.DiscrTree.Key.arrow"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.DiscrTree.Key.star"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.DiscrTree.Key.other"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.DiscrTree.Key.lit"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.DiscrTree.Key.fvar"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.DiscrTree.Key.const"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.DiscrTree.Key.proj"};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instReprKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instReprKey_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instReprKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DiscrTree_instReprKey = (const lean_object*)&l_Lean_Meta_DiscrTree_instReprKey___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instHashableKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DiscrTree_instHashableKey = (const lean_object*)&l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_chain_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_chain_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_DiscrTree_Key_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 2:
{
lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_a_7_);
return v___x_8_;
}
case 3:
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_9_);
v_a_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_a_9_, v_a_10_);
return v___x_11_;
}
case 4:
{
lean_object* v_a_12_; lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_12_);
v_a_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_13_);
lean_dec_ref_known(v_t_5_, 2);
v___x_14_ = lean_apply_2(v_k_6_, v_a_12_, v_a_13_);
return v___x_14_;
}
case 6:
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_15_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_a_17_);
lean_dec_ref_known(v_t_5_, 3);
v___x_18_ = lean_apply_3(v_k_6_, v_a_15_, v_a_16_, v_a_17_);
return v___x_18_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_DiscrTree_Key_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim___redArg(lean_object* v_t_31_, lean_object* v_star_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_31_, v_star_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_star_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_35_, v_star_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim___redArg(lean_object* v_t_39_, lean_object* v_other_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_39_, v_other_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_other_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_43_, v_other_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim___redArg(lean_object* v_t_47_, lean_object* v_lit_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_47_, v_lit_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_lit_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_51_, v_lit_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim___redArg(lean_object* v_t_55_, lean_object* v_fvar_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_55_, v_fvar_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_fvar_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_59_, v_fvar_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim___redArg(lean_object* v_t_63_, lean_object* v_const_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_63_, v_const_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_const_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_67_, v_const_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim___redArg(lean_object* v_t_71_, lean_object* v_arrow_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_71_, v_arrow_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_arrow_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_75_, v_arrow_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim___redArg(lean_object* v_t_79_, lean_object* v_proj_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_79_, v_proj_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_proj_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_83_, v_proj_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedKey_default(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedKey(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
case 1:
{
if (lean_obj_tag(v_x_90_) == 1)
{
uint8_t v___x_93_; 
v___x_93_ = 1;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
case 2:
{
if (lean_obj_tag(v_x_90_) == 2)
{
lean_object* v_a_95_; lean_object* v_a_96_; uint8_t v___x_97_; 
v_a_95_ = lean_ctor_get(v_x_89_, 0);
v_a_96_ = lean_ctor_get(v_x_90_, 0);
v___x_97_ = l_Lean_instBEqLiteral_beq(v_a_95_, v_a_96_);
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
case 3:
{
if (lean_obj_tag(v_x_90_) == 3)
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v_a_102_; uint8_t v___x_103_; 
v_a_99_ = lean_ctor_get(v_x_89_, 0);
v_a_100_ = lean_ctor_get(v_x_89_, 1);
v_a_101_ = lean_ctor_get(v_x_90_, 0);
v_a_102_ = lean_ctor_get(v_x_90_, 1);
v___x_103_ = l_Lean_instBEqFVarId_beq(v_a_99_, v_a_101_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_eq(v_a_100_, v_a_102_);
return v___x_104_;
}
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
case 4:
{
if (lean_obj_tag(v_x_90_) == 4)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v_a_109_; uint8_t v___x_110_; 
v_a_106_ = lean_ctor_get(v_x_89_, 0);
v_a_107_ = lean_ctor_get(v_x_89_, 1);
v_a_108_ = lean_ctor_get(v_x_90_, 0);
v_a_109_ = lean_ctor_get(v_x_90_, 1);
v___x_110_ = lean_name_eq(v_a_106_, v_a_108_);
if (v___x_110_ == 0)
{
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_eq(v_a_107_, v_a_109_);
return v___x_111_;
}
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
case 5:
{
if (lean_obj_tag(v_x_90_) == 5)
{
uint8_t v___x_113_; 
v___x_113_ = 1;
return v___x_113_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
default: 
{
if (lean_obj_tag(v_x_90_) == 6)
{
lean_object* v_a_115_; lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v_a_120_; uint8_t v___x_121_; 
v_a_115_ = lean_ctor_get(v_x_89_, 0);
v_a_116_ = lean_ctor_get(v_x_89_, 1);
v_a_117_ = lean_ctor_get(v_x_89_, 2);
v_a_118_ = lean_ctor_get(v_x_90_, 0);
v_a_119_ = lean_ctor_get(v_x_90_, 1);
v_a_120_ = lean_ctor_get(v_x_90_, 2);
v___x_121_ = lean_name_eq(v_a_115_, v_a_118_);
if (v___x_121_ == 0)
{
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_eq(v_a_116_, v_a_119_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_eq(v_a_117_, v_a_120_);
return v___x_123_;
}
}
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_instBEqKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_89_ = stack[0].m_obj;
lean_object* v_x_90_ = stack[1].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_89_, v_x_90_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(2u);
v___x_142_ = lean_nat_to_int(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr(lean_object* v_x_169_, lean_object* v_prec_170_){
_start:
{
lean_object* v___y_172_; lean_object* v___y_179_; lean_object* v___y_186_; 
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_170_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_179_ = v___x_194_;
goto v___jp_178_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_179_ = v___x_195_;
goto v___jp_178_;
}
}
case 1:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1024u);
v___x_197_ = lean_nat_dec_le(v___x_196_, v_prec_170_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_186_ = v___x_198_;
goto v___jp_185_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_186_ = v___x_199_;
goto v___jp_185_;
}
}
case 2:
{
lean_object* v_a_200_; lean_object* v___y_202_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_a_200_ = lean_ctor_get(v_x_169_, 0);
lean_inc_ref(v_a_200_);
lean_dec_ref_known(v_x_169_, 1);
v___x_211_ = lean_unsigned_to_nat(1024u);
v___x_212_ = lean_nat_dec_le(v___x_211_, v_prec_170_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_202_ = v___x_213_;
goto v___jp_201_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_202_ = v___x_214_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10));
v___x_204_ = lean_unsigned_to_nat(1024u);
v___x_205_ = l_Lean_instReprLiteral_repr(v_a_200_, v___x_204_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
lean_inc(v___y_202_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_208_);
v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_170_);
return v___x_210_;
}
}
case 3:
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_241_; 
v_a_215_ = lean_ctor_get(v_x_169_, 0);
v_a_216_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_241_ == 0)
{
v___x_218_ = v_x_169_;
v_isShared_219_ = v_isSharedCheck_241_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_inc(v_a_215_);
lean_dec(v_x_169_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_241_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___y_221_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1024u);
v___x_238_ = lean_nat_dec_le(v___x_237_, v_prec_170_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_221_ = v___x_239_;
goto v___jp_220_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_221_ = v___x_240_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_222_ = lean_box(1);
v___x_223_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13));
v___x_224_ = lean_unsigned_to_nat(1024u);
v___x_225_ = l_Lean_Name_reprPrec(v_a_215_, v___x_224_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 5);
lean_ctor_set(v___x_218_, 1, v___x_225_);
lean_ctor_set(v___x_218_, 0, v___x_223_);
v___x_227_ = v___x_218_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_236_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_222_);
v___x_229_ = l_Nat_reprFast(v_a_216_);
v___x_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_228_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_inc(v___y_221_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___y_221_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = l_Repr_addAppParen(v___x_234_, v_prec_170_);
return v___x_235_;
}
}
}
}
case 4:
{
lean_object* v_a_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_268_; 
v_a_242_ = lean_ctor_get(v_x_169_, 0);
v_a_243_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_268_ == 0)
{
v___x_245_ = v_x_169_;
v_isShared_246_ = v_isSharedCheck_268_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_inc(v_a_242_);
lean_dec(v_x_169_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_268_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1024u);
v___x_265_ = lean_nat_dec_le(v___x_264_, v_prec_170_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_248_ = v___x_266_;
goto v___jp_247_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_248_ = v___x_267_;
goto v___jp_247_;
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_249_ = lean_box(1);
v___x_250_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16));
v___x_251_ = lean_unsigned_to_nat(1024u);
v___x_252_ = l_Lean_Name_reprPrec(v_a_242_, v___x_251_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 5);
lean_ctor_set(v___x_245_, 1, v___x_252_);
lean_ctor_set(v___x_245_, 0, v___x_250_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_263_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_249_);
v___x_256_ = l_Nat_reprFast(v_a_243_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_255_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_inc(v___y_248_);
v___x_259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_259_, 0, v___y_248_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = 0;
v___x_261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set_uint8(v___x_261_, sizeof(void*)*1, v___x_260_);
v___x_262_ = l_Repr_addAppParen(v___x_261_, v_prec_170_);
return v___x_262_;
}
}
}
}
case 5:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_170_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_172_ = v___x_271_;
goto v___jp_171_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_172_ = v___x_272_;
goto v___jp_171_;
}
}
default: 
{
lean_object* v_a_273_; lean_object* v_a_274_; lean_object* v_a_275_; lean_object* v___y_277_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_a_273_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_a_273_);
v_a_274_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_a_274_);
v_a_275_ = lean_ctor_get(v_x_169_, 2);
lean_inc(v_a_275_);
lean_dec_ref_known(v_x_169_, 3);
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_170_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_277_ = v___x_297_;
goto v___jp_276_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_277_ = v___x_298_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_278_ = lean_box(1);
v___x_279_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19));
v___x_280_ = lean_unsigned_to_nat(1024u);
v___x_281_ = l_Lean_Name_reprPrec(v_a_273_, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_279_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_278_);
v___x_284_ = l_Nat_reprFast(v_a_274_);
v___x_285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_278_);
v___x_288_ = l_Nat_reprFast(v_a_275_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_inc(v___y_277_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_277_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 0;
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_292_);
v___x_294_ = l_Repr_addAppParen(v___x_293_, v_prec_170_);
return v___x_294_;
}
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1));
lean_inc(v___y_172_);
v___x_174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_174_, 0, v___y_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = 0;
v___x_176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*1, v___x_175_);
v___x_177_ = l_Repr_addAppParen(v___x_176_, v_prec_170_);
return v___x_177_;
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3));
lean_inc(v___y_179_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_170_);
return v___x_184_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5));
lean_inc(v___y_186_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_170_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___boxed(lean_object* v_x_299_, lean_object* v_prec_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_x_299_, v_prec_300_);
lean_dec(v_prec_300_);
return v_res_301_;
}
}
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object* v_x_304_){
_start:
{
switch(lean_obj_tag(v_x_304_))
{
case 0:
{
uint64_t v___x_305_; 
v___x_305_ = 7883ULL;
return v___x_305_;
}
case 1:
{
uint64_t v___x_306_; 
v___x_306_ = 2411ULL;
return v___x_306_;
}
case 2:
{
lean_object* v_a_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; 
v_a_307_ = lean_ctor_get(v_x_304_, 0);
v___x_308_ = 1879ULL;
v___x_309_ = l_Lean_Literal_hash(v_a_307_);
v___x_310_ = lean_uint64_mix_hash(v___x_308_, v___x_309_);
return v___x_310_;
}
case 3:
{
lean_object* v_a_311_; lean_object* v_a_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; 
v_a_311_ = lean_ctor_get(v_x_304_, 0);
v_a_312_ = lean_ctor_get(v_x_304_, 1);
v___x_313_ = 3541ULL;
v___x_314_ = l_Lean_instHashableFVarId_hash(v_a_311_);
v___x_315_ = lean_uint64_of_nat(v_a_312_);
v___x_316_ = lean_uint64_mix_hash(v___x_314_, v___x_315_);
v___x_317_ = lean_uint64_mix_hash(v___x_313_, v___x_316_);
return v___x_317_;
}
case 4:
{
lean_object* v_a_318_; lean_object* v_a_319_; uint64_t v___x_320_; uint64_t v___y_322_; 
v_a_318_ = lean_ctor_get(v_x_304_, 0);
v_a_319_ = lean_ctor_get(v_x_304_, 1);
v___x_320_ = 5237ULL;
if (lean_obj_tag(v_a_318_) == 0)
{
uint64_t v___x_326_; 
v___x_326_ = 1723ULL;
v___y_322_ = v___x_326_;
goto v___jp_321_;
}
else
{
uint64_t v_hash_327_; 
v_hash_327_ = lean_ctor_get_uint64(v_a_318_, sizeof(void*)*2);
v___y_322_ = v_hash_327_;
goto v___jp_321_;
}
v___jp_321_:
{
uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; 
v___x_323_ = lean_uint64_of_nat(v_a_319_);
v___x_324_ = lean_uint64_mix_hash(v___y_322_, v___x_323_);
v___x_325_ = lean_uint64_mix_hash(v___x_320_, v___x_324_);
return v___x_325_;
}
}
case 5:
{
uint64_t v___x_328_; 
v___x_328_ = 17ULL;
return v___x_328_;
}
default: 
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v_a_331_; uint64_t v___x_332_; uint64_t v___y_334_; 
v_a_329_ = lean_ctor_get(v_x_304_, 0);
v_a_330_ = lean_ctor_get(v_x_304_, 1);
v_a_331_ = lean_ctor_get(v_x_304_, 2);
v___x_332_ = lean_uint64_of_nat(v_a_331_);
if (lean_obj_tag(v_a_329_) == 0)
{
uint64_t v___x_338_; 
v___x_338_ = 1723ULL;
v___y_334_ = v___x_338_;
goto v___jp_333_;
}
else
{
uint64_t v_hash_339_; 
v_hash_339_ = lean_ctor_get_uint64(v_a_329_, sizeof(void*)*2);
v___y_334_ = v_hash_339_;
goto v___jp_333_;
}
v___jp_333_:
{
uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; 
v___x_335_ = lean_uint64_of_nat(v_a_330_);
v___x_336_ = lean_uint64_mix_hash(v___y_334_, v___x_335_);
v___x_337_ = lean_uint64_mix_hash(v___x_332_, v___x_336_);
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_Key_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_304_ = stack[0].m_obj;
uint64_t v_res_340_;
v_res_340_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_304_);
stack->m_num = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object* v_x_341_){
_start:
{
uint64_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_341_);
lean_dec(v_x_341_);
v_r_343_ = lean_box_uint64(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___redArg(lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_tag_nat(v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___redArg___boxed(lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___redArg(v_x_348_);
lean_dec_ref(v_x_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl(lean_object* v_00_u03b1_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_tag_nat(v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl___boxed(lean_object* v_00_u03b1_353_, lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Meta_DiscrTree_Trie_ctorIdx___impl(v_00_u03b1_353_, v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(lean_object* v_t_356_, lean_object* v_k_357_){
_start:
{
if (lean_obj_tag(v_t_356_) == 0)
{
lean_object* v_key_358_; lean_object* v_child_359_; lean_object* v___x_360_; 
v_key_358_ = lean_ctor_get(v_t_356_, 0);
lean_inc(v_key_358_);
v_child_359_ = lean_ctor_get(v_t_356_, 1);
lean_inc_ref(v_child_359_);
lean_dec_ref_known(v_t_356_, 2);
v___x_360_ = lean_apply_2(v_k_357_, v_key_358_, v_child_359_);
return v___x_360_;
}
else
{
lean_object* v_vs_361_; lean_object* v_children_362_; lean_object* v___x_363_; 
v_vs_361_ = lean_ctor_get(v_t_356_, 0);
lean_inc_ref(v_vs_361_);
v_children_362_ = lean_ctor_get(v_t_356_, 1);
lean_inc_ref(v_children_362_);
lean_dec_ref_known(v_t_356_, 2);
v___x_363_ = lean_apply_2(v_k_357_, v_vs_361_, v_children_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim(lean_object* v_00_u03b1_364_, lean_object* v_motive__1_365_, lean_object* v_ctorIdx_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_k_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(v_t_367_, v_k_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_ctorElim___boxed(lean_object* v_00_u03b1_371_, lean_object* v_motive__1_372_, lean_object* v_ctorIdx_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_k_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_DiscrTree_Trie_ctorElim(v_00_u03b1_371_, v_motive__1_372_, v_ctorIdx_373_, v_t_374_, v_h_375_, v_k_376_);
lean_dec(v_ctorIdx_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_chain_elim___redArg(lean_object* v_t_378_, lean_object* v_chain_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(v_t_378_, v_chain_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_chain_elim(lean_object* v_00_u03b1_381_, lean_object* v_motive__1_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_chain_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(v_t_383_, v_chain_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_node_elim___redArg(lean_object* v_t_387_, lean_object* v_node_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(v_t_387_, v_node_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_node_elim(lean_object* v_00_u03b1_390_, lean_object* v_motive__1_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_node_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_DiscrTree_Trie_ctorElim___redArg(v_t_392_, v_node_394_);
return v___x_395_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_instInhabitedKey_default = _init_l_Lean_Meta_DiscrTree_instInhabitedKey_default();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedKey_default);
l_Lean_Meta_DiscrTree_instInhabitedKey = _init_l_Lean_Meta_DiscrTree_instInhabitedKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedKey);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_DiscrTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_DiscrTree_Types(builtin);
}
#ifdef __cplusplus
}
#endif
