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
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_DiscrTree_Key_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_DiscrTree_Key_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instHashableKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DiscrTree_instHashableKey = (const lean_object*)&l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 2:
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_13_);
lean_dec_ref(v_t_11_);
v___x_14_ = lean_apply_1(v_k_12_, v_a_13_);
return v___x_14_;
}
case 3:
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_16_);
lean_dec_ref(v_t_11_);
v___x_17_ = lean_apply_2(v_k_12_, v_a_15_, v_a_16_);
return v___x_17_;
}
case 4:
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_19_);
lean_dec_ref(v_t_11_);
v___x_20_ = lean_apply_2(v_k_12_, v_a_18_, v_a_19_);
return v___x_20_;
}
case 6:
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_21_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_22_);
v_a_23_ = lean_ctor_get(v_t_11_, 2);
lean_inc(v_a_23_);
lean_dec_ref(v_t_11_);
v___x_24_ = lean_apply_3(v_k_12_, v_a_21_, v_a_22_, v_a_23_);
return v___x_24_;
}
default: 
{
lean_dec(v_t_11_);
return v_k_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_ctorElim___boxed(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Meta_DiscrTree_Key_ctorElim(v_motive_31_, v_ctorIdx_32_, v_t_33_, v_h_34_, v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim___redArg(lean_object* v_t_37_, lean_object* v_star_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_37_, v_star_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_star_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_star_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_41_, v_star_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim___redArg(lean_object* v_t_45_, lean_object* v_other_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_45_, v_other_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_other_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_other_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_49_, v_other_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim___redArg(lean_object* v_t_53_, lean_object* v_lit_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_53_, v_lit_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lit_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_lit_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_57_, v_lit_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim___redArg(lean_object* v_t_61_, lean_object* v_fvar_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_61_, v_fvar_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_fvar_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_fvar_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_65_, v_fvar_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim___redArg(lean_object* v_t_69_, lean_object* v_const_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_69_, v_const_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_const_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_const_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_73_, v_const_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim___redArg(lean_object* v_t_77_, lean_object* v_arrow_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_77_, v_arrow_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arrow_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_arrow_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_81_, v_arrow_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim___redArg(lean_object* v_t_85_, lean_object* v_proj_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_85_, v_proj_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_proj_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_proj_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_89_, v_proj_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedKey_default(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedKey(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
if (lean_obj_tag(v_x_96_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
case 1:
{
if (lean_obj_tag(v_x_96_) == 1)
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
case 2:
{
if (lean_obj_tag(v_x_96_) == 2)
{
lean_object* v_a_101_; lean_object* v_a_102_; uint8_t v___x_103_; 
v_a_101_ = lean_ctor_get(v_x_95_, 0);
v_a_102_ = lean_ctor_get(v_x_96_, 0);
v___x_103_ = l_Lean_instBEqLiteral_beq(v_a_101_, v_a_102_);
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
case 3:
{
if (lean_obj_tag(v_x_96_) == 3)
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v_a_108_; uint8_t v___x_109_; 
v_a_105_ = lean_ctor_get(v_x_95_, 0);
v_a_106_ = lean_ctor_get(v_x_95_, 1);
v_a_107_ = lean_ctor_get(v_x_96_, 0);
v_a_108_ = lean_ctor_get(v_x_96_, 1);
v___x_109_ = l_Lean_instBEqFVarId_beq(v_a_105_, v_a_107_);
if (v___x_109_ == 0)
{
return v___x_109_;
}
else
{
uint8_t v___x_110_; 
v___x_110_ = lean_nat_dec_eq(v_a_106_, v_a_108_);
return v___x_110_;
}
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
case 4:
{
if (lean_obj_tag(v_x_96_) == 4)
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v_a_115_; uint8_t v___x_116_; 
v_a_112_ = lean_ctor_get(v_x_95_, 0);
v_a_113_ = lean_ctor_get(v_x_95_, 1);
v_a_114_ = lean_ctor_get(v_x_96_, 0);
v_a_115_ = lean_ctor_get(v_x_96_, 1);
v___x_116_ = lean_name_eq(v_a_112_, v_a_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = lean_nat_dec_eq(v_a_113_, v_a_115_);
return v___x_117_;
}
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
case 5:
{
if (lean_obj_tag(v_x_96_) == 5)
{
uint8_t v___x_119_; 
v___x_119_ = 1;
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
default: 
{
if (lean_obj_tag(v_x_96_) == 6)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v_a_126_; uint8_t v___x_127_; 
v_a_121_ = lean_ctor_get(v_x_95_, 0);
v_a_122_ = lean_ctor_get(v_x_95_, 1);
v_a_123_ = lean_ctor_get(v_x_95_, 2);
v_a_124_ = lean_ctor_get(v_x_96_, 0);
v_a_125_ = lean_ctor_get(v_x_96_, 1);
v_a_126_ = lean_ctor_get(v_x_96_, 2);
v___x_127_ = lean_name_eq(v_a_121_, v_a_124_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_eq(v_a_122_, v_a_125_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_a_123_, v_a_126_);
return v___x_129_;
}
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_131_, v_x_132_);
lean_dec(v_x_132_);
lean_dec(v_x_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(2u);
v___x_147_ = lean_nat_to_int(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr(lean_object* v_x_174_, lean_object* v_prec_175_){
_start:
{
lean_object* v___y_177_; lean_object* v___y_184_; lean_object* v___y_191_; 
switch(lean_obj_tag(v_x_174_))
{
case 0:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_198_ = lean_nat_dec_le(v___x_197_, v_prec_175_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_184_ = v___x_199_;
goto v___jp_183_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_184_ = v___x_200_;
goto v___jp_183_;
}
}
case 1:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(1024u);
v___x_202_ = lean_nat_dec_le(v___x_201_, v_prec_175_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_191_ = v___x_203_;
goto v___jp_190_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_191_ = v___x_204_;
goto v___jp_190_;
}
}
case 2:
{
lean_object* v_a_205_; lean_object* v___y_207_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_a_205_ = lean_ctor_get(v_x_174_, 0);
lean_inc_ref(v_a_205_);
lean_dec_ref(v_x_174_);
v___x_216_ = lean_unsigned_to_nat(1024u);
v___x_217_ = lean_nat_dec_le(v___x_216_, v_prec_175_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_207_ = v___x_218_;
goto v___jp_206_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_207_ = v___x_219_;
goto v___jp_206_;
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_208_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10));
v___x_209_ = lean_unsigned_to_nat(1024u);
v___x_210_ = l_Lean_instReprLiteral_repr(v_a_205_, v___x_209_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
lean_inc(v___y_207_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = l_Repr_addAppParen(v___x_214_, v_prec_175_);
return v___x_215_;
}
}
case 3:
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_246_; 
v_a_220_ = lean_ctor_get(v_x_174_, 0);
v_a_221_ = lean_ctor_get(v_x_174_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_246_ == 0)
{
v___x_223_ = v_x_174_;
v_isShared_224_ = v_isSharedCheck_246_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v_x_174_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_246_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___y_226_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1024u);
v___x_243_ = lean_nat_dec_le(v___x_242_, v_prec_175_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_226_ = v___x_244_;
goto v___jp_225_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_226_ = v___x_245_;
goto v___jp_225_;
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_227_ = lean_box(1);
v___x_228_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13));
v___x_229_ = lean_unsigned_to_nat(1024u);
v___x_230_ = l_Lean_Name_reprPrec(v_a_220_, v___x_229_);
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 5);
lean_ctor_set(v___x_223_, 1, v___x_230_);
lean_ctor_set(v___x_223_, 0, v___x_228_);
v___x_232_ = v___x_223_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_241_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_227_);
v___x_234_ = l_Nat_reprFast(v_a_221_);
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_233_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_inc(v___y_226_);
v___x_237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_237_, 0, v___y_226_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_238_);
v___x_240_ = l_Repr_addAppParen(v___x_239_, v_prec_175_);
return v___x_240_;
}
}
}
}
case 4:
{
lean_object* v_a_247_; lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_273_; 
v_a_247_ = lean_ctor_get(v_x_174_, 0);
v_a_248_ = lean_ctor_get(v_x_174_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_273_ == 0)
{
v___x_250_ = v_x_174_;
v_isShared_251_ = v_isSharedCheck_273_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_inc(v_a_247_);
lean_dec(v_x_174_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_273_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___y_253_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_175_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_253_ = v___x_271_;
goto v___jp_252_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_253_ = v___x_272_;
goto v___jp_252_;
}
v___jp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_254_ = lean_box(1);
v___x_255_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16));
v___x_256_ = lean_unsigned_to_nat(1024u);
v___x_257_ = l_Lean_Name_reprPrec(v_a_247_, v___x_256_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 5);
lean_ctor_set(v___x_250_, 1, v___x_257_);
lean_ctor_set(v___x_250_, 0, v___x_255_);
v___x_259_ = v___x_250_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_268_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_254_);
v___x_261_ = l_Nat_reprFast(v_a_248_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_inc(v___y_253_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_253_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_175_);
return v___x_267_;
}
}
}
}
case 5:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1024u);
v___x_275_ = lean_nat_dec_le(v___x_274_, v_prec_175_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_177_ = v___x_276_;
goto v___jp_176_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_177_ = v___x_277_;
goto v___jp_176_;
}
}
default: 
{
lean_object* v_a_278_; lean_object* v_a_279_; lean_object* v_a_280_; lean_object* v___y_282_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_a_278_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_a_278_);
v_a_279_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_a_279_);
v_a_280_ = lean_ctor_get(v_x_174_, 2);
lean_inc(v_a_280_);
lean_dec_ref(v_x_174_);
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_175_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6);
v___y_282_ = v___x_302_;
goto v___jp_281_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7, &l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once, _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7);
v___y_282_ = v___x_303_;
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_283_ = lean_box(1);
v___x_284_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19));
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = l_Lean_Name_reprPrec(v_a_278_, v___x_285_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_284_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_283_);
v___x_289_ = l_Nat_reprFast(v_a_279_);
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_283_);
v___x_293_ = l_Nat_reprFast(v_a_280_);
v___x_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_inc(v___y_282_);
v___x_296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_296_, 0, v___y_282_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = 0;
v___x_298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*1, v___x_297_);
v___x_299_ = l_Repr_addAppParen(v___x_298_, v_prec_175_);
return v___x_299_;
}
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_178_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1));
lean_inc(v___y_177_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___y_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = l_Repr_addAppParen(v___x_181_, v_prec_175_);
return v___x_182_;
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_185_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3));
lean_inc(v___y_184_);
v___x_186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = 0;
v___x_188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v_prec_175_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5));
lean_inc(v___y_191_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___y_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = 0;
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_194_);
v___x_196_ = l_Repr_addAppParen(v___x_195_, v_prec_175_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr___boxed(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_x_304_, v_prec_305_);
lean_dec(v_prec_305_);
return v_res_306_;
}
}
static uint64_t _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0(void){
_start:
{
lean_object* v___x_309_; uint64_t v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1723u);
v___x_310_ = lean_uint64_of_nat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object* v_x_311_){
_start:
{
switch(lean_obj_tag(v_x_311_))
{
case 0:
{
uint64_t v___x_312_; 
v___x_312_ = 7883ULL;
return v___x_312_;
}
case 1:
{
uint64_t v___x_313_; 
v___x_313_ = 2411ULL;
return v___x_313_;
}
case 2:
{
lean_object* v_a_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; 
v_a_314_ = lean_ctor_get(v_x_311_, 0);
v___x_315_ = 1879ULL;
v___x_316_ = l_Lean_Literal_hash(v_a_314_);
v___x_317_ = lean_uint64_mix_hash(v___x_315_, v___x_316_);
return v___x_317_;
}
case 3:
{
lean_object* v_a_318_; lean_object* v_a_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; 
v_a_318_ = lean_ctor_get(v_x_311_, 0);
v_a_319_ = lean_ctor_get(v_x_311_, 1);
v___x_320_ = 3541ULL;
v___x_321_ = l_Lean_instHashableFVarId_hash(v_a_318_);
v___x_322_ = lean_uint64_of_nat(v_a_319_);
v___x_323_ = lean_uint64_mix_hash(v___x_321_, v___x_322_);
v___x_324_ = lean_uint64_mix_hash(v___x_320_, v___x_323_);
return v___x_324_;
}
case 4:
{
lean_object* v_a_325_; lean_object* v_a_326_; uint64_t v___x_327_; uint64_t v___y_329_; 
v_a_325_ = lean_ctor_get(v_x_311_, 0);
v_a_326_ = lean_ctor_get(v_x_311_, 1);
v___x_327_ = 5237ULL;
if (lean_obj_tag(v_a_325_) == 0)
{
uint64_t v___x_333_; 
v___x_333_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_Key_hash___closed__0, &l_Lean_Meta_DiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0);
v___y_329_ = v___x_333_;
goto v___jp_328_;
}
else
{
uint64_t v_hash_334_; 
v_hash_334_ = lean_ctor_get_uint64(v_a_325_, sizeof(void*)*2);
v___y_329_ = v_hash_334_;
goto v___jp_328_;
}
v___jp_328_:
{
uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; 
v___x_330_ = lean_uint64_of_nat(v_a_326_);
v___x_331_ = lean_uint64_mix_hash(v___y_329_, v___x_330_);
v___x_332_ = lean_uint64_mix_hash(v___x_327_, v___x_331_);
return v___x_332_;
}
}
case 5:
{
uint64_t v___x_335_; 
v___x_335_ = 17ULL;
return v___x_335_;
}
default: 
{
lean_object* v_a_336_; lean_object* v_a_337_; lean_object* v_a_338_; uint64_t v___x_339_; uint64_t v___y_341_; 
v_a_336_ = lean_ctor_get(v_x_311_, 0);
v_a_337_ = lean_ctor_get(v_x_311_, 1);
v_a_338_ = lean_ctor_get(v_x_311_, 2);
v___x_339_ = lean_uint64_of_nat(v_a_338_);
if (lean_obj_tag(v_a_336_) == 0)
{
uint64_t v___x_345_; 
v___x_345_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_Key_hash___closed__0, &l_Lean_Meta_DiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0);
v___y_341_ = v___x_345_;
goto v___jp_340_;
}
else
{
uint64_t v_hash_346_; 
v_hash_346_ = lean_ctor_get_uint64(v_a_336_, sizeof(void*)*2);
v___y_341_ = v_hash_346_;
goto v___jp_340_;
}
v___jp_340_:
{
uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; 
v___x_342_ = lean_uint64_of_nat(v_a_337_);
v___x_343_ = lean_uint64_mix_hash(v___y_341_, v___x_342_);
v___x_344_ = lean_uint64_mix_hash(v___x_339_, v___x_343_);
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object* v_x_347_){
_start:
{
uint64_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_347_);
lean_dec(v_x_347_);
v_r_349_ = lean_box_uint64(v_res_348_);
return v_r_349_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
