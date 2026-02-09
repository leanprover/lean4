// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
// Imports: public import Init.Data.Hashable public import Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic public import Init.Data.RArray public import Init.Data.ToString.Macro import Init.Data.BitVec.Lemmas import Init.Omega
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
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_instReprBVBit_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value),((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6_value;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instReprBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instToStringBVBit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0;
static lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "||"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "^"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "/ᵤ"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "%ᵤ"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVBinOp_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVBinOp_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value;
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "~"};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rotL "};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rotR "};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ">>a "};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rev"};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVUnOp_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value;
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_reverse(lean_object*, lean_object*);
lean_object* l_BitVec_clz(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
uint64_t l_BitVec_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ++ "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "(replicate "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " << "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__6_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >> "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__7_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVExpr_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " >>a "};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_toString___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_toString___closed__8_value;
lean_object* l_BitVec_BitVec_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<u"};
static const lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVBinPred_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVBinPred_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVPred_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVPred_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVPred_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value;
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = 0;
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_of_nat(x_3);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_of_nat(x_4);
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_instHashableBVBit_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVBit(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_instReprBVBit_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5));
x_6 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6));
x_7 = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7;
x_8 = l_Nat_reprFast(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9));
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11));
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12;
x_22 = l_Nat_reprFast(x_3);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_11);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = l_Nat_reprFast(x_4);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_11);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17;
x_38 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18));
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19));
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_11);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_instReprBVBit_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0));
x_5 = l_Nat_reprFast(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_and_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_or_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_add_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
uint64_t x_4; 
x_4 = 2;
return x_4;
}
case 3:
{
uint64_t x_5; 
x_5 = 3;
return x_5;
}
case 4:
{
uint64_t x_6; 
x_6 = 4;
return x_6;
}
case 5:
{
uint64_t x_7; 
x_7 = 5;
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = 6;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(5u);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 6;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 5;
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_le(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 4;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 3;
return x_13;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_le(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_le(x_1, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 2;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(x_1);
x_4 = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_5; 
x_5 = lean_nat_land(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_nat_lor(x_3, x_4);
return x_6;
}
case 2:
{
lean_object* x_7; 
x_7 = lean_nat_lxor(x_3, x_4);
return x_7;
}
case 3:
{
lean_object* x_8; 
x_8 = l_BitVec_add(x_1, x_3, x_4);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = l_BitVec_mul(x_1, x_3, x_4);
return x_9;
}
case 5:
{
lean_object* x_10; 
x_10 = lean_nat_div(x_3, x_4);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = lean_nat_mod(x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 2;
x_9 = lean_uint64_of_nat(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = 3;
x_13 = lean_uint64_of_nat(x_11);
x_14 = lean_uint64_mix_hash(x_12, x_13);
return x_14;
}
case 4:
{
uint64_t x_15; 
x_15 = 4;
return x_15;
}
default: 
{
uint64_t x_16; 
x_16 = 5;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 4:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 5:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
case 1:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 0;
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_8;
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
return x_8;
}
else
{
return x_10;
}
}
case 4:
{
return x_8;
}
case 5:
{
return x_8;
}
default: 
{
return x_8;
}
}
}
case 2:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = 0;
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_12;
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_nat_dec_eq(x_11, x_13);
if (x_14 == 0)
{
return x_12;
}
else
{
return x_14;
}
}
case 4:
{
return x_12;
}
case 5:
{
return x_12;
}
default: 
{
return x_12;
}
}
}
case 3:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = 0;
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_16;
}
case 3:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_nat_dec_eq(x_15, x_17);
if (x_18 == 0)
{
return x_16;
}
else
{
return x_18;
}
}
case 4:
{
return x_16;
}
case 5:
{
return x_16;
}
default: 
{
return x_16;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
case 4:
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
case 5:
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
default: 
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
case 4:
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
case 5:
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
default: 
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
x_5 = l_Nat_reprFast(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
x_9 = l_Nat_reprFast(x_7);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
x_13 = l_Nat_reprFast(x_11);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
return x_14;
}
case 4:
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return x_15;
}
default: 
{
lean_object* x_16; 
x_16 = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; 
x_4 = l_BitVec_not(x_1, x_3);
lean_dec(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_BitVec_rotateLeft(x_1, x_3, x_5);
lean_dec(x_3);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_BitVec_rotateRight(x_1, x_3, x_7);
lean_dec(x_3);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_BitVec_sshiftRight(x_1, x_3, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; 
x_11 = l_BitVec_reverse(x_1, x_3);
lean_dec(x_3);
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = l_BitVec_clz(x_1, x_3);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_4(x_2, x_9, x_10, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_box(x_16);
x_19 = lean_apply_4(x_2, x_14, x_15, x_18, x_17);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_3(x_2, x_20, x_21, x_22);
return x_23;
}
case 5:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_apply_6(x_2, x_24, x_25, x_26, x_27, x_28, lean_box(0));
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_34 = lean_apply_5(x_2, x_30, x_31, x_32, x_33, lean_box(0));
return x_34;
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_38);
lean_dec_ref(x_1);
x_39 = lean_apply_4(x_2, x_35, x_36, x_37, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_var_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_const_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_extract_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bin_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_un_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_append_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_2(x_3, x_15, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_4(x_4, x_18, x_19, x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_26 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_box(x_25);
x_28 = lean_apply_4(x_5, x_23, x_24, x_27, x_26);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_1);
x_32 = lean_apply_3(x_6, x_29, x_30, x_31);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_apply_6(x_7, x_33, x_34, x_35, x_36, x_37, lean_box(0));
return x_38;
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_42);
lean_dec_ref(x_1);
x_43 = lean_apply_5(x_8, x_39, x_40, x_41, x_42, lean_box(0));
return x_43;
}
case 7:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_47);
lean_dec_ref(x_1);
x_48 = lean_apply_4(x_9, x_44, x_45, x_46, x_47);
return x_48;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_apply_4(x_10, x_49, x_50, x_51, x_52);
return x_53;
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_57);
lean_dec_ref(x_1);
x_58 = lean_apply_4(x_11, x_54, x_55, x_56, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = lean_apply_2(x_4, x_14, x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec_ref(x_3);
x_19 = lean_apply_2(x_5, x_17, x_18);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_23);
lean_dec_ref(x_3);
x_24 = lean_apply_4(x_6, x_20, x_21, x_22, x_23);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_28 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_3);
x_29 = lean_box(x_27);
x_30 = lean_apply_4(x_7, x_25, x_26, x_29, x_28);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_33);
lean_dec_ref(x_3);
x_34 = lean_apply_3(x_8, x_31, x_32, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_39);
lean_dec_ref(x_3);
x_40 = lean_apply_6(x_9, x_35, x_36, x_37, x_38, x_39, lean_box(0));
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_44);
lean_dec_ref(x_3);
x_45 = lean_apply_5(x_10, x_41, x_42, x_43, x_44, lean_box(0));
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_49);
lean_dec_ref(x_3);
x_50 = lean_apply_4(x_11, x_46, x_47, x_48, x_49);
return x_50;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_54);
lean_dec_ref(x_3);
x_55 = lean_apply_4(x_12, x_51, x_52, x_53, x_54);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_59);
lean_dec_ref(x_3);
x_60 = lean_apply_4(x_13, x_56, x_57, x_58, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; lean_object* x_8; 
x_3 = 5;
x_4 = lean_uint64_of_nat(x_1);
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_mix_hash(x_3, x_6);
x_8 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint64(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; lean_object* x_8; 
x_3 = 7;
x_4 = lean_uint64_of_nat(x_1);
x_5 = l_BitVec_hash(x_1, x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_mix_hash(x_3, x_6);
x_8 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint64(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_5 = 11;
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_14; 
x_14 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_14;
goto block_13;
}
case 1:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
goto block_13;
}
case 3:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_16;
goto block_13;
}
case 4:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_17;
goto block_13;
}
case 5:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_18;
goto block_13;
}
default: 
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_19;
goto block_13;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_16; 
x_5 = 13;
x_6 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_16 = x_25;
goto block_24;
}
case 1:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_16 = x_26;
goto block_24;
}
case 3:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_16 = x_27;
goto block_24;
}
case 4:
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_16 = x_28;
goto block_24;
}
case 5:
{
uint64_t x_29; 
x_29 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
x_16 = x_29;
goto block_24;
}
default: 
{
uint64_t x_30; 
x_30 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
x_16 = x_30;
goto block_24;
}
}
block_15:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_uint64_mix_hash(x_5, x_12);
x_14 = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint64(x_14, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 8, x_3);
return x_14;
}
block_24:
{
uint64_t x_17; 
x_17 = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_16;
x_8 = x_17;
x_9 = x_18;
goto block_15;
}
case 1:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_16;
x_8 = x_17;
x_9 = x_19;
goto block_15;
}
case 3:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_16;
x_8 = x_17;
x_9 = x_20;
goto block_15;
}
case 4:
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_16;
x_8 = x_17;
x_9 = x_21;
goto block_15;
}
case 5:
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_7 = x_16;
x_8 = x_17;
x_9 = x_22;
goto block_15;
}
default: 
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_7 = x_16;
x_8 = x_17;
x_9 = x_23;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bin___override(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; 
x_4 = 17;
x_5 = lean_uint64_of_nat(x_1);
x_6 = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_13; 
x_13 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_7 = x_13;
goto block_12;
}
case 1:
{
uint64_t x_14; 
x_14 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_7 = x_14;
goto block_12;
}
case 3:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_7 = x_15;
goto block_12;
}
case 4:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_7 = x_16;
goto block_12;
}
case 5:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_7 = x_17;
goto block_12;
}
default: 
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_7 = x_18;
goto block_12;
}
}
block_12:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; 
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_mix_hash(x_5, x_8);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_15; 
x_6 = 19;
x_7 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_15 = x_23;
goto block_22;
}
case 1:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_15 = x_24;
goto block_22;
}
case 3:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_15 = x_25;
goto block_22;
}
case 4:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_15 = x_26;
goto block_22;
}
case 5:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_15 = x_27;
goto block_22;
}
default: 
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_15 = x_28;
goto block_22;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set_uint64(x_13, sizeof(void*)*5, x_12);
return x_13;
}
block_22:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_16;
goto block_14;
}
case 1:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_17;
goto block_14;
}
case 3:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_18;
goto block_14;
}
case 4:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_19;
goto block_14;
}
case 5:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_5, sizeof(void*)*5);
x_8 = x_15;
x_9 = x_20;
goto block_14;
}
default: 
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
x_8 = x_15;
x_9 = x_21;
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_5 = 23;
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_14; 
x_14 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_14;
goto block_13;
}
case 1:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
goto block_13;
}
case 3:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_16;
goto block_13;
}
case 4:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_17;
goto block_13;
}
case 5:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_18;
goto block_13;
}
default: 
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_19;
goto block_13;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_14; 
x_5 = 29;
x_6 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_22;
goto block_21;
}
case 1:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_23;
goto block_21;
}
case 3:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_24;
goto block_21;
}
case 4:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_25;
goto block_21;
}
case 5:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_14 = x_26;
goto block_21;
}
default: 
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_14 = x_27;
goto block_21;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
return x_12;
}
block_21:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_15;
goto block_13;
}
case 1:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_16;
goto block_13;
}
case 3:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_17;
goto block_13;
}
case 4:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_18;
goto block_13;
}
case 5:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_7 = x_14;
x_8 = x_19;
goto block_13;
}
default: 
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_7 = x_14;
x_8 = x_20;
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_14; 
x_5 = 31;
x_6 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_22;
goto block_21;
}
case 1:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_23;
goto block_21;
}
case 3:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_24;
goto block_21;
}
case 4:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_25;
goto block_21;
}
case 5:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_14 = x_26;
goto block_21;
}
default: 
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_14 = x_27;
goto block_21;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
return x_12;
}
block_21:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_15;
goto block_13;
}
case 1:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_16;
goto block_13;
}
case 3:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_17;
goto block_13;
}
case 4:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_18;
goto block_13;
}
case 5:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_7 = x_14;
x_8 = x_19;
goto block_13;
}
default: 
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_7 = x_14;
x_8 = x_20;
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_14; 
x_5 = 37;
x_6 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_22;
goto block_21;
}
case 1:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_14 = x_23;
goto block_21;
}
case 3:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_24;
goto block_21;
}
case 4:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_14 = x_25;
goto block_21;
}
case 5:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_14 = x_26;
goto block_21;
}
default: 
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_14 = x_27;
goto block_21;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
return x_12;
}
block_21:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_15;
goto block_13;
}
case 1:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_7 = x_14;
x_8 = x_16;
goto block_13;
}
case 3:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_17;
goto block_13;
}
case 4:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = x_14;
x_8 = x_18;
goto block_13;
}
case 5:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_7 = x_14;
x_8 = x_19;
goto block_13;
}
default: 
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_7 = x_14;
x_8 = x_20;
goto block_13;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 3:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_4;
}
case 4:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_5;
}
case 5:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
return x_6;
}
default: 
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
return x_3;
}
case 1:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
return x_4;
}
case 3:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
return x_5;
}
case 4:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
return x_6;
}
case 5:
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 3:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_4;
}
case 4:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_5;
}
case 5:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
return x_6;
}
default: 
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_instHashable(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_88; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_96; 
x_96 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_88 = x_96;
goto block_95;
}
case 1:
{
uint64_t x_97; 
x_97 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_88 = x_97;
goto block_95;
}
case 3:
{
uint64_t x_98; 
x_98 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_88 = x_98;
goto block_95;
}
case 4:
{
uint64_t x_99; 
x_99 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_88 = x_99;
goto block_95;
}
case 5:
{
uint64_t x_100; 
x_100 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
x_88 = x_100;
goto block_95;
}
default: 
{
uint64_t x_101; 
x_101 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_88 = x_101;
goto block_95;
}
}
}
else
{
return x_5;
}
block_87:
{
uint8_t x_8; 
x_8 = lean_uint64_dec_eq(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_nat_dec_eq(x_9, x_10);
return x_11;
}
else
{
return x_5;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_nat_dec_eq(x_12, x_13);
return x_14;
}
else
{
return x_5;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_nat_dec_eq(x_15, x_18);
if (x_21 == 0)
{
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_16, x_19);
if (x_22 == 0)
{
return x_22;
}
else
{
x_1 = x_17;
x_2 = x_20;
goto _start;
}
}
}
else
{
return x_5;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_29 = lean_ctor_get(x_2, 2);
x_30 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_25, x_28);
if (x_30 == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_24, x_27);
if (x_31 == 0)
{
return x_31;
}
else
{
x_1 = x_26;
x_2 = x_29;
goto _start;
}
}
}
else
{
return x_5;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(x_33, x_35);
if (x_37 == 0)
{
return x_37;
}
else
{
x_1 = x_34;
x_2 = x_36;
goto _start;
}
}
else
{
return x_5;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 3);
x_42 = lean_ctor_get(x_1, 4);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 3);
x_46 = lean_ctor_get(x_2, 4);
x_47 = lean_nat_dec_eq(x_39, x_43);
if (x_47 == 0)
{
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_eq(x_40, x_44);
if (x_48 == 0)
{
return x_48;
}
else
{
uint8_t x_49; 
x_49 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_41, x_45);
if (x_49 == 0)
{
return x_49;
}
else
{
x_1 = x_42;
x_2 = x_46;
goto _start;
}
}
}
}
else
{
return x_5;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_nat_dec_eq(x_52, x_55);
if (x_57 == 0)
{
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_eq(x_51, x_54);
if (x_58 == 0)
{
return x_58;
}
else
{
x_1 = x_53;
x_2 = x_56;
goto _start;
}
}
}
else
{
return x_5;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_ctor_get(x_1, 3);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
x_66 = lean_nat_dec_eq(x_60, x_63);
if (x_66 == 0)
{
return x_66;
}
else
{
uint8_t x_67; 
x_67 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_61, x_64);
if (x_67 == 0)
{
return x_67;
}
else
{
x_1 = x_62;
x_2 = x_65;
goto _start;
}
}
}
else
{
return x_5;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_1, 1);
x_70 = lean_ctor_get(x_1, 2);
x_71 = lean_ctor_get(x_1, 3);
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_ctor_get(x_2, 2);
x_74 = lean_ctor_get(x_2, 3);
x_75 = lean_nat_dec_eq(x_69, x_72);
if (x_75 == 0)
{
return x_75;
}
else
{
uint8_t x_76; 
x_76 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_70, x_73);
if (x_76 == 0)
{
return x_76;
}
else
{
x_1 = x_71;
x_2 = x_74;
goto _start;
}
}
}
else
{
return x_5;
}
}
default: 
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_1, 1);
x_79 = lean_ctor_get(x_1, 2);
x_80 = lean_ctor_get(x_1, 3);
x_81 = lean_ctor_get(x_2, 1);
x_82 = lean_ctor_get(x_2, 2);
x_83 = lean_ctor_get(x_2, 3);
x_84 = lean_nat_dec_eq(x_78, x_81);
if (x_84 == 0)
{
return x_84;
}
else
{
uint8_t x_85; 
x_85 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_79, x_82);
if (x_85 == 0)
{
return x_85;
}
else
{
x_1 = x_80;
x_2 = x_83;
goto _start;
}
}
}
else
{
return x_5;
}
}
}
}
else
{
return x_5;
}
}
}
block_95:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_89; 
x_89 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = x_88;
x_7 = x_89;
goto block_87;
}
case 1:
{
uint64_t x_90; 
x_90 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = x_88;
x_7 = x_90;
goto block_87;
}
case 3:
{
uint64_t x_91; 
x_91 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_6 = x_88;
x_7 = x_91;
goto block_87;
}
case 4:
{
uint64_t x_92; 
x_92 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_6 = x_88;
x_7 = x_92;
goto block_87;
}
case 5:
{
uint64_t x_93; 
x_93 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
x_6 = x_88;
x_7 = x_93;
goto block_87;
}
default: 
{
uint64_t x_94; 
x_94 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
x_6 = x_88;
x_7 = x_94;
goto block_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_decEq(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
x_5 = l_Nat_reprFast(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_BitVec_BitVec_repr(x_1, x_7);
x_9 = l_Std_Format_defWidth;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Std_Format_pretty(x_8, x_9, x_10, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = l_Std_Tactic_BVDecide_BVExpr_toString(x_12, x_14);
x_16 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_reprFast(x_13);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Nat_reprFast(x_1);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
x_25 = lean_string_append(x_23, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_28 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_29 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(x_1);
x_30 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_26);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_27);
x_35 = lean_string_append(x_33, x_34);
lean_dec_ref(x_34);
x_36 = lean_string_append(x_35, x_32);
x_37 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_28);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_40 = lean_string_append(x_38, x_39);
return x_40;
}
case 4:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_42);
lean_dec_ref(x_2);
x_43 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
x_44 = l_Std_Tactic_BVDecide_BVUnOp_toString(x_41);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_42);
x_49 = lean_string_append(x_47, x_48);
lean_dec_ref(x_48);
x_50 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_51 = lean_string_append(x_49, x_50);
return x_51;
}
case 5:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_55);
lean_dec_ref(x_2);
x_56 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
x_57 = l_Std_Tactic_BVDecide_BVExpr_toString(x_52, x_54);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
x_59 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
x_60 = lean_string_append(x_58, x_59);
x_61 = l_Std_Tactic_BVDecide_BVExpr_toString(x_53, x_55);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_64 = lean_string_append(x_62, x_63);
return x_64;
}
case 6:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_67);
lean_dec_ref(x_2);
x_68 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
x_69 = l_Nat_reprFast(x_66);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Std_Tactic_BVDecide_BVExpr_toString(x_65, x_67);
x_74 = lean_string_append(x_72, x_73);
lean_dec_ref(x_73);
x_75 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_76 = lean_string_append(x_74, x_75);
return x_76;
}
case 7:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_79);
lean_dec_ref(x_2);
x_80 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
x_81 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_78);
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
x_84 = lean_string_append(x_82, x_83);
x_85 = l_Std_Tactic_BVDecide_BVExpr_toString(x_77, x_79);
x_86 = lean_string_append(x_84, x_85);
lean_dec_ref(x_85);
x_87 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_88 = lean_string_append(x_86, x_87);
return x_88;
}
case 8:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_91);
lean_dec_ref(x_2);
x_92 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
x_93 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_90);
x_94 = lean_string_append(x_92, x_93);
lean_dec_ref(x_93);
x_95 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Std_Tactic_BVDecide_BVExpr_toString(x_89, x_91);
x_98 = lean_string_append(x_96, x_97);
lean_dec_ref(x_97);
x_99 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_100 = lean_string_append(x_98, x_99);
return x_100;
}
default: 
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_103);
lean_dec_ref(x_2);
x_104 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
x_105 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_102);
x_106 = lean_string_append(x_104, x_105);
lean_dec_ref(x_105);
x_107 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
x_108 = lean_string_append(x_106, x_107);
x_109 = l_Std_Tactic_BVDecide_BVExpr_toString(x_101, x_103);
x_110 = lean_string_append(x_108, x_109);
lean_dec_ref(x_109);
x_111 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_112 = lean_string_append(x_110, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Lean_RArray_getImpl___redArg(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_6, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_BitVec_setWidth(x_6, x_1, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_dec(x_6);
return x_7;
}
}
case 1:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 3);
x_14 = l_Std_Tactic_BVDecide_BVExpr_eval(x_11, x_2, x_13);
x_15 = l_BitVec_extractLsb_x27___redArg(x_12, x_1, x_14);
lean_dec(x_14);
return x_15;
}
case 3:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_18 = lean_ctor_get(x_3, 2);
x_19 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_16);
x_20 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_18);
x_21 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_17, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_23);
x_25 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_22, x_24);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_3, 4);
x_30 = l_Std_Tactic_BVDecide_BVExpr_eval(x_26, x_2, x_28);
x_31 = l_Std_Tactic_BVDecide_BVExpr_eval(x_27, x_2, x_29);
x_32 = l_BitVec_append___redArg(x_27, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
return x_32;
}
case 6:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get(x_3, 3);
x_36 = l_Std_Tactic_BVDecide_BVExpr_eval(x_33, x_2, x_35);
x_37 = l_BitVec_replicate(x_33, x_34, x_36);
lean_dec(x_36);
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get(x_3, 3);
x_41 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_39);
x_42 = l_Std_Tactic_BVDecide_BVExpr_eval(x_38, x_2, x_40);
x_43 = l_BitVec_shiftLeft(x_1, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
return x_43;
}
case 8:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 3);
x_47 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_45);
x_48 = l_Std_Tactic_BVDecide_BVExpr_eval(x_44, x_2, x_46);
x_49 = lean_nat_shiftr(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
return x_49;
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_3, 1);
x_51 = lean_ctor_get(x_3, 2);
x_52 = lean_ctor_get(x_3, 3);
x_53 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_51);
x_54 = l_Std_Tactic_BVDecide_BVExpr_eval(x_50, x_2, x_52);
x_55 = l_BitVec_sshiftRight(x_1, x_53, x_54);
lean_dec(x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_2(x_3, x_1, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_2(x_4, x_1, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_20 = lean_apply_4(x_5, x_1, x_17, x_18, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_23 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_2);
x_24 = lean_box(x_22);
x_25 = lean_apply_4(x_6, x_1, x_21, x_24, x_23);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_2);
x_28 = lean_apply_3(x_7, x_1, x_26, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_33 = lean_apply_6(x_8, x_1, x_29, x_30, x_31, x_32, lean_box(0));
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_36);
lean_dec_ref(x_2);
x_37 = lean_apply_5(x_9, x_1, x_34, x_35, x_36, lean_box(0));
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_40);
lean_dec_ref(x_2);
x_41 = lean_apply_4(x_10, x_1, x_38, x_39, x_40);
return x_41;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_44);
lean_dec_ref(x_2);
x_45 = lean_apply_4(x_11, x_1, x_42, x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_48);
lean_dec_ref(x_2);
x_49 = lean_apply_4(x_12, x_1, x_46, x_47, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_2, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinPred_eval(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVPred_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(x_5);
x_8 = lean_apply_4(x_2, x_3, x_4, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_3(x_2, x_9, x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVPred_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(x_2);
x_7 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_4);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_12, x_9);
x_14 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_toString(x_18, x_19);
x_22 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_20);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_4);
x_8 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_6);
x_9 = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(x_5, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = l_Std_Tactic_BVDecide_BVExpr_eval(x_10, x_1, x_11);
x_14 = l_Nat_testBit(x_13, x_12);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVPred_eval(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_eval(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7 = _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7);
l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12 = _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12);
l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16 = _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16);
l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17 = _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17);
l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0 = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0);
l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1 = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1);
l_Std_Tactic_BVDecide_instInhabitedBVBit = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
