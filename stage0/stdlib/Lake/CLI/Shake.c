// Lean compiler output
// Module: Lake.CLI.Shake
// Imports: public import Lean.Util.Path import Lean.ExtraModUses import Lean.Parser.Module import Init.Data.Range.Polymorphic.Iterators meta import Lean.Parser.Module
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__2_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__4 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__3_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__6_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8_value;
lean_object* lean_string_length(lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___closed__0_value;
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInterBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInterBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInterBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInterBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInterBitset___closed__0_value;
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instUnionBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instUnionBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instUnionBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instUnionBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instUnionBitset___closed__0_value;
lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instXorOpBitset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instXorOpBitset___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instXorOpBitset___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instXorOpBitset = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instXorOpBitset___closed__0_value;
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_has(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_has___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isExported"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__2_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__3_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9;
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind___closed__0_value;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_priv = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport___boxed(lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pub"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__2_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__3_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "priv"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "metaPub"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metaPriv"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_empty = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___closed__0_value;
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_unsafe_rec"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__1_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isStr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_simp_"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0_value;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqModuleIdx;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3;
lean_object* l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_indirect"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 226, 26, 178, 217, 221, 126, 236)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3;
extern lean_object* l_Lean_indirectModUseExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0;
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parse errors in file"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1_value;
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "error: failed to find source file for "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1_value;
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.CLI.Shake"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "_private.Lake.CLI.Shake.0.Lake.Shake.decodeHeader"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unexpected header syntax "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__8_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__10 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__10_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11_value;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(lean_object*);
extern lean_object* l_Lean_instInhabitedImport_default;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "_private.Lake.CLI.Shake.0.Lake.Shake.decodeImport"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unexpected syntax "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__4 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__4_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__6_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_0),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_1),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value_aux_2),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__8_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9_value;
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "all "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "public "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "shake: keep-downstream"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__0_value;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__2;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5;
static const lean_ctor_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6_value;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr();
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is implied by other imports"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` is now unused"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` is already covered by `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqImport_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "` is preserved as folder-nested import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` because of `--keep-prefix`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "* upgrading to `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` because of `--add-public`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` is needed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (calculated)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "shake: keep"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0_value;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` as additional dependency"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Adding `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = ": warning: unused import (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` required"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "    because `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` refers to `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "    because of additional compile-time dependencies"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "  note: `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "` from imports to be added because it is now implied"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Removing `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "shake: keep-all"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0_value;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "  add "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ":1: warning: add "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " instead"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "  remove "};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__4 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Preserving `"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` because of recorded extra rev use"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__6_value;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_isExtraRevModUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___lam__0(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__0_value;
lean_object* l_instOrdBool___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdBool___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__1 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__1_value;
lean_object* l_String_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__2 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__2_value;
lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableImport_hash(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Shake_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "No edits required."};
static const lean_object* l_Lake_Shake_run___lam__0___closed__0 = (const lean_object*)&l_Lake_Shake_run___lam__0___closed__0_value;
static const lean_string_object l_Lake_Shake_run___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Successfully applied "};
static const lean_object* l_Lake_Shake_run___lam__0___closed__1 = (const lean_object*)&l_Lake_Shake_run___lam__0___closed__1_value;
static const lean_string_object l_Lake_Shake_run___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " suggestions."};
static const lean_object* l_Lake_Shake_run___lam__0___closed__2 = (const lean_object*)&l_Lake_Shake_run___lam__0___closed__2_value;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Shake_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint32_t, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Shake_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0;
extern lean_object* l_Lean_instInhabitedFileMap_default;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2_value;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3;
extern lean_object* l_System_instInhabitedFilePath_default;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5;
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Shake_run___closed__0;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
static lean_object* l_Lake_Shake_run___closed__1;
static const lean_string_object l_Lake_Shake_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "The following changes will be made automatically:"};
static const lean_object* l_Lake_Shake_run___closed__2 = (const lean_object*)&l_Lake_Shake_run___closed__2_value;
static const lean_string_object l_Lake_Shake_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`lake shake` only works with `module`s currently"};
static const lean_object* l_Lake_Shake_run___closed__3 = (const lean_object*)&l_Lake_Shake_run___closed__3_value;
static const lean_ctor_object l_Lake_Shake_run___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lake_Shake_run___closed__3_value)}};
static const lean_object* l_Lake_Shake_run___closed__4 = (const lean_object*)&l_Lake_Shake_run___closed__4_value;
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_ImportState_markAllExported(lean_object*);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Shake_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Shake_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset_decEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instDecidableEqBitset(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__6));
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10;
x_11 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11));
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12));
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_3, x_1);
x_5 = lean_nat_lor(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instInsertNatBitset___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_3, x_1);
x_5 = lean_nat_lor(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instSingletonNatBitset___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_has(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_testBit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_has___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_has(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get_uint8(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, 1);
x_5 = lean_ctor_get_uint8(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, 1);
if (x_3 == 0)
{
if (x_5 == 0)
{
uint8_t x_9; 
x_9 = 1;
x_7 = x_9;
goto block_8;
}
else
{
return x_3;
}
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
x_7 = x_5;
goto block_8;
}
}
block_8:
{
if (x_4 == 0)
{
if (x_6 == 0)
{
return x_7;
}
else
{
return x_4;
}
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_ctor_get_uint8(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, 1);
x_4 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5));
x_5 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__3));
x_6 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4;
x_7 = l_Bool_repr___redArg(x_2);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = 0;
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6));
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8));
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9;
x_20 = l_Bool_repr___redArg(x_3);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_9);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10;
x_25 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11));
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12));
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_9);
return x_30;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get_uint8(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, 1);
x_4 = 0;
if (x_2 == 0)
{
uint64_t x_12; 
x_12 = 13;
x_5 = x_12;
goto block_11;
}
else
{
uint64_t x_13; 
x_13 = 11;
x_5 = x_13;
goto block_11;
}
block_11:
{
uint64_t x_6; 
x_6 = lean_uint64_mix_hash(x_4, x_5);
if (x_3 == 0)
{
uint64_t x_7; uint64_t x_8; 
x_7 = 13;
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
else
{
uint64_t x_9; uint64_t x_10; 
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_6, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_5, 0, x_2);
lean_ctor_set_uint8(x_5, 1, x_3);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_7, 0, x_2);
lean_ctor_set_uint8(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, 1, x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__5));
x_7 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__3));
x_8 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4;
x_9 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(x_2);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6));
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6));
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_21 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7;
x_22 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_11);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
x_28 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9));
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
x_31 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10;
x_32 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(x_4);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_11);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_14);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12));
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
x_41 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13;
x_42 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(x_5);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_11);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10;
x_47 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__11));
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__12));
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_11);
return x_52;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, 0);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, 1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, 1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_1, x_2);
x_5 = l_Nat_testBit(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, 1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
lean_ctor_set(x_1, 3, x_3);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_3);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_2, 1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 2);
lean_dec(x_26);
lean_ctor_set(x_1, 2, x_3);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_1, x_2);
x_5 = lean_apply_1(x_3, x_4);
x_6 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_set(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lor(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_land(x_2, x_1);
x_4 = lean_nat_lxor(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_modify(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_nat_lor(x_4, x_8);
lean_dec(x_8);
x_13 = lean_nat_lor(x_5, x_9);
lean_dec(x_9);
x_14 = lean_nat_lor(x_6, x_10);
lean_dec(x_10);
x_15 = lean_nat_lor(x_7, x_11);
lean_dec(x_11);
lean_ctor_set(x_2, 3, x_15);
lean_ctor_set(x_2, 2, x_14);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = lean_nat_lor(x_16, x_20);
lean_dec(x_20);
x_25 = lean_nat_lor(x_17, x_21);
lean_dec(x_21);
x_26 = lean_nat_lor(x_18, x_22);
lean_dec(x_22);
x_27 = lean_nat_lor(x_19, x_23);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_instUnionNeeds___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Environment_header(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_38; lean_object* x_53; 
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
if (x_21 == 0)
{
x_53 = x_1;
goto block_67;
}
else
{
if (x_22 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_68, 0, x_21);
lean_ctor_set_uint8(x_68, 1, x_22);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_shiftl(x_70, x_3);
x_72 = lean_nat_lor(x_69, x_71);
lean_dec(x_71);
x_73 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_1, x_68, x_72);
x_74 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_68);
x_75 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_73, x_68, x_74);
lean_dec_ref(x_68);
x_53 = x_75;
goto block_67;
}
else
{
x_53 = x_1;
goto block_67;
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_9, 0, x_6);
lean_ctor_set_uint8(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_10, 0, x_5);
lean_ctor_set_uint8(x_10, 1, x_5);
x_11 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_10);
lean_dec_ref(x_10);
x_12 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_8, x_9, x_11);
lean_dec_ref(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_13, 0, x_7);
lean_ctor_set_uint8(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_14, 0, x_6);
lean_ctor_set_uint8(x_14, 1, x_6);
x_15 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_13);
x_17 = lean_nat_lor(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_8, x_13, x_17);
lean_dec_ref(x_13);
return x_18;
}
}
block_37:
{
if (x_21 == 0)
{
uint8_t x_24; 
x_24 = 1;
if (x_22 == 0)
{
x_5 = x_24;
x_6 = x_20;
x_7 = x_21;
x_8 = x_23;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_25, 0, x_21);
lean_ctor_set_uint8(x_25, 1, x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_shiftl(x_27, x_3);
x_29 = lean_nat_lor(x_26, x_28);
lean_dec(x_28);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_23, x_25, x_29);
x_31 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_31, 0, x_22);
lean_ctor_set_uint8(x_31, 1, x_21);
x_32 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_31);
lean_dec_ref(x_31);
x_33 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_33, 0, x_22);
lean_ctor_set_uint8(x_33, 1, x_22);
x_34 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_33);
lean_dec_ref(x_33);
x_35 = lean_nat_lor(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
x_36 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_30, x_25, x_35);
lean_dec_ref(x_25);
x_5 = x_24;
x_6 = x_20;
x_7 = x_21;
x_8 = x_36;
goto block_19;
}
}
else
{
return x_23;
}
}
block_52:
{
if (x_21 == 0)
{
x_23 = x_38;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_39, 0, x_21);
lean_ctor_set_uint8(x_39, 1, x_21);
x_40 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_39);
lean_inc(x_40);
x_41 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_38, x_39, x_40);
if (x_22 == 0)
{
lean_dec(x_40);
lean_dec_ref(x_39);
x_23 = x_41;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_shiftl(x_43, x_3);
x_45 = lean_nat_lor(x_42, x_44);
lean_dec(x_44);
x_46 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_41, x_39, x_45);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_48, 0, x_22);
lean_ctor_set_uint8(x_48, 1, x_47);
x_49 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_48);
lean_dec_ref(x_48);
x_50 = lean_nat_lor(x_49, x_40);
lean_dec(x_40);
lean_dec(x_49);
x_51 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_46, x_39, x_50);
lean_dec_ref(x_39);
x_23 = x_51;
goto block_37;
}
}
}
block_67:
{
if (x_21 == 0)
{
if (x_22 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = 1;
x_55 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_55, 0, x_22);
lean_ctor_set_uint8(x_55, 1, x_22);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_shiftl(x_57, x_3);
x_59 = lean_nat_lor(x_56, x_58);
lean_dec(x_58);
x_60 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_53, x_55, x_59);
x_61 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_61, 0, x_54);
lean_ctor_set_uint8(x_61, 1, x_22);
x_62 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_61);
lean_dec_ref(x_61);
lean_inc(x_62);
x_63 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_60, x_55, x_62);
if (x_20 == 0)
{
lean_dec(x_62);
lean_dec_ref(x_55);
x_38 = x_63;
goto block_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_4, x_55);
x_65 = lean_nat_lor(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
x_66 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_63, x_55, x_65);
lean_dec_ref(x_55);
x_38 = x_66;
goto block_52;
}
}
else
{
x_38 = x_53;
goto block_52;
}
}
else
{
x_38 = x_53;
goto block_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__1));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; uint8_t x_8; uint8_t x_16; 
x_16 = l_Lean_Name_isStr(x_2);
if (x_16 == 0)
{
x_8 = x_16;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_Name_getString_x21(x_2);
x_18 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__1));
x_19 = lean_string_utf8_byte_size(x_17);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2;
x_21 = lean_nat_dec_le(x_20, x_19);
if (x_21 == 0)
{
lean_dec_ref(x_17);
goto block_15;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_string_memcmp(x_17, x_18, x_22, x_22, x_20);
lean_dec_ref(x_17);
if (x_23 == 0)
{
goto block_15;
}
else
{
x_8 = x_23;
goto block_11;
}
}
}
block_7:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = l_Lean_isMarkedMeta(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_isDeclMeta(x_1, x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_3;
}
}
block_11:
{
uint8_t x_9; 
x_9 = 1;
if (x_8 == 0)
{
x_3 = x_9;
x_4 = x_2;
goto block_7;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_3 = x_9;
x_4 = x_10;
goto block_7;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Name_getString_x21(x_2);
x_13 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__0));
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec_ref(x_12);
x_8 = x_14;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 5);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Name_isStr(x_2);
if (x_10 == 0)
{
x_3 = x_10;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Name_getString_x21(x_2);
x_12 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0));
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1;
x_15 = lean_nat_dec_le(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_string_memcmp(x_11, x_12, x_17, x_17, x_14);
lean_dec_ref(x_11);
x_3 = x_18;
goto block_7;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
block_7:
{
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_array_uget(x_4, x_6);
x_16 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_17 = lean_array_get_borrowed(x_16, x_14, x_2);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_17, x_3, x_15);
if (x_18 == 0)
{
lean_dec(x_15);
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_shiftl(x_20, x_15);
lean_dec(x_15);
x_22 = lean_nat_lor(x_19, x_21);
lean_dec(x_21);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_7, x_3, x_22);
x_8 = x_23;
goto block_12;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; 
x_15 = l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f(x_1, x_6);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_3, 0);
x_20 = lean_ctor_get_uint8(x_3, 1);
if (lean_is_exclusive(x_3)) {
 x_21 = x_3;
} else {
 lean_dec_ref(x_3);
 x_21 = lean_box(0);
}
if (x_20 == 0)
{
lean_dec_ref(x_2);
x_22 = x_20;
goto block_35;
}
else
{
uint8_t x_36; 
lean_inc(x_16);
x_36 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_2, x_16);
if (x_36 == 0)
{
x_22 = x_20;
goto block_35;
}
else
{
uint8_t x_37; 
x_37 = 0;
x_22 = x_37;
goto block_35;
}
}
block_35:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_instBEqModuleIdx;
lean_inc(x_4);
lean_inc(x_18);
x_24 = lean_apply_2(x_23, x_18, x_4);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 0, 2);
} else {
 x_26 = x_21;
}
lean_ctor_set_uint8(x_26, 0, x_19);
lean_ctor_set_uint8(x_26, 1, x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_shiftl(x_28, x_18);
lean_dec(x_18);
x_30 = lean_nat_lor(x_27, x_29);
lean_dec(x_29);
x_31 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_7, x_26, x_30);
x_32 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_5, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0;
x_8 = x_31;
x_9 = x_26;
x_10 = x_33;
goto block_14;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_8 = x_31;
x_9 = x_26;
x_10 = x_34;
goto block_14;
}
}
else
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
return x_7;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
else
{
lean_dec(x_15);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
block_14:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__0(x_1, x_4, x_9, x_10, x_11, x_12, x_8);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrSet___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2;
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___boxed), 7, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_7);
x_9 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3;
x_10 = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_box(0), x_8, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__1));
x_5 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; 
x_7 = lean_array_uget(x_2, x_4);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_24 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_23);
x_8 = x_24;
goto block_20;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_8 = x_25;
goto block_20;
}
block_20:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_shiftl(x_13, x_8);
lean_dec(x_8);
x_15 = lean_nat_lor(x_12, x_14);
lean_dec(x_14);
x_16 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_5, x_11, x_15);
lean_dec_ref(x_11);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_40; uint8_t x_45; 
x_24 = lean_array_uget(x_4, x_6);
x_25 = l_Lean_ConstantInfo_name(x_24);
x_45 = l_Lean_isPrivateName(x_25);
if (x_45 == 0)
{
if (x_23 == 0)
{
goto block_44;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Environment_setExporting(x_1, x_23);
lean_inc(x_25);
x_47 = l_Lean_Environment_find_x3f(x_46, x_25, x_45);
if (lean_obj_tag(x_47) == 0)
{
x_40 = x_47;
goto block_42;
}
else
{
x_26 = x_47;
x_27 = x_23;
goto block_39;
}
}
}
else
{
goto block_44;
}
block_39:
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_1);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_1, x_25);
x_29 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, 1, x_28);
x_30 = l_Lean_ConstantInfo_type(x_24);
lean_inc_ref(x_29);
lean_inc(x_3);
lean_inc_ref(x_2);
x_31 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr(x_2, x_3, x_29, x_30, x_7);
x_32 = l_Lean_ConstantInfo_value_x3f(x_24, x_23);
if (lean_obj_tag(x_32) == 1)
{
if (x_28 == 0)
{
lean_dec_ref(x_29);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_33;
x_20 = x_28;
goto block_22;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec_ref(x_26);
x_36 = l_Lean_ConstantInfo_hasValue(x_35, x_23);
lean_dec(x_35);
if (x_36 == 0)
{
x_18 = x_31;
x_19 = x_34;
x_20 = x_36;
goto block_22;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, 1, x_28);
x_13 = x_31;
x_14 = x_34;
x_15 = x_37;
goto block_17;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_26);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec_ref(x_32);
x_13 = x_31;
x_14 = x_38;
x_15 = x_29;
goto block_17;
}
}
else
{
lean_dec(x_32);
lean_dec_ref(x_29);
lean_dec(x_26);
x_8 = x_31;
goto block_12;
}
}
block_42:
{
uint8_t x_41; 
x_41 = 0;
x_26 = x_40;
x_27 = x_41;
goto block_39;
}
block_44:
{
lean_object* x_43; 
x_43 = lean_box(0);
x_40 = x_43;
goto block_42;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
block_17:
{
lean_object* x_16; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr(x_2, x_3, x_15, x_14, x_13);
x_8 = x_16;
goto block_12;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_21, 0, x_20);
lean_ctor_set_uint8(x_21, 1, x_20);
x_13 = x_18;
x_14 = x_19;
x_15 = x_21;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = l_Lean_Environment_header(x_3);
x_5 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_instInhabitedModuleData_default;
x_7 = lean_array_get(x_6, x_5, x_2);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_10 = lean_array_size(x_8);
x_11 = 0;
lean_inc(x_2);
lean_inc_ref(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__1(x_3, x_1, x_2, x_8, x_10, x_11, x_9);
lean_dec_ref(x_8);
x_13 = l_Lean_getExtraModUses(x_3, x_2);
lean_dec(x_2);
x_14 = lean_array_size(x_13);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2(x_3, x_13, x_14, x_11, x_12);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_instBEqModuleIdx;
lean_inc(x_9);
x_12 = lean_apply_2(x_11, x_7, x_9);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(x_8, x_10);
lean_dec(x_8);
if (x_15 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = lean_uint64_of_nat(x_4);
x_8 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_5);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4___redArg(x_2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
x_10 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_array_get_size(x_1);
x_32 = lean_uint64_of_nat(x_29);
x_33 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_instBEqModuleIdx;
lean_inc(x_13);
lean_inc(x_11);
x_16 = lean_apply_2(x_15, x_11, x_13);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
goto block_10;
}
else
{
uint8_t x_18; 
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(x_12, x_14);
if (x_18 == 0)
{
goto block_10;
}
else
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_6);
return x_19;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 3, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_instBEqModuleIdx;
lean_inc(x_8);
x_11 = lean_apply_2(x_10, x_6, x_8);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_dec(x_7);
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(x_7, x_9);
lean_dec(x_7);
if (x_14 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc_ref(x_2);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_array_uset(x_6, x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_2, x_3, x_24);
x_40 = lean_array_uset(x_38, x_23, x_39);
lean_ctor_set(x_1, 1, x_40);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_array_get_size(x_42);
x_46 = lean_uint64_of_nat(x_43);
x_47 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_45);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_42, x_59);
lean_inc(x_60);
lean_inc_ref(x_2);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_41, x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_array_uset(x_42, x_59, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_42, x_59, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_2, x_3, x_60);
x_78 = lean_array_uset(x_76, x_59, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_inc_ref(x_6);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_5, x_6);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
lean_inc(x_3);
x_16 = l_Lean_Name_toString(x_3, x_15);
x_17 = lean_string_length(x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_Name_toString(x_14, x_15);
x_19 = lean_string_length(x_18);
lean_dec_ref(x_18);
x_20 = lean_nat_dec_lt(x_17, x_19);
if (x_20 == 0)
{
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
goto block_10;
}
}
else
{
lean_dec(x_12);
goto block_10;
}
}
else
{
lean_dec(x_11);
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0___redArg(x_5, x_6, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_18 = lean_array_uget(x_6, x_8);
x_19 = lean_array_get_borrowed(x_17, x_16, x_2);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_19, x_3, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___closed__1));
lean_inc(x_4);
x_22 = l_Lean_Name_append(x_21, x_4);
lean_inc(x_5);
lean_inc_ref(x_3);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation(x_18, x_3, x_5, x_22, x_9);
x_10 = x_23;
goto block_14;
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_8, x_11);
x_8 = x_12;
x_9 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f(x_1, x_7);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_22 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_10);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get_uint8(x_3, 0);
x_25 = lean_ctor_get_uint8(x_3, 1);
if (x_25 == 0)
{
lean_dec_ref(x_6);
x_26 = x_25;
goto block_29;
}
else
{
uint8_t x_30; 
lean_inc(x_10);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_6, x_10);
if (x_30 == 0)
{
x_26 = x_25;
goto block_29;
}
else
{
uint8_t x_31; 
x_31 = 0;
x_26 = x_31;
goto block_29;
}
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, 1, x_26);
lean_inc(x_10);
lean_inc(x_4);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation(x_23, x_27, x_4, x_10, x_8);
x_17 = x_28;
goto block_21;
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_6);
x_17 = x_8;
goto block_21;
}
block_16:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr_spec__0(x_1, x_2, x_3, x_10, x_4, x_12, x_13, x_14, x_11);
lean_dec_ref(x_12);
return x_15;
}
block_21:
{
lean_object* x_18; 
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0;
x_11 = x_17;
x_12 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_11 = x_17;
x_12 = x_20;
goto block_16;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr___lam__0___boxed), 8, 6);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_8);
lean_closure_set(x_9, 5, x_7);
x_10 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3;
x_11 = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(lean_box(0), x_9, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_26; uint8_t x_27; lean_object* x_40; uint8_t x_45; 
x_14 = lean_array_uget(x_4, x_6);
x_15 = l_Lean_ConstantInfo_name(x_14);
x_45 = l_Lean_isPrivateName(x_15);
if (x_45 == 0)
{
if (x_13 == 0)
{
goto block_44;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_1);
x_46 = l_Lean_Environment_setExporting(x_1, x_13);
lean_inc(x_15);
x_47 = l_Lean_Environment_find_x3f(x_46, x_15, x_45);
if (lean_obj_tag(x_47) == 0)
{
x_40 = x_47;
goto block_42;
}
else
{
x_26 = x_47;
x_27 = x_13;
goto block_39;
}
}
}
else
{
goto block_44;
}
block_20:
{
lean_object* x_19; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr(x_2, x_3, x_18, x_15, x_16, x_17);
x_8 = x_19;
goto block_12;
}
block_25:
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, 1, x_23);
x_16 = x_21;
x_17 = x_22;
x_18 = x_24;
goto block_20;
}
block_39:
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_15);
lean_inc_ref(x_1);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_1, x_15);
x_29 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, 1, x_28);
x_30 = l_Lean_ConstantInfo_type(x_14);
lean_inc(x_15);
lean_inc_ref(x_29);
lean_inc(x_3);
lean_inc_ref(x_2);
x_31 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr(x_2, x_3, x_29, x_15, x_30, x_7);
x_32 = l_Lean_ConstantInfo_value_x3f(x_14, x_13);
if (lean_obj_tag(x_32) == 1)
{
if (x_28 == 0)
{
lean_dec_ref(x_29);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_21 = x_33;
x_22 = x_31;
x_23 = x_28;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec_ref(x_26);
x_36 = l_Lean_ConstantInfo_hasValue(x_35, x_13);
lean_dec(x_35);
if (x_36 == 0)
{
x_21 = x_34;
x_22 = x_31;
x_23 = x_36;
goto block_25;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, 1, x_28);
x_16 = x_34;
x_17 = x_31;
x_18 = x_37;
goto block_20;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_26);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec_ref(x_32);
x_16 = x_38;
x_17 = x_31;
x_18 = x_29;
goto block_20;
}
}
else
{
lean_dec(x_32);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_15);
x_8 = x_31;
goto block_12;
}
}
block_42:
{
uint8_t x_41; 
x_41 = 0;
x_26 = x_40;
x_27 = x_41;
goto block_39;
}
block_44:
{
lean_object* x_43; 
x_43 = lean_box(0);
x_40 = x_43;
goto block_42;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = lean_uint64_of_nat(x_4);
x_8 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_5);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; 
x_12 = lean_array_uget(x_2, x_4);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
x_23 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_25 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_24);
x_13 = x_25;
goto block_21;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
x_13 = x_26;
goto block_21;
}
block_21:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_inc_ref(x_17);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0___redArg(x_5, x_17, x_19);
x_6 = x_20;
goto block_10;
}
else
{
lean_dec_ref(x_17);
x_6 = x_5;
goto block_10;
}
}
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = l_Lean_Environment_header(x_3);
x_5 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_instInhabitedModuleData_default;
x_7 = lean_array_get(x_6, x_5, x_2);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1;
x_10 = lean_array_size(x_8);
x_11 = 0;
lean_inc(x_2);
lean_inc_ref(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__1(x_3, x_1, x_2, x_8, x_10, x_11, x_9);
lean_dec_ref(x_8);
x_13 = l_Lean_getExtraModUses(x_3, x_2);
lean_dec(x_2);
x_14 = lean_array_size(x_13);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__2(x_3, x_13, x_14, x_11, x_12);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
lean_inc(x_2);
x_10 = lean_is_reserved_name(x_1, x_2);
if (x_10 == 0)
{
lean_dec(x_2);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0___redArg(x_4, x_2, x_11);
x_5 = x_12;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_array_uget(x_3, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_24 = l_Lean_Environment_getModuleIdx_x3f(x_2, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_26 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_25);
x_14 = x_26;
goto block_23;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_14 = x_27;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_16 = lean_array_push(x_8, x_14);
x_17 = lean_array_get_borrowed(x_13, x_15, x_14);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_9, x_11, x_14, x_17);
lean_dec(x_14);
lean_dec(x_11);
if (lean_is_scalar(x_10)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_10;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_1);
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_instInhabitedModuleData_default;
x_8 = lean_array_get_borrowed(x_7, x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0;
x_11 = lean_array_size(x_9);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(x_5, x_3, x_9, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_array_push(x_16, x_14);
lean_ctor_set(x_5, 1, x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
x_26 = lean_ctor_get(x_5, 5);
x_27 = lean_ctor_get(x_5, 6);
x_28 = lean_ctor_get(x_5, 7);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_29 = lean_array_push(x_22, x_14);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_4);
x_4 = x_32;
x_5 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_2);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_instInhabitedModuleData_default;
x_8 = lean_array_get_borrowed(x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0;
x_11 = lean_array_size(x_9);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(x_5, x_1, x_9, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_array_push(x_16, x_14);
lean_ctor_set(x_5, 1, x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
x_20 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(x_2, x_3, x_1, x_19, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
x_26 = lean_ctor_get(x_5, 5);
x_27 = lean_ctor_get(x_5, 6);
x_28 = lean_ctor_get(x_5, 7);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_29 = lean_array_push(x_22, x_14);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
x_33 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(x_2, x_3, x_1, x_32, x_30);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget_borrowed(x_2, x_4);
x_12 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_1);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_apply_4(x_1, x_5, x_11, x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_4 = x_18;
x_5 = x_15;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
lean_free_object(x_2);
x_13 = 0;
x_14 = lean_usize_of_nat(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_6, x_13, x_14, x_3, x_4);
lean_dec_ref(x_6);
return x_15;
}
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_2);
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_6, x_16, x_17, x_3, x_4);
lean_dec_ref(x_6);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
if (x_22 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_21);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_19, x_28, x_29, x_3, x_4);
lean_dec_ref(x_19);
return x_30;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_21);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_19, x_31, x_32, x_3, x_4);
lean_dec_ref(x_19);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(x_1, x_34, x_35, x_36, x_3, x_4);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_3, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_22 = lean_apply_4(x_1, x_5, x_20, x_21, x_6);
x_13 = x_22;
goto block_17;
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_24 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(x_1, x_23, x_5, x_6);
x_13 = x_24;
goto block_17;
}
default: 
{
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
block_17:
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_7 = x_15;
x_8 = x_16;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg___lam__0), 5, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(x_4, x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_10 = lean_apply_3(x_1, x_7, x_8, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_2 = x_12;
x_3 = x_9;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_box(0);
lean_inc_ref(x_1);
x_10 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5___redArg(x_1, x_9, x_8, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_6 = x_13;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
x_10 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(x_5, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
if (x_9 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_6);
x_13 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(x_5, x_2, x_3);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_inc_ref(x_2);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(x_2, x_6, x_14, x_15, x_11, x_3);
lean_dec_ref(x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(x_5, x_2, x_18);
return x_19;
}
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_8);
lean_inc_ref(x_2);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(x_2, x_6, x_20, x_21, x_11, x_3);
lean_dec_ref(x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(x_5, x_2, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__1));
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3;
x_6 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_7 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2;
lean_inc_ref(x_1);
x_32 = l_Lean_Environment_constants(x_1);
x_33 = l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3___redArg(x_32, x_2, x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_8 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_8 = x_36;
goto block_31;
}
block_31:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = l_Lean_indirectModUseExt;
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
lean_inc_ref(x_1);
x_13 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_3, x_9, x_1, x_11, x_12);
lean_dec(x_11);
x_14 = l_Lean_Environment_header(x_1);
lean_inc_ref(x_14);
x_15 = l_Lean_EnvironmentHeader_moduleNames(x_14);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set(x_16, 4, x_7);
lean_ctor_set(x_16, 5, x_8);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_15);
x_17 = lean_ctor_get(x_14, 6);
lean_inc_ref(x_17);
lean_dec_ref(x_14);
x_18 = lean_array_get_size(x_17);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg(x_1, x_18, x_17, x_4, x_16);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
lean_inc_ref(x_21);
lean_ctor_set(x_19, 2, x_21);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 3);
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_ctor_get(x_19, 5);
x_28 = lean_ctor_get(x_19, 6);
x_29 = lean_ctor_get(x_19, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
lean_inc_ref(x_24);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__7(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(x_2, x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(x_4, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0_spec__1_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(x_4, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Name_hash___override(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0;
x_6 = lean_array_push(x_5, x_3);
x_7 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_array_push(x_12, x_3);
lean_ctor_set(x_10, 0, x_13);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_array_push(x_15, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_add(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1;
x_6 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0;
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_array_push(x_12, x_3);
lean_ctor_set(x_10, 1, x_13);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_array_push(x_16, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1_spec__1(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Message_toString(x_2, x_1);
x_5 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
lean_dec(x_5);
x_10 = lean_nat_add(x_2, x_4);
x_11 = lean_string_utf8_get_fast(x_3, x_10);
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_string_utf8_next_fast(x_3, x_10);
lean_dec(x_10);
x_16 = lean_nat_sub(x_15, x_2);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_9 = lean_apply_2(x_1, x_8, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_7);
if (x_10 == 0)
{
if (x_9 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
lean_free_object(x_2);
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_5, x_11, x_12, x_8);
lean_dec_ref(x_5);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_free_object(x_2);
x_14 = 0;
x_15 = lean_usize_of_nat(x_7);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_5, x_14, x_15, x_8);
lean_dec_ref(x_5);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_box(0);
x_21 = lean_nat_dec_lt(x_18, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_19, x_19);
if (x_23 == 0)
{
if (x_21 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_19);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_17, x_25, x_26, x_20);
lean_dec_ref(x_17);
return x_27;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_19);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_17, x_28, x_29, x_20);
lean_dec_ref(x_17);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_32);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_36 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_2);
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_32, x_38, x_39, x_35);
lean_dec_ref(x_32);
return x_40;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
lean_free_object(x_2);
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_32, x_41, x_42, x_35);
lean_dec_ref(x_32);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_box(0);
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_44);
lean_dec_ref(x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_44);
lean_dec_ref(x_1);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_47);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_44, x_52, x_53, x_47);
lean_dec_ref(x_44);
return x_54;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_46);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_44, x_55, x_56, x_47);
lean_dec_ref(x_44);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_9 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0;
x_8 = lean_usize_shift_right(x_3, x_4);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get_borrowed(x_7, x_6, x_9);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
lean_inc(x_10);
lean_inc_ref(x_1);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4(x_1, x_10, x_14, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
x_22 = lean_array_get_size(x_6);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_17);
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = lean_usize_of_nat(x_22);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_26, x_27, x_23);
lean_dec_ref(x_6);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_17);
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_30 = lean_usize_of_nat(x_22);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_29, x_30, x_23);
lean_dec_ref(x_6);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_17);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_dec(x_9);
x_34 = lean_array_get_size(x_6);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
if (x_36 == 0)
{
lean_object* x_39; 
lean_dec(x_33);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = lean_usize_of_nat(x_34);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_40, x_41, x_35);
lean_dec_ref(x_6);
return x_42;
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_44 = lean_usize_of_nat(x_34);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_43, x_44, x_35);
lean_dec_ref(x_6);
return x_45;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_17;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_usize_to_nat(x_3);
x_49 = lean_array_get_size(x_47);
x_50 = lean_box(0);
x_51 = lean_nat_dec_lt(x_48, x_49);
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
lean_free_object(x_2);
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_47, x_53, x_54, x_50);
lean_dec_ref(x_47);
return x_55;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
lean_free_object(x_2);
x_56 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_57 = lean_usize_of_nat(x_49);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_47, x_56, x_57, x_50);
lean_dec_ref(x_47);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_usize_to_nat(x_3);
x_61 = lean_array_get_size(x_59);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
if (x_63 == 0)
{
lean_object* x_66; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_62);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_68 = lean_usize_of_nat(x_61);
x_69 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_59, x_67, x_68, x_62);
lean_dec_ref(x_59);
return x_69;
}
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; 
x_70 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_71 = lean_usize_of_nat(x_61);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_59, x_70, x_71, x_62);
lean_dec_ref(x_59);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_6 = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__5(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_5);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
if (x_12 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_free_object(x_6);
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_14, x_15, x_11);
lean_dec_ref(x_5);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_6);
x_17 = 0;
x_18 = lean_usize_of_nat(x_10);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_17, x_18, x_11);
lean_dec_ref(x_5);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_5);
x_22 = lean_box(0);
x_23 = lean_nat_dec_lt(x_20, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
if (x_23 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_27, x_28, x_22);
lean_dec_ref(x_5);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_21);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_30, x_31, x_22);
lean_dec_ref(x_5);
return x_32;
}
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_usize(x_2, 4);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_nat_dec_le(x_10, x_3);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_usize_of_nat(x_3);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4(x_1, x_7, x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_array_get_size(x_8);
x_17 = lean_box(0);
x_18 = lean_nat_dec_lt(x_5, x_16);
if (x_18 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_16, x_16);
if (x_19 == 0)
{
if (x_18 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_13);
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_20, x_21, x_17);
lean_dec_ref(x_8);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_13);
x_23 = 0;
x_24 = lean_usize_of_nat(x_16);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_23, x_24, x_17);
lean_dec_ref(x_8);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
x_26 = lean_array_get_size(x_8);
x_27 = lean_box(0);
x_28 = lean_nat_dec_lt(x_5, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
if (x_28 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_27);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_32, x_33, x_27);
lean_dec_ref(x_8);
return x_34;
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_26);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_35, x_36, x_27);
lean_dec_ref(x_8);
return x_37;
}
}
}
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_7);
x_38 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_39 = lean_array_get_size(x_8);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_38);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
if (x_41 == 0)
{
lean_object* x_44; 
lean_dec(x_38);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_40);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_46 = lean_usize_of_nat(x_39);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_45, x_46, x_40);
lean_dec_ref(x_8);
return x_47;
}
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_49 = lean_usize_of_nat(x_39);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_48, x_49, x_40);
lean_dec_ref(x_8);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
x_51 = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6(x_1, x_2);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 1;
x_5 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_2);
x_6 = l_Lean_Parser_mkInputContext___redArg(x_1, x_2, x_4, x_5);
lean_inc_ref(x_6);
x_7 = l_Lean_Parser_parseHeader(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_23; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_12 = x_8;
} else {
 lean_dec_ref(x_8);
 x_12 = lean_box(0);
}
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = l_Lean_MessageLog_toList(x_37);
x_39 = l_List_isEmpty___redArg(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0___boxed), 3, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2(x_37, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1));
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
x_46 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1));
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; lean_object* x_52; 
lean_dec(x_37);
x_51 = 0;
x_52 = l_Lean_Syntax_getTailPos_x3f(x_10, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_36, 0);
lean_inc(x_53);
lean_dec(x_36);
x_23 = x_53;
goto block_35;
}
else
{
lean_object* x_54; 
lean_dec(x_36);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_23 = x_54;
goto block_35;
}
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_String_Slice_Pos_next_x21(x_14, x_16);
lean_dec(x_16);
lean_dec_ref(x_14);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
if (lean_is_scalar(x_9)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_9;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
block_35:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_byte_size(x_25);
lean_inc_ref(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_String_Slice_pos_x21(x_28, x_23);
lean_dec(x_23);
lean_inc(x_29);
lean_inc_ref(x_25);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
x_31 = lean_box(0);
x_32 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(x_30, x_29, x_25, x_26, x_31);
lean_dec_ref(x_25);
lean_dec_ref(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_nat_sub(x_27, x_29);
x_13 = x_29;
x_14 = x_28;
x_15 = x_33;
goto block_22;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_13 = x_29;
x_14 = x_28;
x_15 = x_34;
goto block_22;
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
return x_7;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_dec(x_7);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0));
lean_inc(x_2);
x_5 = l_Lean_SearchPath_findModuleWithExt(x_1, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_free_object(x_5);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_IO_FS_readFile(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(x_10, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_15 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1));
x_16 = 1;
x_17 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_IO_FS_readFile(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(x_23, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_28 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1));
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec_ref(x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_panic_fn(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_26; uint8_t x_27; 
x_26 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4));
lean_inc(x_1);
x_27 = l_Lean_Syntax_isOfKind(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_29 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_30 = lean_unsigned_to_nat(389u);
x_31 = lean_unsigned_to_nat(11u);
x_32 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_33 = lean_box(0);
x_34 = l_Lean_Syntax_formatStx(x_1, x_33, x_27);
x_35 = l_Std_Format_defWidth;
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Std_Format_pretty(x_34, x_35, x_36, x_36);
x_38 = lean_string_append(x_32, x_37);
lean_dec_ref(x_37);
x_39 = l_mkPanicMessageWithDecl(x_28, x_29, x_30, x_31, x_38);
lean_dec_ref(x_38);
x_40 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_78; uint8_t x_79; 
x_41 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Syntax_getArg(x_1, x_41);
x_79 = l_Lean_Syntax_isNone(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_unsigned_to_nat(1u);
lean_inc(x_78);
x_81 = l_Lean_Syntax_matchesNull(x_78, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_78);
x_82 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_83 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_84 = lean_unsigned_to_nat(389u);
x_85 = lean_unsigned_to_nat(11u);
x_86 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_87 = lean_box(0);
x_88 = l_Lean_Syntax_formatStx(x_1, x_87, x_81);
x_89 = l_Std_Format_defWidth;
x_90 = l_Std_Format_pretty(x_88, x_89, x_41, x_41);
x_91 = lean_string_append(x_86, x_90);
lean_dec_ref(x_90);
x_92 = l_mkPanicMessageWithDecl(x_82, x_83, x_84, x_85, x_91);
lean_dec_ref(x_91);
x_93 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Lean_Syntax_getArg(x_78, x_41);
lean_dec(x_78);
x_95 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11));
lean_inc(x_94);
x_96 = l_Lean_Syntax_isOfKind(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_94);
x_97 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_98 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_99 = lean_unsigned_to_nat(389u);
x_100 = lean_unsigned_to_nat(11u);
x_101 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_102 = lean_box(0);
x_103 = l_Lean_Syntax_formatStx(x_1, x_102, x_96);
x_104 = l_Std_Format_defWidth;
x_105 = l_Std_Format_pretty(x_103, x_104, x_41, x_41);
x_106 = lean_string_append(x_101, x_105);
lean_dec_ref(x_105);
x_107 = l_mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_106);
lean_dec_ref(x_106);
x_108 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Syntax_getArg(x_94, x_41);
lean_dec(x_94);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_42 = x_110;
goto block_77;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_78);
x_111 = lean_box(0);
x_42 = x_111;
goto block_77;
}
block_77:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
x_45 = l_Lean_Syntax_isNone(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_inc(x_44);
x_46 = l_Lean_Syntax_matchesNull(x_44, x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_42);
x_47 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_48 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_49 = lean_unsigned_to_nat(389u);
x_50 = lean_unsigned_to_nat(11u);
x_51 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_52 = lean_box(0);
x_53 = l_Lean_Syntax_formatStx(x_1, x_52, x_46);
x_54 = l_Std_Format_defWidth;
x_55 = l_Std_Format_pretty(x_53, x_54, x_41, x_41);
x_56 = lean_string_append(x_51, x_55);
lean_dec_ref(x_55);
x_57 = l_mkPanicMessageWithDecl(x_47, x_48, x_49, x_50, x_56);
lean_dec_ref(x_56);
x_58 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Syntax_getArg(x_44, x_41);
lean_dec(x_44);
x_60 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9));
lean_inc(x_59);
x_61 = l_Lean_Syntax_isOfKind(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_59);
lean_dec(x_42);
x_62 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_63 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_64 = lean_unsigned_to_nat(389u);
x_65 = lean_unsigned_to_nat(11u);
x_66 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_67 = lean_box(0);
x_68 = l_Lean_Syntax_formatStx(x_1, x_67, x_61);
x_69 = l_Std_Format_defWidth;
x_70 = l_Std_Format_pretty(x_68, x_69, x_41, x_41);
x_71 = lean_string_append(x_66, x_70);
lean_dec_ref(x_70);
x_72 = l_mkPanicMessageWithDecl(x_62, x_63, x_64, x_65, x_71);
lean_dec_ref(x_71);
x_73 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Syntax_getArg(x_59, x_41);
lean_dec(x_59);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_16 = x_42;
x_17 = x_75;
goto block_25;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_44);
x_76 = lean_box(0);
x_16 = x_42;
x_17 = x_76;
goto block_25;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
block_15:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
x_2 = x_8;
x_3 = x_10;
x_4 = x_11;
goto block_7;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
x_2 = x_8;
x_3 = x_10;
x_4 = x_9;
goto block_7;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_2 = x_8;
x_3 = x_10;
x_4 = x_14;
goto block_7;
}
}
}
block_25:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_8 = x_20;
x_9 = x_17;
x_10 = x_21;
goto block_15;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
x_8 = x_20;
x_9 = x_17;
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_8 = x_20;
x_9 = x_17;
x_10 = x_24;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedImport_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1));
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_21 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_22 = lean_unsigned_to_nat(394u);
x_23 = lean_unsigned_to_nat(11u);
x_24 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_25 = lean_box(0);
x_26 = l_Lean_Syntax_formatStx(x_1, x_25, x_19);
x_27 = l_Std_Format_defWidth;
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Std_Format_pretty(x_26, x_27, x_28, x_28);
x_30 = lean_string_append(x_24, x_29);
lean_dec_ref(x_29);
x_31 = l_mkPanicMessageWithDecl(x_20, x_21, x_22, x_23, x_30);
lean_dec_ref(x_30);
x_32 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_95; lean_object* x_131; uint8_t x_132; 
x_33 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Syntax_getArg(x_1, x_33);
x_132 = l_Lean_Syntax_isNone(x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_unsigned_to_nat(1u);
lean_inc(x_131);
x_134 = l_Lean_Syntax_matchesNull(x_131, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_131);
x_135 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_136 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_137 = lean_unsigned_to_nat(394u);
x_138 = lean_unsigned_to_nat(11u);
x_139 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_140 = lean_box(0);
x_141 = l_Lean_Syntax_formatStx(x_1, x_140, x_134);
x_142 = l_Std_Format_defWidth;
x_143 = l_Std_Format_pretty(x_141, x_142, x_33, x_33);
x_144 = lean_string_append(x_139, x_143);
lean_dec_ref(x_143);
x_145 = l_mkPanicMessageWithDecl(x_135, x_136, x_137, x_138, x_144);
lean_dec_ref(x_144);
x_146 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_145);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArg(x_131, x_33);
lean_dec(x_131);
x_148 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__9));
lean_inc(x_147);
x_149 = l_Lean_Syntax_isOfKind(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_147);
x_150 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_151 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_152 = lean_unsigned_to_nat(394u);
x_153 = lean_unsigned_to_nat(11u);
x_154 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_155 = lean_box(0);
x_156 = l_Lean_Syntax_formatStx(x_1, x_155, x_149);
x_157 = l_Std_Format_defWidth;
x_158 = l_Std_Format_pretty(x_156, x_157, x_33, x_33);
x_159 = lean_string_append(x_154, x_158);
lean_dec_ref(x_158);
x_160 = l_mkPanicMessageWithDecl(x_150, x_151, x_152, x_153, x_159);
lean_dec_ref(x_159);
x_161 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_160);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = l_Lean_Syntax_getArg(x_147, x_33);
lean_dec(x_147);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_95 = x_163;
goto block_130;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_131);
x_164 = lean_box(0);
x_95 = x_164;
goto block_130;
}
block_56:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(5u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
x_39 = l_Lean_Syntax_matchesNull(x_38, x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_40 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_41 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_42 = lean_unsigned_to_nat(394u);
x_43 = lean_unsigned_to_nat(11u);
x_44 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_45 = lean_box(0);
x_46 = l_Lean_Syntax_formatStx(x_1, x_45, x_39);
x_47 = l_Std_Format_defWidth;
x_48 = l_Std_Format_pretty(x_46, x_47, x_33, x_33);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = l_mkPanicMessageWithDecl(x_40, x_41, x_42, x_43, x_49);
lean_dec_ref(x_49);
x_51 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_unsigned_to_nat(4u);
x_53 = l_Lean_Syntax_getArg(x_1, x_52);
lean_dec(x_1);
x_54 = l_Lean_TSyntax_getId(x_53);
lean_dec(x_53);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_55; 
x_55 = 0;
x_11 = x_35;
x_12 = x_34;
x_13 = x_54;
x_14 = x_39;
x_15 = x_55;
goto block_17;
}
else
{
lean_dec_ref(x_36);
x_11 = x_35;
x_12 = x_34;
x_13 = x_54;
x_14 = x_39;
x_15 = x_39;
goto block_17;
}
}
}
block_94:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(3u);
x_61 = l_Lean_Syntax_getArg(x_1, x_60);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_inc(x_61);
x_63 = l_Lean_Syntax_matchesNull(x_61, x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_57);
x_64 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_65 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_66 = lean_unsigned_to_nat(394u);
x_67 = lean_unsigned_to_nat(11u);
x_68 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_69 = lean_box(0);
x_70 = l_Lean_Syntax_formatStx(x_1, x_69, x_63);
x_71 = l_Std_Format_defWidth;
x_72 = l_Std_Format_pretty(x_70, x_71, x_33, x_33);
x_73 = lean_string_append(x_68, x_72);
lean_dec_ref(x_72);
x_74 = l_mkPanicMessageWithDecl(x_64, x_65, x_66, x_67, x_73);
lean_dec_ref(x_73);
x_75 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = l_Lean_Syntax_getArg(x_61, x_33);
lean_dec(x_61);
x_77 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__5));
lean_inc(x_76);
x_78 = l_Lean_Syntax_isOfKind(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
lean_dec(x_59);
lean_dec(x_57);
x_79 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_80 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_81 = lean_unsigned_to_nat(394u);
x_82 = lean_unsigned_to_nat(11u);
x_83 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_84 = lean_box(0);
x_85 = l_Lean_Syntax_formatStx(x_1, x_84, x_78);
x_86 = l_Std_Format_defWidth;
x_87 = l_Std_Format_pretty(x_85, x_86, x_33, x_33);
x_88 = lean_string_append(x_83, x_87);
lean_dec_ref(x_87);
x_89 = l_mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_88);
lean_dec_ref(x_88);
x_90 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Syntax_getArg(x_76, x_33);
lean_dec(x_76);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_34 = x_59;
x_35 = x_57;
x_36 = x_92;
goto block_56;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_61);
x_93 = lean_box(0);
x_34 = x_59;
x_35 = x_57;
x_36 = x_93;
goto block_56;
}
}
block_130:
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
x_98 = l_Lean_Syntax_isNone(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
lean_inc(x_97);
x_99 = l_Lean_Syntax_matchesNull(x_97, x_96);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_97);
lean_dec(x_95);
x_100 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_101 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_102 = lean_unsigned_to_nat(394u);
x_103 = lean_unsigned_to_nat(11u);
x_104 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_105 = lean_box(0);
x_106 = l_Lean_Syntax_formatStx(x_1, x_105, x_99);
x_107 = l_Std_Format_defWidth;
x_108 = l_Std_Format_pretty(x_106, x_107, x_33, x_33);
x_109 = lean_string_append(x_104, x_108);
lean_dec_ref(x_108);
x_110 = l_mkPanicMessageWithDecl(x_100, x_101, x_102, x_103, x_109);
lean_dec_ref(x_109);
x_111 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Lean_Syntax_getArg(x_97, x_33);
lean_dec(x_97);
x_113 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__7));
lean_inc(x_112);
x_114 = l_Lean_Syntax_isOfKind(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_112);
lean_dec(x_95);
x_115 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_116 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_117 = lean_unsigned_to_nat(394u);
x_118 = lean_unsigned_to_nat(11u);
x_119 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__3));
x_120 = lean_box(0);
x_121 = l_Lean_Syntax_formatStx(x_1, x_120, x_114);
x_122 = l_Std_Format_defWidth;
x_123 = l_Std_Format_pretty(x_121, x_122, x_33, x_33);
x_124 = lean_string_append(x_119, x_123);
lean_dec_ref(x_123);
x_125 = l_mkPanicMessageWithDecl(x_115, x_116, x_117, x_118, x_124);
lean_dec_ref(x_124);
x_126 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeImport_spec__0(x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_Syntax_getArg(x_112, x_33);
lean_dec(x_112);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_57 = x_95;
x_58 = x_96;
x_59 = x_128;
goto block_94;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_97);
x_129 = lean_box(0);
x_57 = x_95;
x_58 = x_96;
x_59 = x_129;
goto block_94;
}
}
}
block_10:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_3);
x_9 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_5);
return x_9;
}
}
block_17:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_16; 
x_16 = 0;
x_2 = x_15;
x_3 = x_12;
x_4 = x_13;
x_5 = x_14;
x_6 = x_16;
goto block_10;
}
else
{
lean_dec_ref(x_11);
x_2 = x_15;
x_3 = x_12;
x_4 = x_13;
x_5 = x_14;
x_6 = x_14;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_4);
x_7 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(x_1, x_2, x_3, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = l_Lean_Environment_getModuleIdx_x3f(x_8, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_dec_ref(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_31; uint8_t x_32; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_31 = lean_array_get_borrowed(x_13, x_10, x_1);
x_32 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_31, x_4, x_12);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get_uint8(x_4, 0);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, 1, x_34);
x_36 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_31, x_35, x_12);
lean_dec_ref(x_35);
x_14 = x_36;
goto block_30;
}
else
{
x_14 = x_32;
goto block_30;
}
block_30:
{
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_4);
return x_7;
}
else
{
uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_15 = 0;
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_get_borrowed(x_13, x_9, x_12);
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_13, x_16, x_12, x_18);
lean_dec(x_12);
lean_dec_ref(x_16);
lean_ctor_set_uint8(x_4, 0, x_14);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_19, x_4, x_3);
lean_dec_ref(x_4);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_21, 0, x_14);
lean_ctor_set_uint8(x_21, 1, x_15);
x_22 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_19, x_21, x_3);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
if (x_22 == 0)
{
lean_dec_ref(x_11);
return x_7;
}
else
{
return x_11;
}
}
else
{
lean_dec_ref(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_11);
return x_7;
}
else
{
return x_11;
}
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
x_24 = lean_array_get_borrowed(x_13, x_9, x_12);
x_25 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_13, x_16, x_12, x_24);
lean_dec(x_12);
lean_dec_ref(x_16);
x_26 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_26, 0, x_14);
lean_ctor_set_uint8(x_26, 1, x_23);
x_27 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_26, x_3);
lean_dec_ref(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_28, 0, x_14);
lean_ctor_set_uint8(x_28, 1, x_15);
x_29 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_28, x_3);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
if (x_29 == 0)
{
lean_dec_ref(x_11);
return x_7;
}
else
{
return x_11;
}
}
else
{
lean_dec_ref(x_25);
if (x_27 == 0)
{
lean_dec_ref(x_11);
return x_7;
}
else
{
return x_11;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_4);
return x_7;
}
}
else
{
lean_object* x_37; 
lean_dec_ref(x_4);
x_37 = lean_box(0);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
lean_dec(x_3);
x_9 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__0));
x_10 = lean_string_append(x_1, x_9);
if (x_7 == 0)
{
lean_object* x_32; 
x_32 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_28 = x_32;
goto block_31;
}
else
{
lean_object* x_33; 
x_33 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_28 = x_33;
goto block_31;
}
block_19:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_10, x_16);
lean_dec_ref(x_16);
x_1 = x_17;
x_2 = x_4;
goto _start;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_24 = lean_string_append(x_22, x_23);
if (x_6 == 0)
{
lean_object* x_25; 
x_25 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_11 = x_24;
x_12 = x_25;
goto block_19;
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_11 = x_24;
x_12 = x_26;
goto block_19;
}
}
block_31:
{
if (x_8 == 0)
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_20 = x_28;
x_21 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_20 = x_28;
x_21 = x_30;
goto block_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
lean_dec(x_4);
x_9 = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__1));
if (x_7 == 0)
{
lean_object* x_32; 
x_32 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_28 = x_32;
goto block_31;
}
else
{
lean_object* x_33; 
x_33 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_28 = x_33;
goto block_31;
}
block_19:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = lean_string_append(x_9, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__2));
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_24 = lean_string_append(x_22, x_23);
if (x_6 == 0)
{
lean_object* x_25; 
x_25 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_10 = x_24;
x_11 = x_25;
goto block_19;
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_10 = x_24;
x_11 = x_26;
goto block_19;
}
}
block_31:
{
if (x_8 == 0)
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_20 = x_28;
x_21 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_20 = x_28;
x_21 = x_30;
goto block_27;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; lean_object* x_52; lean_object* x_59; 
lean_inc(x_3);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*1 + 1);
x_38 = lean_ctor_get_uint8(x_34, sizeof(void*)*1 + 2);
lean_dec(x_34);
x_39 = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17___closed__1));
if (x_37 == 0)
{
lean_object* x_63; 
x_63 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_59 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_59 = x_64;
goto block_62;
}
block_50:
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; 
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = 1;
x_44 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_35, x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_46 = lean_string_append(x_39, x_45);
lean_dec_ref(x_45);
x_47 = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23(x_46, x_3);
x_48 = 93;
x_49 = lean_string_push(x_47, x_48);
return x_49;
}
block_58:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_string_append(x_51, x_52);
lean_dec_ref(x_52);
x_54 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_55 = lean_string_append(x_53, x_54);
if (x_36 == 0)
{
lean_object* x_56; 
x_56 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_40 = x_55;
x_41 = x_56;
goto block_50;
}
else
{
lean_object* x_57; 
x_57 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_40 = x_55;
x_41 = x_57;
goto block_50;
}
}
block_62:
{
if (x_38 == 0)
{
lean_object* x_60; 
x_60 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_51 = x_59;
x_52 = x_60;
goto block_58;
}
else
{
lean_object* x_61; 
x_61 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_51 = x_59;
x_52 = x_61;
goto block_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove(x_5, x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = 0;
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_5; 
lean_dec_ref(x_2);
x_5 = 1;
return x_5;
}
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_nat_add(x_9, x_7);
lean_dec(x_7);
x_11 = lean_string_utf8_next_fast(x_8, x_10);
lean_dec(x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_12);
x_3 = x_4;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_nat_add(x_16, x_14);
lean_dec(x_14);
x_18 = lean_string_utf8_next_fast(x_15, x_17);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_16);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_2 = x_20;
x_3 = x_4;
goto _start;
}
}
case 2:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_nat_sub(x_29, x_28);
x_31 = lean_nat_dec_lt(x_25, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_free_object(x_2);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_26);
lean_dec(x_26);
if (x_33 == 0)
{
return x_3;
}
else
{
lean_object* x_34; 
x_34 = lean_box(3);
x_2 = x_34;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
x_38 = lean_ctor_get(x_23, 2);
x_39 = lean_nat_add(x_28, x_25);
x_40 = lean_string_get_byte_fast(x_27, x_39);
x_41 = lean_nat_add(x_37, x_26);
x_42 = lean_string_get_byte_fast(x_36, x_41);
x_43 = lean_uint8_dec_eq(x_40, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_26, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_26, x_46);
lean_dec(x_26);
x_48 = lean_array_fget_borrowed(x_24, x_47);
lean_dec(x_47);
x_49 = lean_nat_dec_eq(x_48, x_44);
if (x_49 == 0)
{
lean_inc(x_48);
lean_ctor_set(x_2, 3, x_48);
x_3 = x_4;
goto _start;
}
else
{
lean_object* x_51; 
x_51 = l_String_Slice_posGE___redArg(x_1, x_25);
lean_ctor_set(x_2, 3, x_44);
lean_ctor_set(x_2, 2, x_51);
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_26);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_25, x_53);
lean_dec(x_25);
x_55 = l_String_Slice_posGE___redArg(x_1, x_54);
lean_ctor_set(x_2, 3, x_44);
lean_ctor_set(x_2, 2, x_55);
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_26, x_57);
lean_dec(x_26);
x_59 = lean_nat_sub(x_38, x_37);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_nat_add(x_25, x_57);
lean_dec(x_25);
lean_ctor_set(x_2, 3, x_58);
lean_ctor_set(x_2, 2, x_61);
goto _start;
}
else
{
lean_dec(x_58);
lean_free_object(x_2);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
return x_60;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
x_65 = lean_ctor_get(x_2, 2);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
x_69 = lean_ctor_get(x_1, 2);
x_70 = lean_nat_sub(x_69, x_68);
x_71 = lean_nat_dec_lt(x_65, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_66);
lean_dec(x_66);
if (x_73 == 0)
{
return x_3;
}
else
{
lean_object* x_74; 
x_74 = lean_box(3);
x_2 = x_74;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_63, 0);
x_77 = lean_ctor_get(x_63, 1);
x_78 = lean_ctor_get(x_63, 2);
x_79 = lean_nat_add(x_68, x_65);
x_80 = lean_string_get_byte_fast(x_67, x_79);
x_81 = lean_nat_add(x_77, x_66);
x_82 = lean_string_get_byte_fast(x_76, x_81);
x_83 = lean_uint8_dec_eq(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_66, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_66, x_86);
lean_dec(x_66);
x_88 = lean_array_fget_borrowed(x_64, x_87);
lean_dec(x_87);
x_89 = lean_nat_dec_eq(x_88, x_84);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc(x_88);
x_90 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_90, 0, x_63);
lean_ctor_set(x_90, 1, x_64);
lean_ctor_set(x_90, 2, x_65);
lean_ctor_set(x_90, 3, x_88);
x_2 = x_90;
x_3 = x_4;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_String_Slice_posGE___redArg(x_1, x_65);
x_93 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_93, 0, x_63);
lean_ctor_set(x_93, 1, x_64);
lean_ctor_set(x_93, 2, x_92);
lean_ctor_set(x_93, 3, x_84);
x_2 = x_93;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_66);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_65, x_95);
lean_dec(x_65);
x_97 = l_String_Slice_posGE___redArg(x_1, x_96);
x_98 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_98, 0, x_63);
lean_ctor_set(x_98, 1, x_64);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_84);
x_2 = x_98;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_66, x_100);
lean_dec(x_66);
x_102 = lean_nat_sub(x_78, x_77);
x_103 = lean_nat_dec_eq(x_101, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_nat_add(x_65, x_100);
lean_dec(x_65);
x_105 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_105, 0, x_63);
lean_ctor_set(x_105, 1, x_64);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_101);
x_2 = x_105;
goto _start;
}
else
{
lean_dec(x_101);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
return x_103;
}
}
}
}
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(x_1, x_2, x_4);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4;
x_3 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__2;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5;
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6));
x_2 = x_8;
goto block_5;
}
block_5:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(x_1, x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_ctor_get(x_1, 7);
x_9 = lean_box(0);
x_10 = lean_array_uget(x_3, x_4);
x_11 = lean_array_get_borrowed(x_9, x_8, x_2);
lean_inc(x_11);
x_12 = l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_add(x_6, x_11, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_6 = x_12;
goto _start;
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3_spec__4(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_8, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_156; lean_object* x_157; lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_187; lean_object* x_188; lean_object* x_198; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_array_uget(x_6, x_8);
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_50 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_51 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
x_187 = 0;
x_198 = l_Lean_Environment_getModuleIdx_x3f(x_22, x_48);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_200 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_199);
x_188 = x_200;
goto block_197;
}
else
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
lean_dec_ref(x_198);
x_188 = x_201;
goto block_197;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_array_push(x_24, x_23);
x_12 = x_27;
x_13 = x_25;
x_14 = lean_box(0);
goto block_18;
}
block_42:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_string_append(x_30, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_34, x_31);
lean_dec_ref(x_31);
x_36 = lean_string_append(x_29, x_35);
lean_dec_ref(x_35);
x_37 = lean_string_append(x_36, x_32);
lean_dec_ref(x_32);
x_38 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_24 = x_9;
x_25 = x_10;
x_26 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
block_47:
{
lean_object* x_46; 
x_46 = lean_array_push(x_43, x_23);
x_12 = x_46;
x_13 = x_44;
x_14 = lean_box(0);
goto block_18;
}
block_62:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_string_append(x_53, x_57);
lean_dec_ref(x_57);
x_59 = lean_string_append(x_58, x_56);
lean_dec_ref(x_56);
if (x_49 == 0)
{
lean_object* x_60; 
x_60 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_29 = x_52;
x_30 = x_59;
x_31 = x_54;
x_32 = x_55;
x_33 = x_60;
goto block_42;
}
else
{
lean_object* x_61; 
x_61 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_29 = x_52;
x_30 = x_59;
x_31 = x_54;
x_32 = x_55;
x_33 = x_61;
goto block_42;
}
}
block_77:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_string_append(x_65, x_66);
lean_dec_ref(x_66);
x_68 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_48, x_63);
x_69 = lean_string_append(x_67, x_68);
lean_dec_ref(x_68);
x_70 = lean_string_append(x_64, x_69);
lean_dec_ref(x_69);
x_71 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__0));
x_72 = lean_string_append(x_70, x_71);
x_73 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_74; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
block_87:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_84 = lean_string_append(x_82, x_83);
if (x_49 == 0)
{
lean_object* x_85; 
x_85 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_63 = x_78;
x_64 = x_79;
x_65 = x_84;
x_66 = x_85;
goto block_77;
}
else
{
lean_object* x_86; 
x_86 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_63 = x_78;
x_64 = x_79;
x_65 = x_84;
x_66 = x_86;
goto block_77;
}
}
block_93:
{
if (x_51 == 0)
{
lean_object* x_91; 
x_91 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_78 = x_88;
x_79 = x_89;
x_80 = x_90;
x_81 = x_91;
goto block_87;
}
else
{
lean_object* x_92; 
x_92 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_78 = x_88;
x_79 = x_89;
x_80 = x_90;
x_81 = x_92;
goto block_87;
}
}
block_108:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_string_append(x_96, x_97);
lean_dec_ref(x_97);
x_99 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_48, x_95);
x_100 = lean_string_append(x_98, x_99);
lean_dec_ref(x_99);
x_101 = lean_string_append(x_94, x_100);
lean_dec_ref(x_100);
x_102 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__1));
x_103 = lean_string_append(x_101, x_102);
x_104 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_dec_ref(x_104);
x_43 = x_9;
x_44 = x_10;
x_45 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
block_118:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_string_append(x_111, x_112);
lean_dec_ref(x_112);
x_114 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_115 = lean_string_append(x_113, x_114);
if (x_49 == 0)
{
lean_object* x_116; 
x_116 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_94 = x_109;
x_95 = x_110;
x_96 = x_115;
x_97 = x_116;
goto block_108;
}
else
{
lean_object* x_117; 
x_117 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_94 = x_109;
x_95 = x_110;
x_96 = x_115;
x_97 = x_117;
goto block_108;
}
}
block_124:
{
if (x_51 == 0)
{
lean_object* x_122; 
x_122 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_109 = x_119;
x_110 = x_120;
x_111 = x_121;
x_112 = x_122;
goto block_118;
}
else
{
lean_object* x_123; 
x_123 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_109 = x_119;
x_110 = x_120;
x_111 = x_121;
x_112 = x_123;
goto block_118;
}
}
block_139:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_string_append(x_125, x_129);
lean_dec_ref(x_129);
x_131 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_48, x_126);
x_132 = lean_string_append(x_130, x_131);
lean_inc_ref(x_127);
x_133 = lean_string_append(x_127, x_132);
lean_dec_ref(x_132);
x_134 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__2));
x_135 = lean_string_append(x_133, x_134);
x_136 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_51 == 0)
{
lean_object* x_137; 
x_137 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_52 = x_135;
x_53 = x_136;
x_54 = x_131;
x_55 = x_127;
x_56 = x_128;
x_57 = x_137;
goto block_62;
}
else
{
lean_object* x_138; 
x_138 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_52 = x_135;
x_53 = x_136;
x_54 = x_131;
x_55 = x_127;
x_56 = x_128;
x_57 = x_138;
goto block_62;
}
}
block_149:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_string_append(x_142, x_143);
lean_dec_ref(x_143);
x_145 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_146 = lean_string_append(x_144, x_145);
if (x_49 == 0)
{
lean_object* x_147; 
x_147 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_125 = x_146;
x_126 = x_140;
x_127 = x_141;
x_128 = x_145;
x_129 = x_147;
goto block_139;
}
else
{
lean_object* x_148; 
x_148 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_125 = x_146;
x_126 = x_140;
x_127 = x_141;
x_128 = x_145;
x_129 = x_148;
goto block_139;
}
}
block_155:
{
if (x_51 == 0)
{
lean_object* x_153; 
x_153 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_140 = x_150;
x_141 = x_151;
x_142 = x_152;
x_143 = x_153;
goto block_149;
}
else
{
lean_object* x_154; 
x_154 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_140 = x_150;
x_141 = x_151;
x_142 = x_152;
x_143 = x_154;
goto block_149;
}
}
block_171:
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
uint8_t x_159; 
lean_ctor_set_uint8(x_157, 0, x_2);
x_159 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_3, x_157, x_156);
lean_dec(x_156);
lean_dec_ref(x_157);
if (x_159 == 0)
{
lean_dec(x_48);
lean_dec(x_23);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_160; 
x_160 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
if (x_160 == 0)
{
lean_dec(x_48);
x_24 = x_9;
x_25 = x_10;
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_161; 
x_161 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_50 == 0)
{
lean_object* x_162; 
x_162 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_150 = x_160;
x_151 = x_161;
x_152 = x_162;
goto block_155;
}
else
{
lean_object* x_163; 
x_163 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_150 = x_160;
x_151 = x_161;
x_152 = x_163;
goto block_155;
}
}
}
}
else
{
uint8_t x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get_uint8(x_157, 1);
lean_dec(x_157);
x_165 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_165, 0, x_2);
lean_ctor_set_uint8(x_165, 1, x_164);
x_166 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_3, x_165, x_156);
lean_dec(x_156);
lean_dec_ref(x_165);
if (x_166 == 0)
{
lean_dec(x_48);
lean_dec(x_23);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_167; 
x_167 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
if (x_167 == 0)
{
lean_dec(x_48);
x_24 = x_9;
x_25 = x_10;
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_168; 
x_168 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_50 == 0)
{
lean_object* x_169; 
x_169 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_150 = x_167;
x_151 = x_168;
x_152 = x_169;
goto block_155;
}
else
{
lean_object* x_170; 
x_170 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_150 = x_167;
x_151 = x_168;
x_152 = x_170;
goto block_155;
}
}
}
}
}
block_176:
{
if (x_175 == 0)
{
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_48);
lean_dec(x_23);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
if (x_49 == 0)
{
x_156 = x_172;
x_157 = x_173;
goto block_171;
}
else
{
if (x_174 == 0)
{
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_48);
lean_dec(x_23);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
x_156 = x_172;
x_157 = x_173;
goto block_171;
}
}
}
}
block_186:
{
uint8_t x_180; 
x_180 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_5, x_178, x_177);
if (x_180 == 0)
{
uint8_t x_181; 
lean_dec_ref(x_178);
lean_dec(x_177);
x_181 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
if (x_181 == 0)
{
lean_dec(x_48);
x_43 = x_9;
x_44 = x_10;
x_45 = lean_box(0);
goto block_47;
}
else
{
lean_object* x_182; 
x_182 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_50 == 0)
{
lean_object* x_183; 
x_183 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_119 = x_182;
x_120 = x_181;
x_121 = x_183;
goto block_124;
}
else
{
lean_object* x_184; 
x_184 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_119 = x_182;
x_120 = x_181;
x_121 = x_184;
goto block_124;
}
}
}
else
{
uint8_t x_185; 
x_185 = lean_ctor_get_uint8(x_178, 0);
if (x_185 == 0)
{
x_172 = x_177;
x_173 = x_178;
x_174 = x_179;
x_175 = x_180;
goto block_176;
}
else
{
x_172 = x_177;
x_173 = x_178;
x_174 = x_179;
x_175 = x_179;
goto block_176;
}
}
}
block_197:
{
uint8_t x_189; uint8_t x_190; lean_object* x_191; 
x_189 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_190 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
x_191 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
if (x_189 == 0)
{
x_177 = x_188;
x_178 = x_191;
x_179 = x_187;
goto block_186;
}
else
{
uint8_t x_192; 
x_192 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_3, x_191, x_188);
if (x_192 == 0)
{
x_177 = x_188;
x_178 = x_191;
x_179 = x_192;
goto block_186;
}
else
{
lean_dec(x_23);
if (x_190 == 0)
{
lean_dec_ref(x_191);
lean_dec(x_188);
lean_dec(x_48);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_193; 
x_193 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_5, x_191, x_188);
lean_dec(x_188);
lean_dec_ref(x_191);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_50 == 0)
{
lean_object* x_195; 
x_195 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_88 = x_190;
x_89 = x_194;
x_90 = x_195;
goto block_93;
}
else
{
lean_object* x_196; 
x_196 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_88 = x_190;
x_89 = x_194;
x_90 = x_196;
goto block_93;
}
}
else
{
lean_dec(x_48);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_8, x_15);
x_8 = x_16;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_38; uint8_t x_39; 
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = 0;
x_32 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_33 = lean_array_uget(x_5, x_7);
x_38 = lean_array_get_borrowed(x_32, x_21, x_4);
x_39 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_38, x_33, x_1);
if (x_39 == 0)
{
x_34 = x_39;
goto block_37;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0));
x_41 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_22, x_40, x_1);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_42, 0, x_39);
lean_ctor_set_uint8(x_42, 1, x_41);
x_43 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_22, x_42, x_1);
lean_dec_ref(x_42);
x_34 = x_43;
goto block_37;
}
else
{
x_34 = x_41;
goto block_37;
}
}
block_31:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, 1, x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_shiftl(x_27, x_1);
x_29 = lean_nat_lor(x_26, x_28);
lean_dec(x_28);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_8, x_25, x_29);
lean_dec_ref(x_25);
x_11 = x_30;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
block_37:
{
if (x_34 == 0)
{
lean_dec(x_33);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_33, 0);
lean_dec(x_33);
if (x_35 == 0)
{
x_24 = x_35;
goto block_31;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 3);
x_24 = x_36;
goto block_31;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
static size_t _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_nat_dec_lt(x_6, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_15 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__1(x_6, x_1, x_2, x_3, x_14, x_15, x_16, x_5, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_21;
x_7 = x_20;
goto _start;
}
else
{
lean_dec(x_6);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_instBEqImport_beq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4_spec__6(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_29 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_31 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_30);
x_25 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec_ref(x_29);
x_25 = x_32;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_get_borrowed(x_24, x_22, x_25);
x_27 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_6, x_19, x_25, x_26);
lean_dec(x_25);
lean_dec(x_19);
x_9 = x_27;
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_dec(x_19);
x_9 = x_6;
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_26; 
x_26 = lean_usize_dec_lt(x_7, x_6);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_134; lean_object* x_138; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_31 = x_8;
} else {
 lean_dec_ref(x_8);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_34 = x_29;
} else {
 lean_dec_ref(x_29);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_array_uget(x_5, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
x_40 = lean_ctor_get_uint8(x_37, sizeof(void*)*1 + 1);
x_41 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_138 = l_Lean_Environment_getModuleIdx_x3f(x_35, x_38);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_140 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_139);
x_134 = x_140;
goto block_137;
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
lean_dec_ref(x_138);
x_134 = x_141;
goto block_137;
}
block_62:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_array_get_borrowed(x_41, x_36, x_43);
x_52 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_48, x_42, x_43, x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_shiftl(x_54, x_43);
lean_dec(x_43);
x_56 = lean_nat_lor(x_53, x_55);
lean_dec(x_55);
x_57 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_47, x_45, x_56);
lean_dec_ref(x_45);
x_58 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_3, x_42);
if (x_58 == 0)
{
if (x_44 == 0)
{
lean_dec_ref(x_42);
lean_dec(x_34);
lean_dec(x_31);
x_18 = lean_box(0);
x_19 = x_52;
x_20 = x_49;
x_21 = x_46;
x_22 = x_57;
goto block_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_push(x_46, x_42);
if (lean_is_scalar(x_34)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_34;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_52);
if (lean_is_scalar(x_31)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_31;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_11 = x_61;
x_12 = x_49;
x_13 = lean_box(0);
goto block_17;
}
}
else
{
lean_dec_ref(x_42);
lean_dec(x_34);
lean_dec(x_31);
x_18 = lean_box(0);
x_19 = x_52;
x_20 = x_49;
x_21 = x_46;
x_22 = x_57;
goto block_25;
}
}
block_81:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_string_append(x_63, x_70);
lean_dec_ref(x_70);
x_72 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_38, x_64);
x_73 = lean_string_append(x_71, x_72);
lean_dec_ref(x_72);
x_74 = lean_string_append(x_69, x_73);
lean_dec_ref(x_73);
x_75 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___closed__0));
x_76 = lean_string_append(x_74, x_75);
x_77 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_42 = x_66;
x_43 = x_65;
x_44 = x_67;
x_45 = x_68;
x_46 = x_30;
x_47 = x_32;
x_48 = x_33;
x_49 = x_9;
x_50 = lean_box(0);
goto block_62;
}
else
{
uint8_t x_78; 
lean_dec_ref(x_68);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_9);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_90 = lean_string_append(x_88, x_89);
if (x_39 == 0)
{
lean_object* x_91; 
x_91 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_63 = x_90;
x_64 = x_82;
x_65 = x_84;
x_66 = x_83;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
x_70 = x_91;
goto block_81;
}
else
{
lean_object* x_92; 
x_92 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_63 = x_90;
x_64 = x_82;
x_65 = x_84;
x_66 = x_83;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
x_70 = x_92;
goto block_81;
}
}
block_133:
{
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_37);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_37, 0);
lean_dec(x_98);
x_99 = l_Lean_Name_isPrefixOf(x_2, x_38);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_free_object(x_37);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_32);
lean_ctor_set(x_100, 1, x_33);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_30);
lean_ctor_set(x_101, 1, x_100);
x_11 = x_101;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_95);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
lean_inc(x_38);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 2, x_96);
lean_ctor_set_uint8(x_95, 1, x_96);
if (x_103 == 0)
{
lean_dec(x_38);
x_42 = x_37;
x_43 = x_94;
x_44 = x_99;
x_45 = x_95;
x_46 = x_30;
x_47 = x_32;
x_48 = x_33;
x_49 = x_9;
x_50 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_104; 
x_104 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_40 == 0)
{
lean_object* x_105; 
x_105 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_82 = x_103;
x_83 = x_37;
x_84 = x_94;
x_85 = x_99;
x_86 = x_95;
x_87 = x_104;
x_88 = x_105;
goto block_93;
}
else
{
lean_object* x_106; 
x_106 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_82 = x_103;
x_83 = x_37;
x_84 = x_94;
x_85 = x_99;
x_86 = x_95;
x_87 = x_104;
x_88 = x_106;
goto block_93;
}
}
}
else
{
uint8_t x_107; uint8_t x_108; lean_object* x_109; 
x_107 = lean_ctor_get_uint8(x_95, 0);
lean_dec(x_95);
x_108 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
lean_inc(x_38);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 2, x_96);
x_109 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, 1, x_96);
if (x_108 == 0)
{
lean_dec(x_38);
x_42 = x_37;
x_43 = x_94;
x_44 = x_99;
x_45 = x_109;
x_46 = x_30;
x_47 = x_32;
x_48 = x_33;
x_49 = x_9;
x_50 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_110; 
x_110 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_40 == 0)
{
lean_object* x_111; 
x_111 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_82 = x_108;
x_83 = x_37;
x_84 = x_94;
x_85 = x_99;
x_86 = x_109;
x_87 = x_110;
x_88 = x_111;
goto block_93;
}
else
{
lean_object* x_112; 
x_112 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_82 = x_108;
x_83 = x_37;
x_84 = x_94;
x_85 = x_99;
x_86 = x_109;
x_87 = x_110;
x_88 = x_112;
goto block_93;
}
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_37);
x_113 = l_Lean_Name_isPrefixOf(x_2, x_38);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_32);
lean_ctor_set(x_114, 1, x_33);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_30);
lean_ctor_set(x_115, 1, x_114);
x_11 = x_115;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get_uint8(x_95, 0);
if (lean_is_exclusive(x_95)) {
 x_117 = x_95;
} else {
 lean_dec_ref(x_95);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
lean_inc(x_38);
x_119 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_119, 0, x_38);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_39);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 1, x_40);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 2, x_96);
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 0, 2);
} else {
 x_120 = x_117;
}
lean_ctor_set_uint8(x_120, 0, x_116);
lean_ctor_set_uint8(x_120, 1, x_96);
if (x_118 == 0)
{
lean_dec(x_38);
x_42 = x_119;
x_43 = x_94;
x_44 = x_113;
x_45 = x_120;
x_46 = x_30;
x_47 = x_32;
x_48 = x_33;
x_49 = x_9;
x_50 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_121; 
x_121 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_40 == 0)
{
lean_object* x_122; 
x_122 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_82 = x_118;
x_83 = x_119;
x_84 = x_94;
x_85 = x_113;
x_86 = x_120;
x_87 = x_121;
x_88 = x_122;
goto block_93;
}
else
{
lean_object* x_123; 
x_123 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_82 = x_118;
x_83 = x_119;
x_84 = x_94;
x_85 = x_113;
x_86 = x_120;
x_87 = x_121;
x_88 = x_123;
goto block_93;
}
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
x_124 = lean_array_get_borrowed(x_41, x_36, x_94);
x_125 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_33, x_37, x_94, x_124);
lean_dec(x_37);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_shiftl(x_127, x_94);
lean_dec(x_94);
x_129 = lean_nat_lor(x_126, x_128);
lean_dec(x_128);
x_130 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_32, x_95, x_129);
lean_dec_ref(x_95);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_30);
lean_ctor_set(x_132, 1, x_131);
x_11 = x_132;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_137:
{
lean_object* x_135; uint8_t x_136; 
x_135 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_37);
x_136 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_32, x_135, x_134);
if (x_136 == 0)
{
x_94 = x_134;
x_95 = x_135;
x_96 = x_39;
goto block_133;
}
else
{
x_94 = x_134;
x_95 = x_135;
x_96 = x_136;
goto block_133;
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_11 = x_24;
x_12 = x_20;
x_13 = lean_box(0);
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_23 = l_Lean_Environment_getModuleIdx_x3f(x_11, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_25 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_24);
x_16 = x_25;
goto block_22;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
x_16 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_array_get_borrowed(x_15, x_12, x_16);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_5, x_13, x_16, x_17);
lean_dec(x_16);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_5 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_9, x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_36; uint8_t x_37; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_26 = x_10;
} else {
 lean_dec_ref(x_10);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_36 = lean_array_uget(x_7, x_9);
x_37 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_36, x_1);
if (x_37 == 0)
{
lean_dec(x_36);
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_29, x_36, x_1);
if (x_38 == 0)
{
if (x_37 == 0)
{
lean_dec(x_36);
goto block_35;
}
else
{
uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get_uint8(x_36, 0);
x_40 = lean_ctor_get_uint8(x_36, 1);
x_41 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_41, 0, x_37);
lean_ctor_set_uint8(x_41, 1, x_40);
x_42 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_29, x_41, x_1);
lean_dec_ref(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get(x_2, 7);
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 7);
x_49 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_144 = lean_box(0);
x_275 = lean_array_get_borrowed(x_144, x_45, x_1);
lean_inc(x_275);
x_276 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set_uint8(x_276, sizeof(void*)*1, x_42);
lean_ctor_set_uint8(x_276, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_276, sizeof(void*)*1 + 2, x_40);
if (x_48 == 0)
{
uint8_t x_286; 
x_286 = lean_unbox(x_27);
lean_dec(x_27);
lean_inc(x_1);
x_258 = x_25;
x_259 = x_276;
x_260 = x_1;
x_261 = x_36;
x_262 = x_286;
x_263 = x_29;
x_264 = x_30;
x_265 = x_11;
x_266 = lean_box(0);
goto block_274;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_302; 
x_287 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_39 == 0)
{
lean_object* x_306; 
x_306 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_302 = x_306;
goto block_305;
}
else
{
lean_object* x_307; 
x_307 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_302 = x_307;
goto block_305;
}
block_301:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_290 = lean_string_append(x_288, x_289);
lean_dec_ref(x_289);
x_291 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_292 = lean_string_append(x_290, x_291);
lean_inc(x_275);
x_293 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_275, x_48);
x_294 = lean_string_append(x_292, x_293);
lean_dec_ref(x_293);
x_295 = lean_string_append(x_287, x_294);
lean_dec_ref(x_294);
x_296 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__3));
x_297 = lean_string_append(x_295, x_296);
x_298 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_6, x_36, x_1);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_277 = x_297;
x_278 = x_299;
goto block_285;
}
else
{
lean_object* x_300; 
x_300 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__4));
x_277 = x_297;
x_278 = x_300;
goto block_285;
}
}
block_305:
{
if (x_40 == 0)
{
lean_object* x_303; 
x_303 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_288 = x_302;
x_289 = x_303;
goto block_301;
}
else
{
lean_object* x_304; 
x_304 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_288 = x_302;
x_289 = x_304;
goto block_301;
}
}
}
block_70:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_shiftl(x_60, x_50);
x_62 = lean_nat_lor(x_59, x_61);
lean_dec(x_61);
x_63 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_54, x_52, x_62);
lean_dec_ref(x_52);
x_64 = lean_array_get_borrowed(x_49, x_43, x_50);
x_65 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_55, x_53, x_50, x_64);
lean_dec(x_50);
lean_dec_ref(x_53);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = lean_box(x_51);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
x_13 = x_69;
x_14 = x_57;
x_15 = lean_box(0);
goto block_19;
}
block_82:
{
uint8_t x_80; 
x_80 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_3, x_73);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc_ref(x_73);
x_81 = lean_array_push(x_77, x_73);
x_50 = x_74;
x_51 = x_75;
x_52 = x_71;
x_53 = x_73;
x_54 = x_72;
x_55 = x_76;
x_56 = x_81;
x_57 = x_78;
x_58 = lean_box(0);
goto block_70;
}
else
{
x_50 = x_74;
x_51 = x_75;
x_52 = x_71;
x_53 = x_73;
x_54 = x_72;
x_55 = x_76;
x_56 = x_77;
x_57 = x_78;
x_58 = lean_box(0);
goto block_70;
}
}
block_106:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_string_append(x_94, x_95);
lean_dec_ref(x_95);
x_97 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_93, x_92);
x_98 = lean_string_append(x_96, x_97);
lean_dec_ref(x_97);
x_99 = lean_string_append(x_88, x_98);
lean_dec_ref(x_98);
x_100 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__0));
x_101 = lean_string_append(x_99, x_100);
x_102 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
x_71 = x_90;
x_72 = x_89;
x_73 = x_83;
x_74 = x_85;
x_75 = x_37;
x_76 = x_86;
x_77 = x_84;
x_78 = x_91;
x_79 = lean_box(0);
goto block_82;
}
else
{
uint8_t x_103; 
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
block_126:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_string_append(x_110, x_120);
lean_dec_ref(x_120);
x_122 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_123 = lean_string_append(x_121, x_122);
if (x_116 == 0)
{
lean_object* x_124; 
x_124 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_83 = x_113;
x_84 = x_114;
x_85 = x_107;
x_86 = x_115;
x_87 = lean_box(0);
x_88 = x_109;
x_89 = x_117;
x_90 = x_118;
x_91 = x_111;
x_92 = x_112;
x_93 = x_119;
x_94 = x_123;
x_95 = x_124;
goto block_106;
}
else
{
lean_object* x_125; 
x_125 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_83 = x_113;
x_84 = x_114;
x_85 = x_107;
x_86 = x_115;
x_87 = lean_box(0);
x_88 = x_109;
x_89 = x_117;
x_90 = x_118;
x_91 = x_111;
x_92 = x_112;
x_93 = x_119;
x_94 = x_123;
x_95 = x_125;
goto block_106;
}
}
block_143:
{
if (x_138 == 0)
{
lean_object* x_141; 
x_141 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_107 = x_127;
x_108 = lean_box(0);
x_109 = x_129;
x_110 = x_140;
x_111 = x_130;
x_112 = x_131;
x_113 = x_132;
x_114 = x_133;
x_115 = x_134;
x_116 = x_135;
x_117 = x_136;
x_118 = x_137;
x_119 = x_139;
x_120 = x_141;
goto block_126;
}
else
{
lean_object* x_142; 
x_142 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_107 = x_127;
x_108 = lean_box(0);
x_109 = x_129;
x_110 = x_140;
x_111 = x_130;
x_112 = x_131;
x_113 = x_132;
x_114 = x_133;
x_115 = x_134;
x_116 = x_135;
x_117 = x_136;
x_118 = x_137;
x_119 = x_139;
x_120 = x_142;
goto block_126;
}
}
block_172:
{
if (x_46 == 0)
{
x_71 = x_148;
x_72 = x_145;
x_73 = x_146;
x_74 = x_147;
x_75 = x_149;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_146, 0);
x_155 = lean_ctor_get_uint8(x_146, sizeof(void*)*1);
x_156 = lean_ctor_get_uint8(x_146, sizeof(void*)*1 + 1);
x_157 = lean_ctor_get_uint8(x_146, sizeof(void*)*1 + 2);
lean_inc_ref(x_148);
x_158 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(x_5, x_2, x_147, x_148, x_154);
if (lean_obj_tag(x_158) == 1)
{
uint8_t x_159; 
lean_dec(x_147);
x_159 = !lean_is_exclusive(x_146);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_146, 0);
lean_dec(x_160);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
lean_dec_ref(x_158);
x_162 = lean_array_get_borrowed(x_144, x_45, x_161);
lean_inc(x_162);
lean_ctor_set(x_146, 0, x_162);
if (x_48 == 0)
{
x_71 = x_148;
x_72 = x_145;
x_73 = x_146;
x_74 = x_161;
x_75 = x_37;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_163; 
x_163 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
if (x_156 == 0)
{
lean_object* x_164; 
x_164 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
lean_inc(x_162);
x_127 = x_161;
x_128 = lean_box(0);
x_129 = x_163;
x_130 = x_152;
x_131 = x_48;
x_132 = x_146;
x_133 = x_151;
x_134 = x_150;
x_135 = x_155;
x_136 = x_145;
x_137 = x_148;
x_138 = x_157;
x_139 = x_162;
x_140 = x_164;
goto block_143;
}
else
{
lean_object* x_165; 
x_165 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
lean_inc(x_162);
x_127 = x_161;
x_128 = lean_box(0);
x_129 = x_163;
x_130 = x_152;
x_131 = x_48;
x_132 = x_146;
x_133 = x_151;
x_134 = x_150;
x_135 = x_155;
x_136 = x_145;
x_137 = x_148;
x_138 = x_157;
x_139 = x_162;
x_140 = x_165;
goto block_143;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_146);
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_166);
lean_dec_ref(x_158);
x_167 = lean_array_get_borrowed(x_144, x_45, x_166);
lean_inc(x_167);
x_168 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_155);
lean_ctor_set_uint8(x_168, sizeof(void*)*1 + 1, x_156);
lean_ctor_set_uint8(x_168, sizeof(void*)*1 + 2, x_157);
if (x_48 == 0)
{
x_71 = x_148;
x_72 = x_145;
x_73 = x_168;
x_74 = x_166;
x_75 = x_37;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_169; 
x_169 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
if (x_156 == 0)
{
lean_object* x_170; 
x_170 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
lean_inc(x_167);
x_127 = x_166;
x_128 = lean_box(0);
x_129 = x_169;
x_130 = x_152;
x_131 = x_48;
x_132 = x_168;
x_133 = x_151;
x_134 = x_150;
x_135 = x_155;
x_136 = x_145;
x_137 = x_148;
x_138 = x_157;
x_139 = x_167;
x_140 = x_170;
goto block_143;
}
else
{
lean_object* x_171; 
x_171 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
lean_inc(x_167);
x_127 = x_166;
x_128 = lean_box(0);
x_129 = x_169;
x_130 = x_152;
x_131 = x_48;
x_132 = x_168;
x_133 = x_151;
x_134 = x_150;
x_135 = x_155;
x_136 = x_145;
x_137 = x_148;
x_138 = x_157;
x_139 = x_167;
x_140 = x_171;
goto block_143;
}
}
}
}
else
{
lean_dec(x_158);
x_71 = x_148;
x_72 = x_145;
x_73 = x_146;
x_74 = x_147;
x_75 = x_149;
x_76 = x_150;
x_77 = x_151;
x_78 = x_152;
x_79 = lean_box(0);
goto block_82;
}
}
}
block_197:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_string_append(x_180, x_186);
lean_dec_ref(x_186);
x_188 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_177, x_181);
x_189 = lean_string_append(x_187, x_188);
lean_dec_ref(x_188);
x_190 = lean_string_append(x_174, x_189);
lean_dec_ref(x_189);
x_191 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__2));
x_192 = lean_string_append(x_190, x_191);
x_193 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_dec_ref(x_193);
x_145 = x_185;
x_146 = x_178;
x_147 = x_175;
x_148 = x_173;
x_149 = x_183;
x_150 = x_184;
x_151 = x_176;
x_152 = x_179;
x_153 = lean_box(0);
goto block_172;
}
else
{
uint8_t x_194; 
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_173);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
return x_193;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
}
}
block_218:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_string_append(x_198, x_212);
lean_dec_ref(x_212);
x_214 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_215 = lean_string_append(x_213, x_214);
if (x_206 == 0)
{
lean_object* x_216; 
x_216 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_173 = x_199;
x_174 = x_200;
x_175 = x_201;
x_176 = x_202;
x_177 = x_203;
x_178 = x_204;
x_179 = x_205;
x_180 = x_215;
x_181 = x_207;
x_182 = lean_box(0);
x_183 = x_209;
x_184 = x_210;
x_185 = x_211;
x_186 = x_216;
goto block_197;
}
else
{
lean_object* x_217; 
x_217 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_173 = x_199;
x_174 = x_200;
x_175 = x_201;
x_176 = x_202;
x_177 = x_203;
x_178 = x_204;
x_179 = x_205;
x_180 = x_215;
x_181 = x_207;
x_182 = lean_box(0);
x_183 = x_209;
x_184 = x_210;
x_185 = x_211;
x_186 = x_217;
goto block_197;
}
}
block_257:
{
if (x_228 == 0)
{
x_145 = x_227;
x_146 = x_220;
x_147 = x_225;
x_148 = x_224;
x_149 = x_222;
x_150 = x_221;
x_151 = x_223;
x_152 = x_226;
x_153 = lean_box(0);
goto block_172;
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_224);
if (x_229 == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_220);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_220, 0);
x_232 = lean_ctor_get_uint8(x_220, sizeof(void*)*1);
x_233 = lean_ctor_get_uint8(x_220, sizeof(void*)*1 + 2);
lean_ctor_set_uint8(x_224, 0, x_37);
lean_inc(x_231);
lean_ctor_set_uint8(x_220, sizeof(void*)*1 + 1, x_37);
if (x_48 == 0)
{
lean_dec(x_231);
x_145 = x_227;
x_146 = x_220;
x_147 = x_225;
x_148 = x_224;
x_149 = x_222;
x_150 = x_221;
x_151 = x_223;
x_152 = x_226;
x_153 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
x_235 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_233 == 0)
{
lean_object* x_236; 
x_236 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_198 = x_235;
x_199 = x_224;
x_200 = x_234;
x_201 = x_225;
x_202 = x_223;
x_203 = x_231;
x_204 = x_220;
x_205 = x_226;
x_206 = x_232;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_236;
goto block_218;
}
else
{
lean_object* x_237; 
x_237 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_198 = x_235;
x_199 = x_224;
x_200 = x_234;
x_201 = x_225;
x_202 = x_223;
x_203 = x_231;
x_204 = x_220;
x_205 = x_226;
x_206 = x_232;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_237;
goto block_218;
}
}
}
else
{
lean_object* x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_220, 0);
x_239 = lean_ctor_get_uint8(x_220, sizeof(void*)*1);
x_240 = lean_ctor_get_uint8(x_220, sizeof(void*)*1 + 2);
lean_inc(x_238);
lean_dec(x_220);
lean_ctor_set_uint8(x_224, 0, x_37);
lean_inc(x_238);
x_241 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set_uint8(x_241, sizeof(void*)*1, x_239);
lean_ctor_set_uint8(x_241, sizeof(void*)*1 + 1, x_37);
lean_ctor_set_uint8(x_241, sizeof(void*)*1 + 2, x_240);
if (x_48 == 0)
{
lean_dec(x_238);
x_145 = x_227;
x_146 = x_241;
x_147 = x_225;
x_148 = x_224;
x_149 = x_222;
x_150 = x_221;
x_151 = x_223;
x_152 = x_226;
x_153 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
x_243 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_240 == 0)
{
lean_object* x_244; 
x_244 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_198 = x_243;
x_199 = x_224;
x_200 = x_242;
x_201 = x_225;
x_202 = x_223;
x_203 = x_238;
x_204 = x_241;
x_205 = x_226;
x_206 = x_239;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_244;
goto block_218;
}
else
{
lean_object* x_245; 
x_245 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_198 = x_243;
x_199 = x_224;
x_200 = x_242;
x_201 = x_225;
x_202 = x_223;
x_203 = x_238;
x_204 = x_241;
x_205 = x_226;
x_206 = x_239;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_245;
goto block_218;
}
}
}
}
else
{
uint8_t x_246; lean_object* x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get_uint8(x_224, 1);
lean_dec(x_224);
x_247 = lean_ctor_get(x_220, 0);
lean_inc(x_247);
x_248 = lean_ctor_get_uint8(x_220, sizeof(void*)*1);
x_249 = lean_ctor_get_uint8(x_220, sizeof(void*)*1 + 2);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_250 = x_220;
} else {
 lean_dec_ref(x_220);
 x_250 = lean_box(0);
}
x_251 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_251, 0, x_37);
lean_ctor_set_uint8(x_251, 1, x_246);
lean_inc(x_247);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 1, 3);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_248);
lean_ctor_set_uint8(x_252, sizeof(void*)*1 + 1, x_37);
lean_ctor_set_uint8(x_252, sizeof(void*)*1 + 2, x_249);
if (x_48 == 0)
{
lean_dec(x_247);
x_145 = x_227;
x_146 = x_252;
x_147 = x_225;
x_148 = x_251;
x_149 = x_222;
x_150 = x_221;
x_151 = x_223;
x_152 = x_226;
x_153 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
x_254 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_249 == 0)
{
lean_object* x_255; 
x_255 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_198 = x_254;
x_199 = x_251;
x_200 = x_253;
x_201 = x_225;
x_202 = x_223;
x_203 = x_247;
x_204 = x_252;
x_205 = x_226;
x_206 = x_248;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_255;
goto block_218;
}
else
{
lean_object* x_256; 
x_256 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_198 = x_254;
x_199 = x_251;
x_200 = x_253;
x_201 = x_225;
x_202 = x_223;
x_203 = x_247;
x_204 = x_252;
x_205 = x_226;
x_206 = x_248;
x_207 = x_48;
x_208 = lean_box(0);
x_209 = x_222;
x_210 = x_221;
x_211 = x_227;
x_212 = x_256;
goto block_218;
}
}
}
}
}
block_274:
{
if (x_47 == 0)
{
x_145 = x_258;
x_146 = x_259;
x_147 = x_260;
x_148 = x_261;
x_149 = x_262;
x_150 = x_263;
x_151 = x_264;
x_152 = x_265;
x_153 = lean_box(0);
goto block_172;
}
else
{
uint8_t x_267; 
x_267 = lean_ctor_get_uint8(x_261, 0);
if (x_267 == 0)
{
uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = lean_ctor_get_uint8(x_261, 1);
x_269 = lean_array_get_borrowed(x_49, x_44, x_5);
x_270 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_270, 0, x_37);
lean_ctor_set_uint8(x_270, 1, x_268);
x_271 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_269, x_270, x_260);
lean_dec_ref(x_270);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_272, 0, x_37);
lean_ctor_set_uint8(x_272, 1, x_37);
x_273 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_269, x_272, x_260);
lean_dec_ref(x_272);
x_219 = lean_box(0);
x_220 = x_259;
x_221 = x_263;
x_222 = x_262;
x_223 = x_264;
x_224 = x_261;
x_225 = x_260;
x_226 = x_265;
x_227 = x_258;
x_228 = x_273;
goto block_257;
}
else
{
x_219 = lean_box(0);
x_220 = x_259;
x_221 = x_263;
x_222 = x_262;
x_223 = x_264;
x_224 = x_261;
x_225 = x_260;
x_226 = x_265;
x_227 = x_258;
x_228 = x_271;
goto block_257;
}
}
else
{
x_145 = x_258;
x_146 = x_259;
x_147 = x_260;
x_148 = x_261;
x_149 = x_262;
x_150 = x_263;
x_151 = x_264;
x_152 = x_265;
x_153 = lean_box(0);
goto block_172;
}
}
}
block_285:
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_string_append(x_277, x_278);
lean_dec_ref(x_278);
x_280 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_279);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
lean_dec_ref(x_280);
x_281 = lean_unbox(x_27);
lean_dec(x_27);
lean_inc(x_1);
x_258 = x_25;
x_259 = x_276;
x_260 = x_1;
x_261 = x_36;
x_262 = x_281;
x_263 = x_29;
x_264 = x_30;
x_265 = x_11;
x_266 = lean_box(0);
goto block_274;
}
else
{
uint8_t x_282; 
lean_dec_ref(x_276);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec_ref(x_11);
lean_dec(x_1);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
return x_280;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_280, 0);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
}
}
}
else
{
lean_dec(x_36);
goto block_35;
}
}
}
else
{
lean_dec(x_36);
goto block_35;
}
}
block_35:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_28;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_13 = x_34;
x_14 = x_11;
x_15 = lean_box(0);
goto block_19;
}
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_9, x_16);
x_9 = x_17;
x_10 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_14, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_8, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_array_uget(x_6, x_8);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_24 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_25 = 0;
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_22, x_1, x_2, x_3, x_4, x_5, x_23, x_24, x_25, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_8, x_30);
x_8 = x_31;
x_9 = x_28;
x_10 = x_29;
goto _start;
}
else
{
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_array_uget(x_6, x_8);
x_36 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_15, 1, x_37);
x_38 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_39 = 0;
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_35, x_1, x_2, x_3, x_4, x_5, x_36, x_38, x_39, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = lean_usize_add(x_8, x_44);
x_8 = x_45;
x_9 = x_42;
x_10 = x_43;
goto _start;
}
else
{
return x_40;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_50 = x_16;
} else {
 lean_dec_ref(x_16);
 x_50 = lean_box(0);
}
x_51 = lean_array_uget(x_6, x_8);
x_52 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_9, 1, x_54);
x_55 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_56 = 0;
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_51, x_1, x_2, x_3, x_4, x_5, x_52, x_55, x_56, x_9, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 1;
x_62 = lean_usize_add(x_8, x_61);
x_8 = x_62;
x_9 = x_59;
x_10 = x_60;
goto _start;
}
else
{
return x_57;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_ctor_get(x_15, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_66 = x_15;
} else {
 lean_dec_ref(x_15);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_16, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_69 = x_16;
} else {
 lean_dec_ref(x_16);
 x_69 = lean_box(0);
}
x_70 = lean_array_uget(x_6, x_8);
x_71 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_76 = 0;
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_70, x_1, x_2, x_3, x_4, x_5, x_71, x_75, x_76, x_74, x_10);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = 1;
x_82 = lean_usize_add(x_8, x_81);
x_8 = x_82;
x_9 = x_79;
x_10 = x_80;
goto _start;
}
else
{
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_13, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4;
x_3 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5;
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6));
x_2 = x_8;
goto block_5;
}
block_5:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(x_1, x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_61; lean_object* x_62; lean_object* x_74; lean_object* x_75; lean_object* x_95; lean_object* x_102; lean_object* x_103; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget(x_5, x_7);
lean_inc(x_22);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_22);
x_102 = lean_ctor_get(x_23, 0);
lean_inc(x_102);
x_103 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_102);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_105 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_104);
x_95 = x_105;
goto block_101;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec_ref(x_103);
x_95 = x_106;
goto block_101;
}
block_40:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec_ref(x_23);
x_30 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_31 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_29, x_24);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_26, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__0));
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_36);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_37; 
lean_dec_ref(x_25);
lean_dec_ref(x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
block_52:
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_47 = lean_string_append(x_43, x_45);
lean_dec_ref(x_45);
x_48 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_49 = lean_string_append(x_47, x_48);
if (x_46 == 0)
{
lean_object* x_50; 
x_50 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_24 = x_41;
x_25 = x_42;
x_26 = x_44;
x_27 = x_49;
x_28 = x_50;
goto block_40;
}
else
{
lean_object* x_51; 
x_51 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_24 = x_41;
x_25 = x_42;
x_26 = x_44;
x_27 = x_49;
x_28 = x_51;
goto block_40;
}
}
block_60:
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_41 = x_53;
x_42 = x_54;
x_43 = x_56;
x_44 = x_55;
x_45 = x_58;
goto block_52;
}
else
{
lean_object* x_59; 
x_59 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_41 = x_53;
x_42 = x_54;
x_43 = x_56;
x_44 = x_55;
x_45 = x_59;
goto block_52;
}
}
block_73:
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 7);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_shiftl(x_65, x_61);
lean_dec(x_61);
x_67 = lean_nat_lor(x_64, x_66);
lean_dec(x_66);
x_68 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_8, x_62, x_67);
lean_dec_ref(x_62);
if (x_63 == 0)
{
lean_dec_ref(x_23);
x_11 = x_68;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_69; lean_object* x_70; 
x_69 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_70 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__1));
if (x_69 == 0)
{
lean_object* x_71; 
x_71 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_53 = x_63;
x_54 = x_68;
x_55 = x_70;
x_56 = x_71;
goto block_60;
}
else
{
lean_object* x_72; 
x_72 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_53 = x_63;
x_54 = x_68;
x_55 = x_70;
x_56 = x_72;
goto block_60;
}
}
}
block_94:
{
lean_object* x_76; 
x_76 = l_Lean_Syntax_getTrailing_x3f(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_23);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_ctor_get(x_77, 2);
x_82 = lean_string_utf8_extract(x_79, x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_string_utf8_byte_size(x_82);
lean_ctor_set(x_77, 2, x_84);
lean_ctor_set(x_77, 1, x_83);
lean_ctor_set(x_77, 0, x_82);
x_85 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(x_77);
lean_dec_ref(x_77);
if (x_85 == 0)
{
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_23);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
x_61 = x_74;
x_62 = x_75;
goto block_73;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
x_88 = lean_ctor_get(x_77, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_89 = lean_string_utf8_extract(x_86, x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_string_utf8_byte_size(x_89);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(x_92);
lean_dec_ref(x_92);
if (x_93 == 0)
{
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_23);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
x_61 = x_74;
x_62 = x_75;
goto block_73;
}
}
}
}
block_101:
{
lean_object* x_96; 
x_96 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
if (x_2 == 0)
{
uint8_t x_97; 
x_97 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_97 == 0)
{
x_74 = x_95;
x_75 = x_96;
goto block_94;
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
if (x_98 == 0)
{
x_74 = x_95;
x_75 = x_96;
goto block_94;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3));
x_100 = l_Lean_Name_isPrefixOf(x_99, x_3);
if (x_100 == 0)
{
lean_dec(x_22);
x_61 = x_95;
x_62 = x_96;
goto block_73;
}
else
{
x_74 = x_95;
x_75 = x_96;
goto block_94;
}
}
}
}
else
{
lean_dec(x_22);
x_61 = x_95;
x_62 = x_96;
goto block_73;
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9(x_1, x_11, x_3, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_1);
x_8 = l_Lean_instBEqImport_beq(x_6, x_7);
lean_dec_ref(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_8;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_1);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
else
{
if (x_23 == 0)
{
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; uint8_t x_27; 
x_24 = lean_array_uget(x_4, x_6);
x_25 = 0;
x_26 = lean_usize_of_nat(x_22);
lean_inc(x_24);
x_27 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19(x_24, x_1, x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_24);
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_49; lean_object* x_50; 
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_unsigned_to_nat(1u);
x_49 = 0;
x_50 = l_Lean_Syntax_getPos_x3f(x_24, x_49);
lean_dec(x_24);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_52 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_51);
x_30 = x_52;
goto block_48;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
x_30 = x_53;
goto block_48;
}
block_48:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_28);
x_31 = l_Lean_FileMap_toPosition(x_28, x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
lean_inc_ref(x_3);
x_35 = lean_string_append(x_3, x_34);
x_36 = l_Nat_reprFast(x_32);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_38 = lean_string_append(x_37, x_34);
x_39 = lean_nat_add(x_33, x_29);
lean_dec(x_33);
x_40 = l_Nat_reprFast(x_39);
x_41 = lean_string_append(x_38, x_40);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__1));
x_43 = lean_string_append(x_41, x_42);
x_44 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_10;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Name_isPrefixOf(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Options_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0;
x_4 = l_Lean_sanitizeName(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_82; uint8_t x_89; lean_object* x_90; lean_object* x_103; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_box(0);
x_89 = 0;
x_103 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_105 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_104);
x_90 = x_105;
goto block_102;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec_ref(x_103);
x_90 = x_106;
goto block_102;
}
block_63:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_31 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_29, x_1);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_25, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_36);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec_ref(x_27);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1));
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_38);
x_42 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_41, x_1);
x_43 = lean_string_append(x_40, x_42);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2));
x_45 = lean_string_append(x_43, x_44);
x_46 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_39);
x_47 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_46, x_1);
x_48 = lean_string_append(x_45, x_47);
lean_dec_ref(x_47);
x_49 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
x_50 = lean_string_append(x_48, x_49);
x_51 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_11 = x_24;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_52; 
lean_dec_ref(x_9);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_27);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_56 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_11 = x_24;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_57; 
lean_dec_ref(x_9);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_27);
lean_dec_ref(x_9);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
lean_dec(x_36);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_74:
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_69 = lean_string_append(x_66, x_67);
lean_dec_ref(x_67);
x_70 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_71 = lean_string_append(x_69, x_70);
if (x_68 == 0)
{
lean_object* x_72; 
x_72 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_25 = x_64;
x_26 = x_71;
x_27 = x_65;
x_28 = x_72;
goto block_63;
}
else
{
lean_object* x_73; 
x_73 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_25 = x_64;
x_26 = x_71;
x_27 = x_65;
x_28 = x_73;
goto block_63;
}
}
block_81:
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_64 = x_75;
x_65 = x_76;
x_66 = x_77;
x_67 = x_79;
goto block_74;
}
else
{
lean_object* x_80; 
x_80 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_64 = x_75;
x_65 = x_76;
x_66 = x_77;
x_67 = x_80;
goto block_74;
}
}
block_88:
{
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_85 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_84 == 0)
{
lean_object* x_86; 
x_86 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_75 = x_85;
x_76 = x_83;
x_77 = x_86;
goto block_81;
}
else
{
lean_object* x_87; 
x_87 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_75 = x_85;
x_76 = x_83;
x_77 = x_87;
goto block_81;
}
}
else
{
lean_dec(x_82);
lean_dec(x_22);
x_11 = x_24;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_102:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_22);
lean_inc_ref(x_91);
lean_inc(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
if (x_94 == 0)
{
lean_dec_ref(x_91);
lean_dec(x_90);
x_82 = x_93;
goto block_88;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_ctor_set_uint8(x_91, 0, x_89);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_91);
x_97 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_96);
x_82 = x_97;
goto block_88;
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get_uint8(x_91, 1);
lean_dec(x_91);
x_99 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_99, 0, x_89);
lean_ctor_set_uint8(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_100);
x_82 = x_101;
goto block_88;
}
}
}
else
{
lean_dec_ref(x_91);
lean_dec(x_90);
x_82 = x_93;
goto block_88;
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21(x_11, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_83; lean_object* x_90; lean_object* x_103; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = 0;
x_25 = lean_box(0);
x_103 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_105 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_104);
x_90 = x_105;
goto block_102;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec_ref(x_103);
x_90 = x_106;
goto block_102;
}
block_64:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_string_append(x_26, x_29);
lean_dec_ref(x_29);
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_30, x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = lean_string_append(x_28, x_33);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_36 = lean_string_append(x_34, x_35);
x_37 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec_ref(x_27);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1));
x_42 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_39);
x_43 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_42, x_1);
x_44 = lean_string_append(x_41, x_43);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2));
x_46 = lean_string_append(x_44, x_45);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_40);
x_48 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_47, x_1);
x_49 = lean_string_append(x_46, x_48);
lean_dec_ref(x_48);
x_50 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
x_51 = lean_string_append(x_49, x_50);
x_52 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_27);
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_57 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_58; 
lean_dec_ref(x_9);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_27);
lean_dec_ref(x_9);
x_61 = !lean_is_exclusive(x_37);
if (x_61 == 0)
{
return x_37;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_37, 0);
lean_inc(x_62);
lean_dec(x_37);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
block_75:
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_70 = lean_string_append(x_65, x_68);
lean_dec_ref(x_68);
x_71 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_72 = lean_string_append(x_70, x_71);
if (x_69 == 0)
{
lean_object* x_73; 
x_73 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_26 = x_72;
x_27 = x_66;
x_28 = x_67;
x_29 = x_73;
goto block_64;
}
else
{
lean_object* x_74; 
x_74 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_26 = x_72;
x_27 = x_66;
x_28 = x_67;
x_29 = x_74;
goto block_64;
}
}
block_82:
{
uint8_t x_79; 
x_79 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_65 = x_78;
x_66 = x_76;
x_67 = x_77;
x_68 = x_80;
goto block_75;
}
else
{
lean_object* x_81; 
x_81 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_65 = x_78;
x_66 = x_76;
x_67 = x_77;
x_68 = x_81;
goto block_75;
}
}
block_89:
{
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_86 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_85 == 0)
{
lean_object* x_87; 
x_87 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_76 = x_84;
x_77 = x_86;
x_78 = x_87;
goto block_82;
}
else
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_76 = x_84;
x_77 = x_86;
x_78 = x_88;
goto block_82;
}
}
else
{
lean_dec(x_83);
lean_dec(x_22);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_102:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_22);
lean_inc_ref(x_91);
lean_inc(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
if (x_94 == 0)
{
lean_dec_ref(x_91);
lean_dec(x_90);
x_83 = x_93;
goto block_89;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_ctor_set_uint8(x_91, 0, x_24);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_91);
x_97 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_96);
x_83 = x_97;
goto block_89;
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get_uint8(x_91, 1);
lean_dec(x_91);
x_99 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_99, 0, x_24);
lean_ctor_set_uint8(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_100);
x_83 = x_101;
goto block_89;
}
}
}
else
{
lean_dec_ref(x_91);
lean_dec(x_90);
x_83 = x_93;
goto block_89;
}
}
}
block_17:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_11, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_11, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_nat_dec_lt(x_8, x_5);
if (x_9 == 0)
{
lean_free_object(x_3);
lean_dec(x_8);
lean_free_object(x_1);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_8, x_10);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_array_push(x_2, x_8);
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_nat_dec_lt(x_14, x_5);
if (x_15 == 0)
{
lean_dec(x_14);
lean_free_object(x_1);
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_14, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_1, 0, x_18);
x_19 = lean_array_push(x_2, x_14);
x_2 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_23 = x_3;
} else {
 lean_dec_ref(x_3);
 x_23 = lean_box(0);
}
x_24 = lean_nat_dec_lt(x_22, x_21);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_22, x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
x_29 = lean_array_push(x_2, x_22);
x_1 = x_28;
x_2 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_8, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_box(0);
x_23 = lean_array_uget(x_6, x_8);
x_24 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_84; lean_object* x_91; lean_object* x_104; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_104 = l_Lean_Environment_getModuleIdx_x3f(x_25, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_106 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_105);
x_91 = x_106;
goto block_103;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec_ref(x_104);
x_91 = x_107;
goto block_103;
}
block_65:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_31, x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_27, x_34);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec_ref(x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1));
x_43 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_40);
x_44 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_43, x_2);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2));
x_47 = lean_string_append(x_45, x_46);
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_41);
x_49 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_48, x_2);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
x_52 = lean_string_append(x_50, x_51);
x_53 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_54; 
lean_dec_ref(x_10);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_28);
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_58 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_59; 
lean_dec_ref(x_10);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_28);
lean_dec_ref(x_10);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
block_76:
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_71 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_72 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_73 = lean_string_append(x_71, x_72);
if (x_70 == 0)
{
lean_object* x_74; 
x_74 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_27 = x_66;
x_28 = x_67;
x_29 = x_73;
x_30 = x_74;
goto block_65;
}
else
{
lean_object* x_75; 
x_75 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_27 = x_66;
x_28 = x_67;
x_29 = x_73;
x_30 = x_75;
goto block_65;
}
}
block_83:
{
uint8_t x_80; 
x_80 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_66 = x_77;
x_67 = x_78;
x_68 = x_79;
x_69 = x_81;
goto block_76;
}
else
{
lean_object* x_82; 
x_82 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_66 = x_77;
x_67 = x_78;
x_68 = x_79;
x_69 = x_82;
goto block_76;
}
}
block_90:
{
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_87 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_86 == 0)
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_77 = x_87;
x_78 = x_85;
x_79 = x_88;
goto block_83;
}
else
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_77 = x_87;
x_78 = x_85;
x_79 = x_89;
goto block_83;
}
}
else
{
lean_dec(x_84);
lean_dec(x_23);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_103:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
lean_inc_ref(x_92);
lean_inc(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
if (x_95 == 0)
{
lean_dec_ref(x_92);
lean_dec(x_91);
x_84 = x_94;
goto block_90;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_ctor_set_uint8(x_92, 0, x_24);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_92);
x_98 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_97);
x_84 = x_98;
goto block_90;
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get_uint8(x_92, 1);
lean_dec(x_92);
x_100 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_100, 0, x_24);
lean_ctor_set_uint8(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_101);
x_84 = x_102;
goto block_90;
}
}
}
else
{
lean_dec_ref(x_92);
lean_dec(x_91);
x_84 = x_94;
goto block_90;
}
}
}
else
{
lean_dec(x_23);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_8, x_15);
x_8 = x_16;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_8, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_box(0);
x_23 = lean_array_uget(x_6, x_8);
x_24 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_84; lean_object* x_91; lean_object* x_104; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_104 = l_Lean_Environment_getModuleIdx_x3f(x_25, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_106 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_105);
x_91 = x_106;
goto block_103;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec_ref(x_104);
x_91 = x_107;
goto block_103;
}
block_65:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_31, x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_27, x_34);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec_ref(x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__1));
x_43 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_40);
x_44 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_43, x_2);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__2));
x_47 = lean_string_append(x_45, x_46);
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0(x_41);
x_49 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_48, x_2);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
x_52 = lean_string_append(x_50, x_51);
x_53 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_54; 
lean_dec_ref(x_10);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_28);
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_58 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_59; 
lean_dec_ref(x_10);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_28);
lean_dec_ref(x_10);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
block_76:
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_71 = lean_string_append(x_66, x_69);
lean_dec_ref(x_69);
x_72 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_73 = lean_string_append(x_71, x_72);
if (x_70 == 0)
{
lean_object* x_74; 
x_74 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_27 = x_67;
x_28 = x_68;
x_29 = x_73;
x_30 = x_74;
goto block_65;
}
else
{
lean_object* x_75; 
x_75 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_27 = x_67;
x_28 = x_68;
x_29 = x_73;
x_30 = x_75;
goto block_65;
}
}
block_83:
{
uint8_t x_80; 
x_80 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_66 = x_79;
x_67 = x_77;
x_68 = x_78;
x_69 = x_81;
goto block_76;
}
else
{
lean_object* x_82; 
x_82 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_66 = x_79;
x_67 = x_77;
x_68 = x_78;
x_69 = x_82;
goto block_76;
}
}
block_90:
{
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_87 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_86 == 0)
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_77 = x_87;
x_78 = x_85;
x_79 = x_88;
goto block_83;
}
else
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_77 = x_87;
x_78 = x_85;
x_79 = x_89;
goto block_83;
}
}
else
{
lean_dec(x_84);
lean_dec(x_23);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_103:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
lean_inc_ref(x_92);
lean_inc(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
if (x_95 == 0)
{
lean_dec_ref(x_92);
lean_dec(x_91);
x_84 = x_94;
goto block_90;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_ctor_set_uint8(x_92, 0, x_24);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_92);
x_98 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_97);
x_84 = x_98;
goto block_90;
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get_uint8(x_92, 1);
lean_dec(x_92);
x_100 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_100, 0, x_24);
lean_ctor_set_uint8(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_101);
x_84 = x_102;
goto block_90;
}
}
}
else
{
lean_dec_ref(x_92);
lean_dec(x_91);
x_84 = x_94;
goto block_90;
}
}
}
else
{
lean_dec(x_23);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_18:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_8, x_15);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_12, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
x_8 = l_Lean_instBEqImport_beq(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2_spec__4(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___00Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2_spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Array_eraseIdx___redArg(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_23 = x_8;
} else {
 lean_dec_ref(x_8);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
x_27 = lean_array_uget(x_5, x_7);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_22, x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_23;
}
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
x_11 = x_30;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_81; uint8_t x_87; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 7);
x_33 = lean_ctor_get_uint8(x_27, 0);
x_34 = lean_ctor_get_uint8(x_27, 1);
x_35 = lean_box(0);
x_36 = 0;
x_37 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_38 = lean_array_get_borrowed(x_35, x_32, x_1);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*1 + 2, x_34);
x_87 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_25, x_39);
if (x_87 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
goto block_80;
}
else
{
uint8_t x_88; 
x_88 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_24, x_27, x_1);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_89, 0, x_4);
lean_ctor_set_uint8(x_89, 1, x_34);
x_90 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_24, x_89, x_1);
lean_dec_ref(x_89);
x_81 = x_90;
goto block_86;
}
else
{
x_81 = x_88;
goto block_86;
}
}
block_52:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2(x_41, x_39);
lean_dec_ref(x_39);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_shiftl(x_46, x_1);
x_48 = lean_nat_lor(x_45, x_47);
lean_dec(x_47);
x_49 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(x_40, x_27, x_48);
lean_dec(x_27);
if (lean_is_scalar(x_26)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_26;
}
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_44);
if (lean_is_scalar(x_23)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_23;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_11 = x_51;
x_12 = x_42;
x_13 = lean_box(0);
goto block_17;
}
block_69:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_string_append(x_53, x_56);
lean_dec_ref(x_56);
x_58 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_59 = lean_string_append(x_57, x_58);
lean_inc(x_38);
x_60 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_38, x_54);
x_61 = lean_string_append(x_59, x_60);
lean_dec_ref(x_60);
x_62 = lean_string_append(x_55, x_61);
lean_dec_ref(x_61);
x_63 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__0));
x_64 = lean_string_append(x_62, x_63);
x_65 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
x_40 = x_22;
x_41 = x_25;
x_42 = x_9;
x_43 = lean_box(0);
goto block_52;
}
else
{
uint8_t x_66; 
lean_dec_ref(x_39);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
block_75:
{
if (x_34 == 0)
{
lean_object* x_73; 
x_73 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_53 = x_72;
x_54 = x_70;
x_55 = x_71;
x_56 = x_73;
goto block_69;
}
else
{
lean_object* x_74; 
x_74 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_53 = x_72;
x_54 = x_70;
x_55 = x_71;
x_56 = x_74;
goto block_69;
}
}
block_80:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_array_get_borrowed(x_37, x_31, x_1);
x_77 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_24, x_39, x_1, x_76);
lean_dec_ref(x_39);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_25);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_22);
lean_ctor_set(x_79, 1, x_78);
x_11 = x_79;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
block_86:
{
if (x_81 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
goto block_80;
}
else
{
uint8_t x_82; 
x_82 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 7);
if (x_82 == 0)
{
x_40 = x_22;
x_41 = x_25;
x_42 = x_9;
x_43 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_83; 
x_83 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__1));
if (x_33 == 0)
{
lean_object* x_84; 
x_84 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_70 = x_82;
x_71 = x_83;
x_72 = x_84;
goto block_75;
}
else
{
lean_object* x_85; 
x_85 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_70 = x_82;
x_71 = x_83;
x_72 = x_85;
goto block_75;
}
}
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_11;
x_9 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(x_1, x_2, x_3, x_11, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_4, x_6);
x_17 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_18 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(x_16, x_1, x_2, x_3, x_17, x_18, x_19, x_7, x_8);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_22;
x_8 = x_23;
goto _start;
}
else
{
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_array_uget(x_4, x_6);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_7, 1, x_31);
x_32 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(x_29, x_1, x_2, x_3, x_30, x_32, x_33, x_7, x_8);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 1;
x_39 = lean_usize_add(x_6, x_38);
x_6 = x_39;
x_7 = x_36;
x_8 = x_37;
goto _start;
}
else
{
return x_34;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_array_uget(x_4, x_6);
x_47 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(x_46, x_1, x_2, x_3, x_47, x_50, x_51, x_49, x_8);
lean_dec(x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = 1;
x_57 = lean_usize_add(x_6, x_56);
x_6 = x_57;
x_7 = x_54;
x_8 = x_55;
goto _start;
}
else
{
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_1, x_2, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4;
x_3 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5;
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__6));
x_2 = x_8;
goto block_5;
}
block_5:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(x_1, x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_shiftl(x_14, x_1);
x_16 = lean_nat_lor(x_13, x_15);
lean_dec(x_15);
lean_inc_ref(x_2);
x_17 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(x_2, x_12, x_16);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_get(x_17, x_12);
lean_dec_ref(x_17);
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(x_6, x_12, x_18);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_6, x_19, x_1);
if (x_20 == 0)
{
lean_dec(x_19);
x_9 = x_6;
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_19, 0);
x_22 = lean_ctor_get_uint8(x_19, 1);
lean_dec(x_19);
x_23 = 0;
x_24 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_25 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_22);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_25, x_27, x_1, x_2);
lean_dec_ref(x_27);
x_29 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_30 = 0;
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__6(x_1, x_28, x_24, x_29, x_30, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_9 = x_33;
x_10 = x_34;
x_11 = lean_box(0);
goto block_15;
}
else
{
return x_31;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_lt(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_14 = lean_array_get_borrowed(x_13, x_12, x_4);
x_15 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all;
x_16 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0;
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__7(x_4, x_14, x_15, x_16, x_17, x_3, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_22;
x_5 = x_21;
goto _start;
}
else
{
lean_dec(x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_172; lean_object* x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; size_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_198; lean_object* x_199; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; size_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; size_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_265; lean_object* x_266; lean_object* x_267; size_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; size_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; size_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; size_t x_298; uint8_t x_299; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; size_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; size_t x_333; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; size_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; size_t x_347; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; size_t x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; size_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; size_t x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; size_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; size_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; uint8_t x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; size_t x_663; lean_object* x_664; lean_object* x_665; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; uint8_t x_675; lean_object* x_676; lean_object* x_677; size_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_690; lean_object* x_691; uint8_t x_692; uint8_t x_693; lean_object* x_694; lean_object* x_695; size_t x_696; lean_object* x_697; uint8_t x_698; lean_object* x_728; lean_object* x_729; uint8_t x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; size_t x_734; lean_object* x_735; lean_object* x_736; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; lean_object* x_761; lean_object* x_762; size_t x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_778; lean_object* x_779; uint8_t x_848; 
x_204 = lean_ctor_get(x_8, 0);
x_205 = lean_ctor_get(x_8, 1);
x_206 = lean_ctor_get(x_8, 2);
x_207 = lean_ctor_get(x_8, 3);
x_208 = lean_ctor_get(x_8, 4);
x_209 = lean_ctor_get(x_8, 5);
x_210 = lean_ctor_get(x_8, 6);
x_211 = lean_ctor_get(x_8, 7);
x_212 = lean_box(0);
x_372 = l_Lean_instInhabitedModuleData_default;
x_373 = lean_array_get(x_212, x_211, x_3);
x_848 = l_Lean_isExtraRevModUse(x_204, x_3);
if (x_848 == 0)
{
x_778 = x_8;
x_779 = lean_box(0);
goto block_847;
}
else
{
lean_object* x_849; uint8_t x_850; uint8_t x_851; lean_object* x_852; 
lean_inc_ref(x_211);
lean_inc_ref(x_210);
lean_inc_ref(x_209);
lean_inc_ref(x_208);
lean_inc_ref(x_207);
lean_inc_ref(x_206);
lean_inc_ref(x_205);
lean_inc_ref(x_204);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 lean_ctor_release(x_8, 7);
 x_849 = x_8;
} else {
 lean_dec_ref(x_8);
 x_849 = lean_box(0);
}
x_850 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_851 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 7);
if (x_850 == 0)
{
lean_object* x_869; 
x_869 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_869, 0, x_850);
lean_ctor_set_uint8(x_869, 1, x_850);
x_852 = x_869;
goto block_868;
}
else
{
uint8_t x_870; lean_object* x_871; 
x_870 = 0;
x_871 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_871, 0, x_848);
lean_ctor_set_uint8(x_871, 1, x_870);
x_852 = x_871;
goto block_868;
}
block_868:
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_853 = lean_unsigned_to_nat(0u);
x_854 = lean_unsigned_to_nat(1u);
x_855 = lean_nat_shiftl(x_854, x_3);
x_856 = lean_nat_lor(x_853, x_855);
lean_dec(x_855);
x_857 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_207, x_852, x_856);
lean_dec_ref(x_852);
if (lean_is_scalar(x_849)) {
 x_858 = lean_alloc_ctor(0, 8, 0);
} else {
 x_858 = x_849;
}
lean_ctor_set(x_858, 0, x_204);
lean_ctor_set(x_858, 1, x_205);
lean_ctor_set(x_858, 2, x_206);
lean_ctor_set(x_858, 3, x_857);
lean_ctor_set(x_858, 4, x_208);
lean_ctor_set(x_858, 5, x_209);
lean_ctor_set(x_858, 6, x_210);
lean_ctor_set(x_858, 7, x_211);
if (x_851 == 0)
{
x_778 = x_858;
x_779 = lean_box(0);
goto block_847;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_859 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__5));
lean_inc(x_373);
x_860 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_373, x_851);
x_861 = lean_string_append(x_859, x_860);
lean_dec_ref(x_860);
x_862 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__6));
x_863 = lean_string_append(x_861, x_862);
x_864 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_863);
if (lean_obj_tag(x_864) == 0)
{
lean_dec_ref(x_864);
x_778 = x_858;
x_779 = lean_box(0);
goto block_847;
}
else
{
uint8_t x_865; 
lean_dec_ref(x_858);
lean_dec(x_373);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_865 = !lean_is_exclusive(x_864);
if (x_865 == 0)
{
return x_864;
}
else
{
lean_object* x_866; lean_object* x_867; 
x_866 = lean_ctor_get(x_864, 0);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_867, 0, x_866);
return x_867;
}
}
}
}
}
block_142:
{
lean_object* x_19; 
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13(x_14, x_10, x_15, x_12, x_16, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_size(x_11);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14(x_14, x_11, x_23, x_16, x_21, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_33 = lean_array_set(x_31, x_3, x_30);
lean_ctor_set(x_28, 1, x_33);
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_34 = lean_box(0);
lean_ctor_set(x_26, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_26);
lean_free_object(x_24);
lean_inc_ref(x_14);
x_35 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(x_14, x_3);
x_36 = lean_box(0);
x_37 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_10, x_32, x_35, x_6, x_14, x_15, x_12, x_16, x_36, x_28);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_32, x_35, x_6, x_14, x_11, x_23, x_16, x_36, x_39);
lean_dec_ref(x_11);
lean_dec_ref(x_14);
lean_dec_ref(x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_36);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
return x_40;
}
}
else
{
lean_dec_ref(x_35);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_37;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_28, 0);
x_54 = lean_ctor_get(x_28, 1);
x_55 = lean_ctor_get(x_28, 2);
x_56 = lean_ctor_get(x_28, 3);
x_57 = lean_ctor_get(x_28, 4);
x_58 = lean_ctor_get(x_28, 5);
x_59 = lean_ctor_get(x_28, 6);
x_60 = lean_ctor_get(x_28, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_28);
x_61 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_62 = lean_array_set(x_54, x_3, x_52);
x_63 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_57);
lean_ctor_set(x_63, 5, x_58);
lean_ctor_set(x_63, 6, x_59);
lean_ctor_set(x_63, 7, x_60);
if (x_61 == 0)
{
lean_object* x_64; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_64 = lean_box(0);
lean_ctor_set(x_26, 1, x_63);
lean_ctor_set(x_26, 0, x_64);
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_26);
lean_free_object(x_24);
lean_inc_ref(x_14);
x_65 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(x_14, x_3);
x_66 = lean_box(0);
x_67 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_10, x_61, x_65, x_6, x_14, x_15, x_12, x_16, x_66, x_63);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_61, x_65, x_6, x_14, x_11, x_23, x_16, x_66, x_69);
lean_dec_ref(x_11);
lean_dec_ref(x_14);
lean_dec_ref(x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
return x_70;
}
}
else
{
lean_dec_ref(x_65);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_67;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_26, 1);
x_78 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
lean_inc(x_78);
lean_dec(x_26);
x_79 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_77, 5);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_77, 6);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_77, 7);
lean_inc_ref(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_89 = lean_array_set(x_80, x_3, x_78);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 8, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_81);
lean_ctor_set(x_90, 3, x_82);
lean_ctor_set(x_90, 4, x_83);
lean_ctor_set(x_90, 5, x_84);
lean_ctor_set(x_90, 6, x_85);
lean_ctor_set(x_90, 7, x_86);
if (x_88 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_24, 0, x_92);
return x_24;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_24);
lean_inc_ref(x_14);
x_93 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(x_14, x_3);
x_94 = lean_box(0);
x_95 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_10, x_88, x_93, x_6, x_14, x_15, x_12, x_16, x_94, x_90);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_88, x_93, x_6, x_14, x_11, x_23, x_16, x_94, x_97);
lean_dec_ref(x_11);
lean_dec_ref(x_14);
lean_dec_ref(x_93);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_101);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
else
{
return x_98;
}
}
else
{
lean_dec_ref(x_93);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_95;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_105 = lean_ctor_get(x_24, 0);
lean_inc(x_105);
lean_dec(x_24);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_106, 2);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_106, 4);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_106, 5);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_106, 6);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_106, 7);
lean_inc_ref(x_116);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 x_117 = x_106;
} else {
 lean_dec_ref(x_106);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_119 = lean_array_set(x_110, x_3, x_107);
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 8, 0);
} else {
 x_120 = x_117;
}
lean_ctor_set(x_120, 0, x_109);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set(x_120, 4, x_113);
lean_ctor_set(x_120, 5, x_114);
lean_ctor_set(x_120, 6, x_115);
lean_ctor_set(x_120, 7, x_116);
if (x_118 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_121 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_108;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_108);
lean_inc_ref(x_14);
x_124 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(x_14, x_3);
x_125 = lean_box(0);
x_126 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_10, x_118, x_124, x_6, x_14, x_15, x_12, x_16, x_125, x_120);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_118, x_124, x_6, x_14, x_11, x_23, x_16, x_125, x_128);
lean_dec_ref(x_11);
lean_dec_ref(x_14);
lean_dec_ref(x_124);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_132);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
return x_129;
}
}
else
{
lean_dec_ref(x_124);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_126;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_24);
if (x_136 == 0)
{
return x_24;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_24, 0);
lean_inc(x_137);
lean_dec(x_24);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_19);
if (x_139 == 0)
{
return x_19;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_19, 0);
lean_inc(x_140);
lean_dec(x_19);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
block_171:
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_151);
lean_ctor_set(x_159, 2, x_144);
lean_ctor_set(x_159, 3, x_143);
lean_ctor_set(x_159, 4, x_158);
lean_ctor_set(x_159, 5, x_147);
lean_ctor_set(x_159, 6, x_155);
lean_ctor_set(x_159, 7, x_145);
x_160 = l_Array_isEmpty___redArg(x_154);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__0));
x_162 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_154);
x_163 = lean_array_to_list(x_154);
x_164 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_163);
x_165 = lean_string_append(x_162, x_164);
lean_dec_ref(x_164);
x_166 = lean_string_append(x_161, x_165);
lean_dec_ref(x_165);
x_167 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_167);
x_10 = x_152;
x_11 = x_154;
x_12 = x_146;
x_13 = x_156;
x_14 = x_148;
x_15 = x_149;
x_16 = x_150;
x_17 = x_159;
x_18 = lean_box(0);
goto block_142;
}
else
{
uint8_t x_168; 
lean_dec_ref(x_159);
lean_dec_ref(x_156);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec(x_3);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
return x_167;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
else
{
x_10 = x_152;
x_11 = x_154;
x_12 = x_146;
x_13 = x_156;
x_14 = x_148;
x_15 = x_149;
x_16 = x_150;
x_17 = x_159;
x_18 = lean_box(0);
goto block_142;
}
}
block_197:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_182 = lean_ctor_get(x_180, 0);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_180, 2);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_180, 3);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_180, 4);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_180, 5);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_180, 6);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_180, 7);
lean_inc_ref(x_189);
x_190 = lean_array_get_size(x_173);
x_191 = lean_nat_dec_lt(x_177, x_190);
lean_dec(x_177);
if (x_191 == 0)
{
lean_dec_ref(x_180);
x_143 = x_185;
x_144 = x_184;
x_145 = x_189;
x_146 = x_174;
x_147 = x_187;
x_148 = x_176;
x_149 = x_178;
x_150 = x_179;
x_151 = x_183;
x_152 = x_172;
x_153 = lean_box(0);
x_154 = x_173;
x_155 = x_188;
x_156 = x_175;
x_157 = x_182;
x_158 = x_186;
goto block_171;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_190, x_190);
if (x_192 == 0)
{
if (x_191 == 0)
{
lean_dec_ref(x_180);
x_143 = x_185;
x_144 = x_184;
x_145 = x_189;
x_146 = x_174;
x_147 = x_187;
x_148 = x_176;
x_149 = x_178;
x_150 = x_179;
x_151 = x_183;
x_152 = x_172;
x_153 = lean_box(0);
x_154 = x_173;
x_155 = x_188;
x_156 = x_175;
x_157 = x_182;
x_158 = x_186;
goto block_171;
}
else
{
size_t x_193; lean_object* x_194; 
x_193 = lean_usize_of_nat(x_190);
x_194 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(x_180, x_3, x_173, x_179, x_193, x_186);
lean_dec_ref(x_180);
x_143 = x_185;
x_144 = x_184;
x_145 = x_189;
x_146 = x_174;
x_147 = x_187;
x_148 = x_176;
x_149 = x_178;
x_150 = x_179;
x_151 = x_183;
x_152 = x_172;
x_153 = lean_box(0);
x_154 = x_173;
x_155 = x_188;
x_156 = x_175;
x_157 = x_182;
x_158 = x_194;
goto block_171;
}
}
else
{
size_t x_195; lean_object* x_196; 
x_195 = lean_usize_of_nat(x_190);
x_196 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(x_180, x_3, x_173, x_179, x_195, x_186);
lean_dec_ref(x_180);
x_143 = x_185;
x_144 = x_184;
x_145 = x_189;
x_146 = x_174;
x_147 = x_187;
x_148 = x_176;
x_149 = x_178;
x_150 = x_179;
x_151 = x_183;
x_152 = x_172;
x_153 = lean_box(0);
x_154 = x_173;
x_155 = x_188;
x_156 = x_175;
x_157 = x_182;
x_158 = x_196;
goto block_171;
}
}
}
block_203:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
block_264:
{
uint8_t x_224; 
x_224 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
if (x_224 == 0)
{
lean_dec(x_2);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_222;
x_181 = lean_box(0);
goto block_197;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_218, 7);
x_226 = lean_array_get_borrowed(x_212, x_225, x_3);
lean_inc(x_226);
x_227 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(x_2, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; size_t x_239; lean_object* x_240; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_233);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_box(0);
x_239 = lean_array_size(x_237);
lean_inc_ref(x_222);
lean_inc(x_231);
lean_inc(x_232);
x_240 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21(x_214, x_232, x_231, x_237, x_239, x_221, x_238, x_222);
lean_dec(x_237);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = l_Array_isEmpty___redArg(x_215);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_244 = lean_ctor_get(x_232, 2);
lean_inc_ref(x_244);
lean_dec(x_232);
x_245 = l_Lean_FileMap_toPosition(x_244, x_234);
lean_dec(x_234);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_248 = lean_string_append(x_231, x_247);
x_249 = lean_nat_sub(x_246, x_213);
lean_dec(x_246);
x_250 = l_Nat_reprFast(x_249);
x_251 = lean_string_append(x_248, x_250);
lean_dec_ref(x_250);
x_252 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__2));
x_253 = lean_string_append(x_251, x_252);
x_254 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_215);
x_255 = lean_array_to_list(x_215);
x_256 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_255);
x_257 = lean_string_append(x_254, x_256);
lean_dec_ref(x_256);
x_258 = lean_string_append(x_253, x_257);
lean_dec_ref(x_257);
x_259 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__3));
x_260 = lean_string_append(x_258, x_259);
x_261 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_dec_ref(x_261);
lean_dec_ref(x_222);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_242;
x_181 = lean_box(0);
goto block_197;
}
else
{
lean_dec_ref(x_261);
lean_dec(x_242);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_222;
x_181 = lean_box(0);
goto block_197;
}
}
else
{
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_222);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_242;
x_181 = lean_box(0);
goto block_197;
}
}
else
{
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_231);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec_ref(x_222);
x_262 = lean_ctor_get(x_240, 0);
lean_inc(x_262);
lean_dec_ref(x_240);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_263;
x_181 = lean_box(0);
goto block_197;
}
else
{
lean_dec_ref(x_240);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_222;
x_181 = lean_box(0);
goto block_197;
}
}
}
else
{
lean_dec_ref(x_227);
x_172 = x_214;
x_173 = x_215;
x_174 = x_216;
x_175 = x_217;
x_176 = x_218;
x_177 = x_220;
x_178 = x_219;
x_179 = x_221;
x_180 = x_222;
x_181 = lean_box(0);
goto block_197;
}
}
}
block_287:
{
uint8_t x_276; 
x_276 = l_Array_isEmpty___redArg(x_266);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__4));
x_278 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_266);
x_279 = lean_array_to_list(x_266);
x_280 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_279);
x_281 = lean_string_append(x_278, x_280);
lean_dec_ref(x_280);
x_282 = lean_string_append(x_277, x_281);
lean_dec_ref(x_281);
x_283 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_dec_ref(x_283);
x_213 = x_265;
x_214 = x_266;
x_215 = x_267;
x_216 = x_268;
x_217 = x_269;
x_218 = x_270;
x_219 = x_272;
x_220 = x_271;
x_221 = x_273;
x_222 = x_274;
x_223 = lean_box(0);
goto block_264;
}
else
{
uint8_t x_284; 
lean_dec_ref(x_274);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_269);
lean_dec_ref(x_267);
lean_dec_ref(x_266);
lean_dec(x_3);
lean_dec(x_2);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
return x_283;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
}
else
{
x_213 = x_265;
x_214 = x_266;
x_215 = x_267;
x_216 = x_268;
x_217 = x_269;
x_218 = x_270;
x_219 = x_272;
x_220 = x_271;
x_221 = x_273;
x_222 = x_274;
x_223 = lean_box(0);
goto block_264;
}
}
block_322:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_295, 7);
x_301 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0));
x_302 = lean_array_get_borrowed(x_212, x_300, x_3);
lean_inc(x_302);
lean_inc(x_2);
x_303 = l_Lean_SearchPath_findModuleWithExt(x_2, x_301, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec_ref(x_303);
if (lean_obj_tag(x_304) == 1)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_307 = lean_string_append(x_305, x_306);
x_308 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_308);
x_265 = x_290;
x_266 = x_291;
x_267 = x_292;
x_268 = x_293;
x_269 = x_294;
x_270 = x_295;
x_271 = x_297;
x_272 = x_296;
x_273 = x_298;
x_274 = x_289;
x_275 = lean_box(0);
goto block_287;
}
else
{
uint8_t x_309; 
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_289);
lean_dec(x_3);
lean_dec(x_2);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
return x_308;
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_304);
lean_inc(x_302);
x_312 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_302, x_299);
x_313 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_314 = lean_string_append(x_312, x_313);
x_315 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_dec_ref(x_315);
x_265 = x_290;
x_266 = x_291;
x_267 = x_292;
x_268 = x_293;
x_269 = x_294;
x_270 = x_295;
x_271 = x_297;
x_272 = x_296;
x_273 = x_298;
x_274 = x_289;
x_275 = lean_box(0);
goto block_287;
}
else
{
uint8_t x_316; 
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_289);
lean_dec(x_3);
lean_dec(x_2);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
return x_315;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_289);
lean_dec(x_3);
lean_dec(x_2);
x_319 = !lean_is_exclusive(x_303);
if (x_319 == 0)
{
return x_303;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_303, 0);
lean_inc(x_320);
lean_dec(x_303);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
}
}
block_335:
{
uint8_t x_334; 
x_334 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
if (x_334 == 0)
{
x_265 = x_325;
x_266 = x_326;
x_267 = x_327;
x_268 = x_328;
x_269 = x_329;
x_270 = x_330;
x_271 = x_332;
x_272 = x_331;
x_273 = x_333;
x_274 = x_324;
x_275 = lean_box(0);
goto block_287;
}
else
{
x_288 = lean_box(0);
x_289 = x_324;
x_290 = x_325;
x_291 = x_326;
x_292 = x_327;
x_293 = x_328;
x_294 = x_329;
x_295 = x_330;
x_296 = x_331;
x_297 = x_332;
x_298 = x_333;
x_299 = x_334;
goto block_322;
}
}
block_349:
{
uint8_t x_348; 
x_348 = l_Array_isEmpty___redArg(x_339);
if (x_348 == 0)
{
if (x_342 == 0)
{
x_323 = lean_box(0);
x_324 = x_337;
x_325 = x_338;
x_326 = x_339;
x_327 = x_340;
x_328 = x_341;
x_329 = x_343;
x_330 = x_344;
x_331 = x_346;
x_332 = x_345;
x_333 = x_347;
goto block_335;
}
else
{
x_288 = lean_box(0);
x_289 = x_337;
x_290 = x_338;
x_291 = x_339;
x_292 = x_340;
x_293 = x_341;
x_294 = x_343;
x_295 = x_344;
x_296 = x_346;
x_297 = x_345;
x_298 = x_347;
x_299 = x_342;
goto block_322;
}
}
else
{
x_323 = lean_box(0);
x_324 = x_337;
x_325 = x_338;
x_326 = x_339;
x_327 = x_340;
x_328 = x_341;
x_329 = x_343;
x_330 = x_344;
x_331 = x_346;
x_332 = x_345;
x_333 = x_347;
goto block_335;
}
}
block_371:
{
lean_object* x_369; uint8_t x_370; 
x_369 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_369, 0, x_354);
lean_ctor_set(x_369, 1, x_351);
lean_ctor_set(x_369, 2, x_350);
lean_ctor_set(x_369, 3, x_358);
lean_ctor_set(x_369, 4, x_368);
lean_ctor_set(x_369, 5, x_353);
lean_ctor_set(x_369, 6, x_364);
lean_ctor_set(x_369, 7, x_362);
x_370 = l_Array_isEmpty___redArg(x_366);
if (x_370 == 0)
{
if (x_356 == 0)
{
x_336 = lean_box(0);
x_337 = x_369;
x_338 = x_363;
x_339 = x_365;
x_340 = x_366;
x_341 = x_355;
x_342 = x_356;
x_343 = x_367;
x_344 = x_357;
x_345 = x_359;
x_346 = x_360;
x_347 = x_361;
goto block_349;
}
else
{
x_288 = lean_box(0);
x_289 = x_369;
x_290 = x_363;
x_291 = x_365;
x_292 = x_366;
x_293 = x_355;
x_294 = x_367;
x_295 = x_357;
x_296 = x_360;
x_297 = x_359;
x_298 = x_361;
x_299 = x_356;
goto block_322;
}
}
else
{
x_336 = lean_box(0);
x_337 = x_369;
x_338 = x_363;
x_339 = x_365;
x_340 = x_366;
x_341 = x_355;
x_342 = x_356;
x_343 = x_367;
x_344 = x_357;
x_345 = x_359;
x_346 = x_360;
x_347 = x_361;
goto block_349;
}
}
block_412:
{
lean_object* x_389; 
x_389 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12(x_379, x_377, x_385, x_6, x_384, x_381, x_376, x_383, x_382, x_387);
lean_dec_ref(x_384);
lean_dec_ref(x_385);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 0);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get(x_391, 0);
lean_inc_ref(x_393);
x_394 = lean_ctor_get(x_391, 1);
lean_inc_ref(x_394);
x_395 = lean_ctor_get(x_391, 2);
lean_inc_ref(x_395);
x_396 = lean_ctor_get(x_391, 3);
lean_inc_ref(x_396);
x_397 = lean_ctor_get(x_391, 4);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_391, 5);
lean_inc_ref(x_398);
x_399 = lean_ctor_get(x_391, 6);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_391, 7);
lean_inc_ref(x_400);
lean_dec(x_391);
x_401 = l_Array_append___redArg(x_374, x_386);
lean_dec_ref(x_386);
x_402 = lean_array_get_size(x_392);
x_403 = lean_nat_dec_lt(x_380, x_402);
if (x_403 == 0)
{
lean_dec(x_373);
x_350 = x_395;
x_351 = x_394;
x_352 = lean_box(0);
x_353 = x_398;
x_354 = x_393;
x_355 = x_376;
x_356 = x_377;
x_357 = x_379;
x_358 = x_396;
x_359 = x_380;
x_360 = x_381;
x_361 = x_383;
x_362 = x_400;
x_363 = x_375;
x_364 = x_399;
x_365 = x_392;
x_366 = x_401;
x_367 = x_378;
x_368 = x_397;
goto block_371;
}
else
{
uint8_t x_404; 
x_404 = lean_nat_dec_le(x_402, x_402);
if (x_404 == 0)
{
if (x_403 == 0)
{
lean_dec(x_373);
x_350 = x_395;
x_351 = x_394;
x_352 = lean_box(0);
x_353 = x_398;
x_354 = x_393;
x_355 = x_376;
x_356 = x_377;
x_357 = x_379;
x_358 = x_396;
x_359 = x_380;
x_360 = x_381;
x_361 = x_383;
x_362 = x_400;
x_363 = x_375;
x_364 = x_399;
x_365 = x_392;
x_366 = x_401;
x_367 = x_378;
x_368 = x_397;
goto block_371;
}
else
{
size_t x_405; lean_object* x_406; 
x_405 = lean_usize_of_nat(x_402);
x_406 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(x_373, x_392, x_383, x_405, x_397);
x_350 = x_395;
x_351 = x_394;
x_352 = lean_box(0);
x_353 = x_398;
x_354 = x_393;
x_355 = x_376;
x_356 = x_377;
x_357 = x_379;
x_358 = x_396;
x_359 = x_380;
x_360 = x_381;
x_361 = x_383;
x_362 = x_400;
x_363 = x_375;
x_364 = x_399;
x_365 = x_392;
x_366 = x_401;
x_367 = x_378;
x_368 = x_406;
goto block_371;
}
}
else
{
size_t x_407; lean_object* x_408; 
x_407 = lean_usize_of_nat(x_402);
x_408 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(x_373, x_392, x_383, x_407, x_397);
x_350 = x_395;
x_351 = x_394;
x_352 = lean_box(0);
x_353 = x_398;
x_354 = x_393;
x_355 = x_376;
x_356 = x_377;
x_357 = x_379;
x_358 = x_396;
x_359 = x_380;
x_360 = x_381;
x_361 = x_383;
x_362 = x_400;
x_363 = x_375;
x_364 = x_399;
x_365 = x_392;
x_366 = x_401;
x_367 = x_378;
x_368 = x_408;
goto block_371;
}
}
}
else
{
uint8_t x_409; 
lean_dec_ref(x_386);
lean_dec_ref(x_381);
lean_dec(x_380);
lean_dec_ref(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_409 = !lean_is_exclusive(x_389);
if (x_409 == 0)
{
return x_389;
}
else
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_389, 0);
lean_inc(x_410);
lean_dec(x_389);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_410);
return x_411;
}
}
}
block_652:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; size_t x_430; lean_object* x_431; 
x_424 = lean_array_get(x_372, x_413, x_3);
lean_dec_ref(x_413);
x_425 = lean_ctor_get(x_424, 0);
lean_inc_ref(x_425);
lean_dec(x_424);
x_426 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_427 = lean_mk_empty_array_with_capacity(x_419);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_421);
lean_ctor_set(x_428, 1, x_426);
lean_inc_ref(x_427);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = lean_array_size(x_425);
x_431 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11(x_418, x_373, x_425, x_6, x_425, x_430, x_420, x_429, x_422);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
x_435 = !lean_is_exclusive(x_432);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = lean_ctor_get(x_432, 1);
x_437 = lean_ctor_get(x_432, 0);
lean_dec(x_437);
x_438 = !lean_is_exclusive(x_433);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_439 = lean_ctor_get(x_433, 0);
x_440 = lean_ctor_get(x_433, 1);
lean_dec(x_440);
x_441 = !lean_is_exclusive(x_434);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; size_t x_449; lean_object* x_450; 
x_442 = lean_ctor_get(x_434, 0);
x_443 = lean_ctor_get(x_434, 1);
lean_inc(x_419);
x_444 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_444, 0, x_419);
lean_ctor_set(x_432, 1, x_414);
lean_ctor_set(x_432, 0, x_444);
lean_inc_ref(x_427);
x_445 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_432, x_427);
x_446 = l_Array_reverse___redArg(x_445);
lean_inc_ref(x_427);
lean_inc(x_443);
lean_ctor_set(x_434, 1, x_427);
lean_ctor_set(x_434, 0, x_443);
x_447 = lean_box(x_417);
lean_ctor_set(x_433, 0, x_447);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_442);
lean_ctor_set(x_448, 1, x_433);
x_449 = lean_array_size(x_446);
x_450 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_418, x_425, x_6, x_3, x_4, x_446, x_449, x_420, x_448, x_436);
lean_dec_ref(x_4);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
x_454 = !lean_is_exclusive(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_455 = lean_ctor_get(x_453, 1);
x_456 = lean_ctor_get(x_453, 0);
x_457 = lean_unbox(x_456);
lean_dec(x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_free_object(x_453);
lean_dec_ref(x_446);
lean_dec(x_443);
x_458 = lean_ctor_get(x_451, 1);
lean_inc(x_458);
lean_dec(x_451);
x_459 = lean_ctor_get(x_452, 0);
lean_inc(x_459);
lean_dec(x_452);
x_460 = lean_ctor_get(x_455, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_455, 1);
lean_inc(x_461);
lean_dec(x_455);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_459;
x_385 = x_460;
x_386 = x_461;
x_387 = x_458;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_462 = lean_ctor_get(x_451, 1);
lean_inc(x_462);
lean_dec(x_451);
x_463 = lean_ctor_get(x_452, 0);
lean_inc(x_463);
lean_dec(x_452);
x_464 = !lean_is_exclusive(x_455);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_455, 0);
lean_dec(x_465);
lean_ctor_set(x_455, 0, x_443);
lean_ctor_set(x_453, 0, x_463);
x_466 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_446, x_449, x_420, x_453, x_462);
lean_dec_ref(x_446);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
lean_dec_ref(x_466);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = lean_ctor_get(x_468, 0);
lean_inc(x_471);
lean_dec(x_468);
x_472 = lean_ctor_get(x_469, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_469, 1);
lean_inc(x_473);
lean_dec(x_469);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_471;
x_385 = x_472;
x_386 = x_473;
x_387 = x_470;
x_388 = lean_box(0);
goto block_412;
}
else
{
uint8_t x_474; 
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_474 = !lean_is_exclusive(x_466);
if (x_474 == 0)
{
return x_466;
}
else
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_466, 0);
lean_inc(x_475);
lean_dec(x_466);
x_476 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_476, 0, x_475);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_455, 1);
lean_inc(x_477);
lean_dec(x_455);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_443);
lean_ctor_set(x_478, 1, x_477);
lean_ctor_set(x_453, 1, x_478);
lean_ctor_set(x_453, 0, x_463);
x_479 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_446, x_449, x_420, x_453, x_462);
lean_dec_ref(x_446);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
lean_dec_ref(x_479);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_dec(x_480);
x_484 = lean_ctor_get(x_481, 0);
lean_inc(x_484);
lean_dec(x_481);
x_485 = lean_ctor_get(x_482, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_482, 1);
lean_inc(x_486);
lean_dec(x_482);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_484;
x_385 = x_485;
x_386 = x_486;
x_387 = x_483;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_487 = lean_ctor_get(x_479, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 x_488 = x_479;
} else {
 lean_dec_ref(x_479);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 1, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_487);
return x_489;
}
}
}
}
else
{
lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_490 = lean_ctor_get(x_453, 1);
x_491 = lean_ctor_get(x_453, 0);
lean_inc(x_490);
lean_inc(x_491);
lean_dec(x_453);
x_492 = lean_unbox(x_491);
lean_dec(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec_ref(x_446);
lean_dec(x_443);
x_493 = lean_ctor_get(x_451, 1);
lean_inc(x_493);
lean_dec(x_451);
x_494 = lean_ctor_get(x_452, 0);
lean_inc(x_494);
lean_dec(x_452);
x_495 = lean_ctor_get(x_490, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_490, 1);
lean_inc(x_496);
lean_dec(x_490);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_494;
x_385 = x_495;
x_386 = x_496;
x_387 = x_493;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_451, 1);
lean_inc(x_497);
lean_dec(x_451);
x_498 = lean_ctor_get(x_452, 0);
lean_inc(x_498);
lean_dec(x_452);
x_499 = lean_ctor_get(x_490, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_500 = x_490;
} else {
 lean_dec_ref(x_490);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_443);
lean_ctor_set(x_501, 1, x_499);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_501);
x_503 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_446, x_449, x_420, x_502, x_497);
lean_dec_ref(x_446);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
lean_dec_ref(x_503);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_507);
lean_dec(x_504);
x_508 = lean_ctor_get(x_505, 0);
lean_inc(x_508);
lean_dec(x_505);
x_509 = lean_ctor_get(x_506, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_506, 1);
lean_inc(x_510);
lean_dec(x_506);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_508;
x_385 = x_509;
x_386 = x_510;
x_387 = x_507;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_511 = lean_ctor_get(x_503, 0);
lean_inc(x_511);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 x_512 = x_503;
} else {
 lean_dec_ref(x_503);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 1, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_511);
return x_513;
}
}
}
}
else
{
uint8_t x_514; 
lean_dec_ref(x_446);
lean_dec(x_443);
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_514 = !lean_is_exclusive(x_450);
if (x_514 == 0)
{
return x_450;
}
else
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_450, 0);
lean_inc(x_515);
lean_dec(x_450);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; size_t x_525; lean_object* x_526; 
x_517 = lean_ctor_get(x_434, 0);
x_518 = lean_ctor_get(x_434, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_434);
lean_inc(x_419);
x_519 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_519, 0, x_419);
lean_ctor_set(x_432, 1, x_414);
lean_ctor_set(x_432, 0, x_519);
lean_inc_ref(x_427);
x_520 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_432, x_427);
x_521 = l_Array_reverse___redArg(x_520);
lean_inc_ref(x_427);
lean_inc(x_518);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_518);
lean_ctor_set(x_522, 1, x_427);
x_523 = lean_box(x_417);
lean_ctor_set(x_433, 1, x_522);
lean_ctor_set(x_433, 0, x_523);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_517);
lean_ctor_set(x_524, 1, x_433);
x_525 = lean_array_size(x_521);
x_526 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_418, x_425, x_6, x_3, x_4, x_521, x_525, x_420, x_524, x_436);
lean_dec_ref(x_4);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
lean_dec_ref(x_526);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_532 = x_529;
} else {
 lean_dec_ref(x_529);
 x_532 = lean_box(0);
}
x_533 = lean_unbox(x_531);
lean_dec(x_531);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_532);
lean_dec_ref(x_521);
lean_dec(x_518);
x_534 = lean_ctor_get(x_527, 1);
lean_inc(x_534);
lean_dec(x_527);
x_535 = lean_ctor_get(x_528, 0);
lean_inc(x_535);
lean_dec(x_528);
x_536 = lean_ctor_get(x_530, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_530, 1);
lean_inc(x_537);
lean_dec(x_530);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_535;
x_385 = x_536;
x_386 = x_537;
x_387 = x_534;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_538 = lean_ctor_get(x_527, 1);
lean_inc(x_538);
lean_dec(x_527);
x_539 = lean_ctor_get(x_528, 0);
lean_inc(x_539);
lean_dec(x_528);
x_540 = lean_ctor_get(x_530, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_541 = x_530;
} else {
 lean_dec_ref(x_530);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_518);
lean_ctor_set(x_542, 1, x_540);
if (lean_is_scalar(x_532)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_532;
}
lean_ctor_set(x_543, 0, x_539);
lean_ctor_set(x_543, 1, x_542);
x_544 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_521, x_525, x_420, x_543, x_538);
lean_dec_ref(x_521);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
lean_dec_ref(x_544);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
x_548 = lean_ctor_get(x_545, 1);
lean_inc(x_548);
lean_dec(x_545);
x_549 = lean_ctor_get(x_546, 0);
lean_inc(x_549);
lean_dec(x_546);
x_550 = lean_ctor_get(x_547, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_547, 1);
lean_inc(x_551);
lean_dec(x_547);
x_374 = x_439;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_549;
x_385 = x_550;
x_386 = x_551;
x_387 = x_548;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_552 = lean_ctor_get(x_544, 0);
lean_inc(x_552);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 x_553 = x_544;
} else {
 lean_dec_ref(x_544);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 1, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_552);
return x_554;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec_ref(x_521);
lean_dec(x_518);
lean_dec(x_439);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_555 = lean_ctor_get(x_526, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 x_556 = x_526;
} else {
 lean_dec_ref(x_526);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 1, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_555);
return x_557;
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; size_t x_569; lean_object* x_570; 
x_558 = lean_ctor_get(x_433, 0);
lean_inc(x_558);
lean_dec(x_433);
x_559 = lean_ctor_get(x_434, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_434, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_561 = x_434;
} else {
 lean_dec_ref(x_434);
 x_561 = lean_box(0);
}
lean_inc(x_419);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_419);
lean_ctor_set(x_432, 1, x_414);
lean_ctor_set(x_432, 0, x_562);
lean_inc_ref(x_427);
x_563 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_432, x_427);
x_564 = l_Array_reverse___redArg(x_563);
lean_inc_ref(x_427);
lean_inc(x_560);
if (lean_is_scalar(x_561)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_561;
}
lean_ctor_set(x_565, 0, x_560);
lean_ctor_set(x_565, 1, x_427);
x_566 = lean_box(x_417);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_565);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_559);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_array_size(x_564);
x_570 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_418, x_425, x_6, x_3, x_4, x_564, x_569, x_420, x_568, x_436);
lean_dec_ref(x_4);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
lean_dec_ref(x_570);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_576 = x_573;
} else {
 lean_dec_ref(x_573);
 x_576 = lean_box(0);
}
x_577 = lean_unbox(x_575);
lean_dec(x_575);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_576);
lean_dec_ref(x_564);
lean_dec(x_560);
x_578 = lean_ctor_get(x_571, 1);
lean_inc(x_578);
lean_dec(x_571);
x_579 = lean_ctor_get(x_572, 0);
lean_inc(x_579);
lean_dec(x_572);
x_580 = lean_ctor_get(x_574, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_574, 1);
lean_inc(x_581);
lean_dec(x_574);
x_374 = x_558;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_579;
x_385 = x_580;
x_386 = x_581;
x_387 = x_578;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_582 = lean_ctor_get(x_571, 1);
lean_inc(x_582);
lean_dec(x_571);
x_583 = lean_ctor_get(x_572, 0);
lean_inc(x_583);
lean_dec(x_572);
x_584 = lean_ctor_get(x_574, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_585 = x_574;
} else {
 lean_dec_ref(x_574);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_560);
lean_ctor_set(x_586, 1, x_584);
if (lean_is_scalar(x_576)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_576;
}
lean_ctor_set(x_587, 0, x_583);
lean_ctor_set(x_587, 1, x_586);
x_588 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_564, x_569, x_420, x_587, x_582);
lean_dec_ref(x_564);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
lean_dec_ref(x_588);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_589, 1);
lean_inc(x_592);
lean_dec(x_589);
x_593 = lean_ctor_get(x_590, 0);
lean_inc(x_593);
lean_dec(x_590);
x_594 = lean_ctor_get(x_591, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_591, 1);
lean_inc(x_595);
lean_dec(x_591);
x_374 = x_558;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_593;
x_385 = x_594;
x_386 = x_595;
x_387 = x_592;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_558);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_596 = lean_ctor_get(x_588, 0);
lean_inc(x_596);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_597 = x_588;
} else {
 lean_dec_ref(x_588);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 1, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_596);
return x_598;
}
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec_ref(x_564);
lean_dec(x_560);
lean_dec(x_558);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_599 = lean_ctor_get(x_570, 0);
lean_inc(x_599);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 x_600 = x_570;
} else {
 lean_dec_ref(x_570);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 1, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_599);
return x_601;
}
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; size_t x_616; lean_object* x_617; 
x_602 = lean_ctor_get(x_432, 1);
lean_inc(x_602);
lean_dec(x_432);
x_603 = lean_ctor_get(x_433, 0);
lean_inc(x_603);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_604 = x_433;
} else {
 lean_dec_ref(x_433);
 x_604 = lean_box(0);
}
x_605 = lean_ctor_get(x_434, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_434, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_607 = x_434;
} else {
 lean_dec_ref(x_434);
 x_607 = lean_box(0);
}
lean_inc(x_419);
x_608 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_608, 0, x_419);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_414);
lean_inc_ref(x_427);
x_610 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_609, x_427);
x_611 = l_Array_reverse___redArg(x_610);
lean_inc_ref(x_427);
lean_inc(x_606);
if (lean_is_scalar(x_607)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_607;
}
lean_ctor_set(x_612, 0, x_606);
lean_ctor_set(x_612, 1, x_427);
x_613 = lean_box(x_417);
if (lean_is_scalar(x_604)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_604;
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_605);
lean_ctor_set(x_615, 1, x_614);
x_616 = lean_array_size(x_611);
x_617 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_418, x_425, x_6, x_3, x_4, x_611, x_616, x_420, x_615, x_602);
lean_dec_ref(x_4);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
lean_dec_ref(x_617);
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
x_621 = lean_ctor_get(x_620, 1);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
x_624 = lean_unbox(x_622);
lean_dec(x_622);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_623);
lean_dec_ref(x_611);
lean_dec(x_606);
x_625 = lean_ctor_get(x_618, 1);
lean_inc(x_625);
lean_dec(x_618);
x_626 = lean_ctor_get(x_619, 0);
lean_inc(x_626);
lean_dec(x_619);
x_627 = lean_ctor_get(x_621, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_621, 1);
lean_inc(x_628);
lean_dec(x_621);
x_374 = x_603;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_626;
x_385 = x_627;
x_386 = x_628;
x_387 = x_625;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_629 = lean_ctor_get(x_618, 1);
lean_inc(x_629);
lean_dec(x_618);
x_630 = lean_ctor_get(x_619, 0);
lean_inc(x_630);
lean_dec(x_619);
x_631 = lean_ctor_get(x_621, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_632 = x_621;
} else {
 lean_dec_ref(x_621);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_606);
lean_ctor_set(x_633, 1, x_631);
if (lean_is_scalar(x_623)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_623;
}
lean_ctor_set(x_634, 0, x_630);
lean_ctor_set(x_634, 1, x_633);
x_635 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_418, x_6, x_416, x_611, x_616, x_420, x_634, x_629);
lean_dec_ref(x_611);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
lean_dec_ref(x_635);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec(x_636);
x_640 = lean_ctor_get(x_637, 0);
lean_inc(x_640);
lean_dec(x_637);
x_641 = lean_ctor_get(x_638, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_638, 1);
lean_inc(x_642);
lean_dec(x_638);
x_374 = x_603;
x_375 = x_415;
x_376 = x_430;
x_377 = x_416;
x_378 = x_426;
x_379 = x_418;
x_380 = x_419;
x_381 = x_425;
x_382 = x_427;
x_383 = x_420;
x_384 = x_640;
x_385 = x_641;
x_386 = x_642;
x_387 = x_639;
x_388 = lean_box(0);
goto block_412;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_603);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_643 = lean_ctor_get(x_635, 0);
lean_inc(x_643);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 x_644 = x_635;
} else {
 lean_dec_ref(x_635);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 1, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_643);
return x_645;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec_ref(x_611);
lean_dec(x_606);
lean_dec(x_603);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_373);
lean_dec(x_3);
lean_dec(x_2);
x_646 = lean_ctor_get(x_617, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 x_647 = x_617;
} else {
 lean_dec_ref(x_617);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 1, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_646);
return x_648;
}
}
}
else
{
uint8_t x_649; 
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_414);
lean_dec(x_373);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_649 = !lean_is_exclusive(x_431);
if (x_649 == 0)
{
return x_431;
}
else
{
lean_object* x_650; lean_object* x_651; 
x_650 = lean_ctor_get(x_431, 0);
lean_inc(x_650);
lean_dec(x_431);
x_651 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_651, 0, x_650);
return x_651;
}
}
}
block_669:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_nat_shiftl(x_656, x_665);
lean_dec(x_665);
x_667 = lean_nat_lor(x_662, x_666);
lean_dec(x_666);
x_668 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_657, x_664, x_667);
lean_dec_ref(x_664);
x_413 = x_653;
x_414 = x_654;
x_415 = x_656;
x_416 = x_658;
x_417 = x_659;
x_418 = x_661;
x_419 = x_662;
x_420 = x_663;
x_421 = x_668;
x_422 = x_660;
x_423 = lean_box(0);
goto block_652;
}
block_689:
{
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_682 = lean_ctor_get(x_676, 0);
x_683 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_683, 0, x_674);
lean_ctor_set_uint8(x_683, 1, x_675);
x_684 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3));
x_685 = l_Lean_Environment_getModuleIdx_x3f(x_682, x_684);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; 
x_686 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_687 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_686);
x_653 = x_671;
x_654 = x_672;
x_655 = lean_box(0);
x_656 = x_673;
x_657 = x_679;
x_658 = x_674;
x_659 = x_675;
x_660 = x_680;
x_661 = x_676;
x_662 = x_677;
x_663 = x_678;
x_664 = x_683;
x_665 = x_687;
goto block_669;
}
else
{
lean_object* x_688; 
x_688 = lean_ctor_get(x_685, 0);
lean_inc(x_688);
lean_dec_ref(x_685);
x_653 = x_671;
x_654 = x_672;
x_655 = lean_box(0);
x_656 = x_673;
x_657 = x_679;
x_658 = x_674;
x_659 = x_675;
x_660 = x_680;
x_661 = x_676;
x_662 = x_677;
x_663 = x_678;
x_664 = x_683;
x_665 = x_688;
goto block_669;
}
}
else
{
lean_dec_ref(x_670);
x_413 = x_671;
x_414 = x_672;
x_415 = x_673;
x_416 = x_674;
x_417 = x_675;
x_418 = x_676;
x_419 = x_677;
x_420 = x_678;
x_421 = x_679;
x_422 = x_680;
x_423 = lean_box(0);
goto block_652;
}
}
block_727:
{
size_t x_699; lean_object* x_700; 
x_699 = lean_array_size(x_697);
lean_inc_ref(x_4);
lean_inc_ref(x_694);
x_700 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9(x_6, x_698, x_373, x_694, x_697, x_699, x_696, x_4, x_694);
lean_dec_ref(x_697);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
lean_dec_ref(x_700);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
x_704 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_694);
x_705 = lean_array_get_size(x_704);
x_706 = lean_unsigned_to_nat(1u);
lean_inc(x_695);
x_707 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_707, 0, x_695);
lean_ctor_set(x_707, 1, x_705);
lean_ctor_set(x_707, 2, x_706);
lean_inc(x_695);
x_708 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(x_6, x_694, x_3, x_707, x_702, x_695, x_703);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec_ref(x_708);
if (x_698 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
lean_inc(x_695);
x_712 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(x_694, x_707, x_710, x_695, x_711);
lean_dec_ref(x_707);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
lean_dec_ref(x_712);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_670 = x_690;
x_671 = x_704;
x_672 = x_705;
x_673 = x_706;
x_674 = x_692;
x_675 = x_693;
x_676 = x_694;
x_677 = x_695;
x_678 = x_696;
x_679 = x_714;
x_680 = x_715;
x_681 = lean_box(0);
goto block_689;
}
else
{
uint8_t x_716; 
lean_dec_ref(x_704);
lean_dec(x_695);
lean_dec_ref(x_694);
lean_dec(x_690);
lean_dec(x_373);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_716 = !lean_is_exclusive(x_712);
if (x_716 == 0)
{
return x_712;
}
else
{
lean_object* x_717; lean_object* x_718; 
x_717 = lean_ctor_get(x_712, 0);
lean_inc(x_717);
lean_dec(x_712);
x_718 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_718, 0, x_717);
return x_718;
}
}
}
else
{
lean_object* x_719; lean_object* x_720; 
lean_dec_ref(x_707);
x_719 = lean_ctor_get(x_709, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_709, 1);
lean_inc(x_720);
lean_dec(x_709);
x_670 = x_690;
x_671 = x_704;
x_672 = x_705;
x_673 = x_706;
x_674 = x_692;
x_675 = x_693;
x_676 = x_694;
x_677 = x_695;
x_678 = x_696;
x_679 = x_719;
x_680 = x_720;
x_681 = lean_box(0);
goto block_689;
}
}
else
{
uint8_t x_721; 
lean_dec_ref(x_707);
lean_dec_ref(x_704);
lean_dec(x_695);
lean_dec_ref(x_694);
lean_dec(x_690);
lean_dec(x_373);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_721 = !lean_is_exclusive(x_708);
if (x_721 == 0)
{
return x_708;
}
else
{
lean_object* x_722; lean_object* x_723; 
x_722 = lean_ctor_get(x_708, 0);
lean_inc(x_722);
lean_dec(x_708);
x_723 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_723, 0, x_722);
return x_723;
}
}
}
else
{
uint8_t x_724; 
lean_dec(x_695);
lean_dec_ref(x_694);
lean_dec(x_690);
lean_dec(x_373);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_724 = !lean_is_exclusive(x_700);
if (x_724 == 0)
{
return x_700;
}
else
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_700, 0);
lean_inc(x_725);
lean_dec(x_700);
x_726 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_726, 0, x_725);
return x_726;
}
}
}
block_754:
{
if (x_7 == 0)
{
if (lean_obj_tag(x_729) == 0)
{
x_690 = x_728;
x_691 = lean_box(0);
x_692 = x_730;
x_693 = x_731;
x_694 = x_735;
x_695 = x_732;
x_696 = x_734;
x_697 = x_733;
x_698 = x_7;
goto block_727;
}
else
{
lean_object* x_737; lean_object* x_738; 
x_737 = lean_ctor_get(x_729, 0);
lean_inc(x_737);
lean_dec_ref(x_729);
x_738 = l_Lean_Syntax_getTrailing_x3f(x_737);
lean_dec(x_737);
if (lean_obj_tag(x_738) == 0)
{
x_690 = x_728;
x_691 = lean_box(0);
x_692 = x_730;
x_693 = x_731;
x_694 = x_735;
x_695 = x_732;
x_696 = x_734;
x_697 = x_733;
x_698 = x_7;
goto block_727;
}
else
{
lean_object* x_739; uint8_t x_740; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
lean_dec_ref(x_738);
x_740 = !lean_is_exclusive(x_739);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; 
x_741 = lean_ctor_get(x_739, 0);
x_742 = lean_ctor_get(x_739, 1);
x_743 = lean_ctor_get(x_739, 2);
x_744 = lean_string_utf8_extract(x_741, x_742, x_743);
lean_dec(x_743);
lean_dec(x_742);
lean_dec_ref(x_741);
x_745 = lean_string_utf8_byte_size(x_744);
lean_inc(x_732);
lean_ctor_set(x_739, 2, x_745);
lean_ctor_set(x_739, 1, x_732);
lean_ctor_set(x_739, 0, x_744);
x_746 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(x_739);
lean_dec_ref(x_739);
x_690 = x_728;
x_691 = lean_box(0);
x_692 = x_730;
x_693 = x_731;
x_694 = x_735;
x_695 = x_732;
x_696 = x_734;
x_697 = x_733;
x_698 = x_746;
goto block_727;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
x_747 = lean_ctor_get(x_739, 0);
x_748 = lean_ctor_get(x_739, 1);
x_749 = lean_ctor_get(x_739, 2);
lean_inc(x_749);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_739);
x_750 = lean_string_utf8_extract(x_747, x_748, x_749);
lean_dec(x_749);
lean_dec(x_748);
lean_dec_ref(x_747);
x_751 = lean_string_utf8_byte_size(x_750);
lean_inc(x_732);
x_752 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_732);
lean_ctor_set(x_752, 2, x_751);
x_753 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(x_752);
lean_dec_ref(x_752);
x_690 = x_728;
x_691 = lean_box(0);
x_692 = x_730;
x_693 = x_731;
x_694 = x_735;
x_695 = x_732;
x_696 = x_734;
x_697 = x_733;
x_698 = x_753;
goto block_727;
}
}
}
}
else
{
lean_dec(x_729);
x_690 = x_728;
x_691 = lean_box(0);
x_692 = x_730;
x_693 = x_731;
x_694 = x_735;
x_695 = x_732;
x_696 = x_734;
x_697 = x_733;
x_698 = x_7;
goto block_727;
}
}
block_777:
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_772 = lean_unsigned_to_nat(1u);
x_773 = lean_nat_shiftl(x_772, x_3);
x_774 = lean_nat_lor(x_762, x_773);
lean_dec(x_773);
x_775 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_766, x_771, x_774);
lean_dec_ref(x_771);
x_776 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_776, 0, x_768);
lean_ctor_set(x_776, 1, x_758);
lean_ctor_set(x_776, 2, x_761);
lean_ctor_set(x_776, 3, x_775);
lean_ctor_set(x_776, 4, x_769);
lean_ctor_set(x_776, 5, x_755);
lean_ctor_set(x_776, 6, x_759);
lean_ctor_set(x_776, 7, x_765);
x_728 = x_756;
x_729 = x_757;
x_730 = x_760;
x_731 = x_767;
x_732 = x_762;
x_733 = x_770;
x_734 = x_763;
x_735 = x_776;
x_736 = lean_box(0);
goto block_754;
}
block_847:
{
lean_object* x_780; lean_object* x_781; uint8_t x_782; 
x_780 = lean_unsigned_to_nat(0u);
x_781 = lean_array_get_size(x_1);
x_782 = lean_nat_dec_lt(x_780, x_781);
if (x_782 == 0)
{
lean_dec(x_373);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_box(0);
x_199 = x_778;
goto block_203;
}
else
{
if (x_782 == 0)
{
lean_dec(x_373);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_box(0);
x_199 = x_778;
goto block_203;
}
else
{
size_t x_783; size_t x_784; uint8_t x_785; 
x_783 = 0;
x_784 = lean_usize_of_nat(x_781);
x_785 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(x_373, x_1, x_783, x_784);
if (x_785 == 0)
{
lean_dec(x_373);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_box(0);
x_199 = x_778;
goto block_203;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_786 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_5);
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 0);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = lean_ctor_get(x_787, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_787, 1);
lean_inc(x_790);
lean_dec(x_787);
x_791 = 0;
if (lean_obj_tag(x_788) == 0)
{
x_728 = x_789;
x_729 = x_788;
x_730 = x_785;
x_731 = x_791;
x_732 = x_780;
x_733 = x_790;
x_734 = x_783;
x_735 = x_778;
x_736 = lean_box(0);
goto block_754;
}
else
{
lean_object* x_792; lean_object* x_793; 
x_792 = lean_ctor_get(x_788, 0);
x_793 = l_Lean_Syntax_getTrailing_x3f(x_792);
if (lean_obj_tag(x_793) == 0)
{
x_728 = x_789;
x_729 = x_788;
x_730 = x_785;
x_731 = x_791;
x_732 = x_780;
x_733 = x_790;
x_734 = x_783;
x_735 = x_778;
x_736 = lean_box(0);
goto block_754;
}
else
{
lean_object* x_794; uint8_t x_795; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
lean_dec_ref(x_793);
x_795 = !lean_is_exclusive(x_794);
if (x_795 == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; 
x_796 = lean_ctor_get(x_794, 0);
x_797 = lean_ctor_get(x_794, 1);
x_798 = lean_ctor_get(x_794, 2);
x_799 = lean_string_utf8_extract(x_796, x_797, x_798);
lean_dec(x_798);
lean_dec(x_797);
lean_dec_ref(x_796);
x_800 = lean_string_utf8_byte_size(x_799);
lean_ctor_set(x_794, 2, x_800);
lean_ctor_set(x_794, 1, x_780);
lean_ctor_set(x_794, 0, x_799);
x_801 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(x_794);
lean_dec_ref(x_794);
if (x_801 == 0)
{
x_728 = x_789;
x_729 = x_788;
x_730 = x_785;
x_731 = x_791;
x_732 = x_780;
x_733 = x_790;
x_734 = x_783;
x_735 = x_778;
x_736 = lean_box(0);
goto block_754;
}
else
{
uint8_t x_802; 
x_802 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_803 = lean_ctor_get(x_778, 0);
lean_inc_ref(x_803);
x_804 = lean_ctor_get(x_778, 1);
lean_inc_ref(x_804);
x_805 = lean_ctor_get(x_778, 2);
lean_inc_ref(x_805);
x_806 = lean_ctor_get(x_778, 3);
lean_inc_ref(x_806);
x_807 = lean_ctor_get(x_778, 4);
lean_inc_ref(x_807);
x_808 = lean_ctor_get(x_778, 5);
lean_inc_ref(x_808);
x_809 = lean_ctor_get(x_778, 6);
lean_inc_ref(x_809);
x_810 = lean_ctor_get(x_778, 7);
lean_inc_ref(x_810);
lean_dec_ref(x_778);
x_811 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0));
x_755 = x_808;
x_756 = x_789;
x_757 = x_788;
x_758 = x_804;
x_759 = x_809;
x_760 = x_785;
x_761 = x_805;
x_762 = x_780;
x_763 = x_783;
x_764 = lean_box(0);
x_765 = x_810;
x_766 = x_806;
x_767 = x_791;
x_768 = x_803;
x_769 = x_807;
x_770 = x_790;
x_771 = x_811;
goto block_777;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_812 = lean_ctor_get(x_778, 0);
lean_inc_ref(x_812);
x_813 = lean_ctor_get(x_778, 1);
lean_inc_ref(x_813);
x_814 = lean_ctor_get(x_778, 2);
lean_inc_ref(x_814);
x_815 = lean_ctor_get(x_778, 3);
lean_inc_ref(x_815);
x_816 = lean_ctor_get(x_778, 4);
lean_inc_ref(x_816);
x_817 = lean_ctor_get(x_778, 5);
lean_inc_ref(x_817);
x_818 = lean_ctor_get(x_778, 6);
lean_inc_ref(x_818);
x_819 = lean_ctor_get(x_778, 7);
lean_inc_ref(x_819);
lean_dec_ref(x_778);
x_820 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_820, 0, x_801);
lean_ctor_set_uint8(x_820, 1, x_791);
x_755 = x_817;
x_756 = x_789;
x_757 = x_788;
x_758 = x_813;
x_759 = x_818;
x_760 = x_785;
x_761 = x_814;
x_762 = x_780;
x_763 = x_783;
x_764 = lean_box(0);
x_765 = x_819;
x_766 = x_815;
x_767 = x_791;
x_768 = x_812;
x_769 = x_816;
x_770 = x_790;
x_771 = x_820;
goto block_777;
}
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; uint8_t x_827; 
x_821 = lean_ctor_get(x_794, 0);
x_822 = lean_ctor_get(x_794, 1);
x_823 = lean_ctor_get(x_794, 2);
lean_inc(x_823);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_794);
x_824 = lean_string_utf8_extract(x_821, x_822, x_823);
lean_dec(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_825 = lean_string_utf8_byte_size(x_824);
x_826 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_780);
lean_ctor_set(x_826, 2, x_825);
x_827 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(x_826);
lean_dec_ref(x_826);
if (x_827 == 0)
{
x_728 = x_789;
x_729 = x_788;
x_730 = x_785;
x_731 = x_791;
x_732 = x_780;
x_733 = x_790;
x_734 = x_783;
x_735 = x_778;
x_736 = lean_box(0);
goto block_754;
}
else
{
uint8_t x_828; 
x_828 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_829 = lean_ctor_get(x_778, 0);
lean_inc_ref(x_829);
x_830 = lean_ctor_get(x_778, 1);
lean_inc_ref(x_830);
x_831 = lean_ctor_get(x_778, 2);
lean_inc_ref(x_831);
x_832 = lean_ctor_get(x_778, 3);
lean_inc_ref(x_832);
x_833 = lean_ctor_get(x_778, 4);
lean_inc_ref(x_833);
x_834 = lean_ctor_get(x_778, 5);
lean_inc_ref(x_834);
x_835 = lean_ctor_get(x_778, 6);
lean_inc_ref(x_835);
x_836 = lean_ctor_get(x_778, 7);
lean_inc_ref(x_836);
lean_dec_ref(x_778);
x_837 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0));
x_755 = x_834;
x_756 = x_789;
x_757 = x_788;
x_758 = x_830;
x_759 = x_835;
x_760 = x_785;
x_761 = x_831;
x_762 = x_780;
x_763 = x_783;
x_764 = lean_box(0);
x_765 = x_836;
x_766 = x_832;
x_767 = x_791;
x_768 = x_829;
x_769 = x_833;
x_770 = x_790;
x_771 = x_837;
goto block_777;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_838 = lean_ctor_get(x_778, 0);
lean_inc_ref(x_838);
x_839 = lean_ctor_get(x_778, 1);
lean_inc_ref(x_839);
x_840 = lean_ctor_get(x_778, 2);
lean_inc_ref(x_840);
x_841 = lean_ctor_get(x_778, 3);
lean_inc_ref(x_841);
x_842 = lean_ctor_get(x_778, 4);
lean_inc_ref(x_842);
x_843 = lean_ctor_get(x_778, 5);
lean_inc_ref(x_843);
x_844 = lean_ctor_get(x_778, 6);
lean_inc_ref(x_844);
x_845 = lean_ctor_get(x_778, 7);
lean_inc_ref(x_845);
lean_dec_ref(x_778);
x_846 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_846, 0, x_827);
lean_ctor_set_uint8(x_846, 1, x_791);
x_755 = x_843;
x_756 = x_789;
x_757 = x_788;
x_758 = x_839;
x_759 = x_844;
x_760 = x_785;
x_761 = x_840;
x_762 = x_780;
x_763 = x_783;
x_764 = lean_box(0);
x_765 = x_845;
x_766 = x_841;
x_767 = x_791;
x_768 = x_838;
x_769 = x_842;
x_770 = x_790;
x_771 = x_846;
goto block_777;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
x_11 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(x_1, x_2, x_3, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec_ref(x_1);
if (x_3 == 0)
{
uint8_t x_10; 
x_10 = 1;
x_4 = x_10;
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = 0;
x_4 = x_11;
goto block_9;
}
block_9:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 1;
x_6 = l_Lean_Name_toString(x_2, x_5);
x_7 = lean_box(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__2));
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__1));
x_3 = l_lexOrd___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__0));
x_2 = l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3;
x_3 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_23; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_23 = lean_nat_dec_lt(x_6, x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_27, 2);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
x_9 = x_5;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_33; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_27, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_27, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
x_39 = lean_ctor_get(x_28, 2);
x_40 = lean_array_fget(x_29, x_30);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_30, x_41);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_42);
x_43 = lean_nat_dec_lt(x_38, x_39);
if (x_43 == 0)
{
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_2);
x_9 = x_5;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_44; 
lean_inc(x_39);
lean_inc(x_38);
lean_inc_ref(x_37);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_28, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_28, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_28, 0);
lean_dec(x_47);
x_48 = lean_array_fget(x_37, x_38);
x_49 = lean_nat_add(x_38, x_41);
lean_dec(x_38);
lean_ctor_set(x_28, 1, x_49);
x_50 = lean_task_get_own(x_40);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_io_error_to_string(x_51);
x_53 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_17 = x_5;
x_18 = x_7;
x_19 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_54; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_free_object(x_5);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec_ref(x_50);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = 0;
x_62 = lean_task_get_own(x_48);
lean_inc(x_6);
lean_inc(x_2);
x_63 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_6, x_62, x_60, x_3, x_61, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_17 = x_5;
x_18 = x_65;
x_19 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_66; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_28);
x_69 = lean_array_fget(x_37, x_38);
x_70 = lean_nat_add(x_38, x_41);
lean_dec(x_38);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_39);
x_72 = lean_task_get_own(x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_io_error_to_string(x_73);
x_75 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
lean_ctor_set(x_5, 0, x_71);
x_17 = x_5;
x_18 = x_7;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_71);
lean_dec_ref(x_27);
lean_free_object(x_5);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec_ref(x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = 0;
x_84 = lean_task_get_own(x_69);
lean_inc(x_6);
lean_inc(x_2);
x_85 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_6, x_84, x_82, x_3, x_83, x_7);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_ctor_set(x_5, 0, x_71);
x_17 = x_5;
x_18 = x_87;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_71);
lean_dec_ref(x_27);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_2);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_27);
x_91 = lean_ctor_get(x_28, 0);
x_92 = lean_ctor_get(x_28, 1);
x_93 = lean_ctor_get(x_28, 2);
x_94 = lean_array_fget(x_29, x_30);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_30, x_95);
lean_dec(x_30);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_29);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_31);
x_98 = lean_nat_dec_lt(x_92, x_93);
if (x_98 == 0)
{
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
lean_ctor_set(x_5, 1, x_97);
x_9 = x_5;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_inc(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_99 = x_28;
} else {
 lean_dec_ref(x_28);
 x_99 = lean_box(0);
}
x_100 = lean_array_fget(x_91, x_92);
x_101 = lean_nat_add(x_92, x_95);
lean_dec(x_92);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 3, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_93);
x_103 = lean_task_get_own(x_94);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_100);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_io_error_to_string(x_104);
x_106 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_dec_ref(x_106);
lean_ctor_set(x_5, 1, x_97);
lean_ctor_set(x_5, 0, x_102);
x_17 = x_5;
x_18 = x_7;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_102);
lean_dec_ref(x_97);
lean_free_object(x_5);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec_ref(x_103);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = 0;
x_115 = lean_task_get_own(x_100);
lean_inc(x_6);
lean_inc(x_2);
x_116 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_6, x_115, x_113, x_3, x_114, x_7);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_ctor_set(x_5, 1, x_97);
lean_ctor_set(x_5, 0, x_102);
x_17 = x_5;
x_18 = x_118;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_102);
lean_dec_ref(x_97);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_2);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_5, 1);
x_123 = lean_ctor_get(x_5, 0);
lean_inc(x_122);
lean_inc(x_123);
lean_dec(x_5);
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_ctor_get(x_122, 2);
x_127 = lean_nat_dec_lt(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_6);
lean_dec(x_2);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_122);
x_9 = x_128;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_inc(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_123, 0);
x_131 = lean_ctor_get(x_123, 1);
x_132 = lean_ctor_get(x_123, 2);
x_133 = lean_array_fget(x_124, x_125);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_125, x_134);
lean_dec(x_125);
if (lean_is_scalar(x_129)) {
 x_136 = lean_alloc_ctor(0, 3, 0);
} else {
 x_136 = x_129;
}
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_126);
x_137 = lean_nat_dec_lt(x_131, x_132);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_2);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_123);
lean_ctor_set(x_138, 1, x_136);
x_9 = x_138;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_inc(x_132);
lean_inc(x_131);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 x_139 = x_123;
} else {
 lean_dec_ref(x_123);
 x_139 = lean_box(0);
}
x_140 = lean_array_fget(x_130, x_131);
x_141 = lean_nat_add(x_131, x_134);
lean_dec(x_131);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_130);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_132);
x_143 = lean_task_get_own(x_133);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = lean_io_error_to_string(x_144);
x_146 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
lean_dec_ref(x_146);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_136);
x_17 = x_147;
x_18 = x_7;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_142);
lean_dec_ref(x_136);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_143, 0);
lean_inc(x_151);
lean_dec_ref(x_143);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_155 = 0;
x_156 = lean_task_get_own(x_140);
lean_inc(x_6);
lean_inc(x_2);
x_157 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_6, x_156, x_154, x_3, x_155, x_7);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_142);
lean_ctor_set(x_160, 1, x_136);
x_17 = x_160;
x_18 = x_159;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_142);
lean_dec_ref(x_136);
lean_dec(x_6);
lean_dec(x_2);
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_162 = x_157;
} else {
 lean_dec_ref(x_157);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_22:
{
lean_object* x_20; 
x_20 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_5 = x_17;
x_6 = x_20;
x_7 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec_ref(x_2);
if (x_17 == 0)
{
x_18 = x_1;
goto block_22;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_18 = x_23;
goto block_22;
}
block_8:
{
uint8_t x_7; 
x_7 = lean_string_dec_lt(x_6, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_6);
if (x_7 == 0)
{
return x_7;
}
else
{
return x_4;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = l_Lean_Name_toString(x_13, x_10);
if (x_9 == 0)
{
if (x_12 == 1)
{
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_12;
}
else
{
x_4 = x_10;
x_5 = x_14;
x_6 = x_11;
goto block_8;
}
}
else
{
if (x_12 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_11);
return x_12;
}
else
{
x_4 = x_10;
x_5 = x_14;
x_6 = x_11;
goto block_8;
}
}
}
block_22:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_20 = l_Lean_Name_toString(x_16, x_1);
if (x_19 == 0)
{
x_9 = x_18;
x_10 = x_1;
x_11 = x_20;
x_12 = x_1;
goto block_15;
}
else
{
uint8_t x_21; 
x_21 = 0;
x_9 = x_18;
x_10 = x_1;
x_11 = x_20;
x_12 = x_21;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0(x_4, x_2, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc(x_2);
x_7 = l_Array_qpartition___redArg(x_1, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_nat_dec_le(x_3, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(x_9, x_2, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_12 = lean_nat_dec_le(x_3, x_6);
if (x_12 == 0)
{
lean_inc(x_6);
x_7 = x_6;
goto block_11;
}
else
{
x_7 = x_3;
goto block_11;
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_inc(x_7);
x_9 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(x_1, x_7, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(x_1, x_7, x_6);
lean_dec(x_6);
return x_10;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqImport_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_instHashableImport_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
lean_dec(x_5);
x_10 = 10;
x_11 = lean_nat_add(x_2, x_4);
x_12 = lean_string_utf8_get_fast(x_3, x_11);
x_13 = lean_uint32_dec_eq(x_12, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_string_utf8_next_fast(x_3, x_11);
lean_dec(x_11);
x_16 = lean_nat_sub(x_15, x_2);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_instHashableImport_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_instHashableImport_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableImport_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_52; uint8_t x_69; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = 0;
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_19);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_19);
x_69 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_2, x_20);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_16, x_20);
if (x_70 == 0)
{
lean_dec(x_19);
x_21 = x_13;
x_22 = x_15;
x_23 = x_7;
x_24 = lean_box(0);
goto block_32;
}
else
{
goto block_68;
}
}
else
{
goto block_68;
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_25 = lean_box(0);
x_26 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(x_16, x_20, x_25);
if (lean_is_scalar(x_17)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_17;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
if (lean_is_scalar(x_14)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_14;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_28;
x_7 = x_23;
goto _start;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_38 = l_String_Slice_Pos_next_x21(x_33, x_37);
lean_dec(x_37);
lean_dec_ref(x_33);
x_21 = x_35;
x_22 = x_38;
x_23 = x_7;
x_24 = lean_box(0);
goto block_32;
}
block_51:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_String_Slice_pos_x21(x_40, x_44);
lean_dec(x_44);
lean_inc(x_43);
lean_inc(x_45);
lean_inc_ref(x_1);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
x_47 = lean_box(0);
x_48 = l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(x_46, x_45, x_1, x_41, x_47);
lean_dec_ref(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_nat_sub(x_43, x_45);
lean_dec(x_43);
x_33 = x_40;
x_34 = x_45;
x_35 = x_42;
x_36 = x_49;
goto block_39;
}
else
{
lean_object* x_50; 
lean_dec(x_43);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_33 = x_40;
x_34 = x_45;
x_35 = x_42;
x_36 = x_50;
goto block_39;
}
}
block_63:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_String_Slice_pos_x21(x_55, x_52);
lean_dec(x_52);
x_57 = lean_string_utf8_extract(x_1, x_15, x_56);
lean_dec(x_56);
lean_dec(x_15);
x_58 = lean_string_append(x_13, x_57);
lean_dec_ref(x_57);
x_59 = l_Lean_Syntax_getTailPos_x3f(x_19, x_18);
lean_dec(x_19);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_61 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_60);
x_40 = x_55;
x_41 = x_53;
x_42 = x_58;
x_43 = x_54;
x_44 = x_61;
goto block_51;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec_ref(x_59);
x_40 = x_55;
x_41 = x_53;
x_42 = x_58;
x_43 = x_54;
x_44 = x_62;
goto block_51;
}
}
block_68:
{
lean_object* x_64; 
x_64 = l_Lean_Syntax_getPos_x3f(x_19, x_18);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3;
x_66 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_65);
x_52 = x_66;
goto block_63;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec_ref(x_64);
x_52 = x_67;
goto block_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_20 = x_5;
} else {
 lean_dec_ref(x_5);
 x_20 = lean_box(0);
}
x_21 = lean_array_uget(x_2, x_4);
x_22 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_19, x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_37; lean_object* x_38; lean_object* x_46; 
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_24 = lean_box(0);
lean_inc(x_21);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(x_19, x_21, x_24);
if (x_23 == 0)
{
lean_object* x_51; 
x_51 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_46 = x_51;
goto block_50;
}
else
{
lean_object* x_52; 
x_52 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_46 = x_52;
goto block_50;
}
block_36:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_30 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_28, x_1);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___closed__0));
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_18, x_33);
lean_dec_ref(x_33);
if (lean_is_scalar(x_20)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_20;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_8 = x_35;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
block_45:
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_40 = lean_string_append(x_37, x_38);
lean_dec_ref(x_38);
x_41 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_42 = lean_string_append(x_40, x_41);
if (x_39 == 0)
{
lean_object* x_43; 
x_43 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_26 = x_42;
x_27 = x_43;
goto block_36;
}
else
{
lean_object* x_44; 
x_44 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_26 = x_42;
x_27 = x_44;
goto block_36;
}
}
block_50:
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_37 = x_46;
x_38 = x_48;
goto block_45;
}
else
{
lean_object* x_49; 
x_49 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_37 = x_46;
x_38 = x_49;
goto block_45;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_21);
if (lean_is_scalar(x_20)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_20;
}
lean_ctor_set(x_53, 0, x_18);
lean_ctor_set(x_53, 1, x_19);
x_8 = x_53;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2;
x_2 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_inc(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 4);
x_32 = lean_array_fget(x_21, x_22);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_uget(x_2, x_4);
x_35 = lean_nat_add(x_22, x_33);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_35);
x_36 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_31, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_task_get_own(x_32);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; 
lean_free_object(x_5);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_46);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_45, 2);
lean_inc_ref(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_50);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3;
x_54 = lean_array_size(x_51);
x_55 = 0;
lean_inc_ref(x_52);
x_56 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(x_52, x_38, x_51, x_54, x_55, x_53, x_6);
lean_dec(x_51);
lean_dec(x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(x_39);
x_65 = lean_string_utf8_extract(x_52, x_63, x_47);
lean_dec(x_63);
x_66 = lean_string_append(x_61, x_65);
lean_dec_ref(x_65);
lean_ctor_set(x_59, 0, x_66);
x_67 = lean_array_size(x_64);
x_68 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_1, x_64, x_67, x_55, x_59, x_60);
lean_dec_ref(x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
lean_dec(x_74);
x_75 = lean_string_utf8_byte_size(x_52);
x_76 = lean_string_utf8_extract(x_52, x_47, x_75);
lean_dec(x_47);
lean_dec_ref(x_52);
x_77 = lean_string_append(x_73, x_76);
lean_dec_ref(x_76);
x_78 = l_IO_FS_writeFile(x_44, x_77);
lean_dec_ref(x_77);
lean_dec(x_44);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_dec_ref(x_78);
x_79 = lean_nat_add(x_20, x_33);
lean_dec(x_20);
lean_ctor_set(x_70, 1, x_79);
lean_ctor_set(x_70, 0, x_19);
x_8 = x_70;
x_9 = x_71;
x_10 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_80; 
lean_free_object(x_70);
lean_dec(x_71);
lean_dec_ref(x_19);
lean_dec(x_20);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
lean_dec(x_70);
x_84 = lean_string_utf8_byte_size(x_52);
x_85 = lean_string_utf8_extract(x_52, x_47, x_84);
lean_dec(x_47);
lean_dec_ref(x_52);
x_86 = lean_string_append(x_83, x_85);
lean_dec_ref(x_85);
x_87 = l_IO_FS_writeFile(x_44, x_86);
lean_dec_ref(x_86);
lean_dec(x_44);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_87);
x_88 = lean_nat_add(x_20, x_33);
lean_dec(x_20);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_88);
x_8 = x_89;
x_9 = x_71;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_71);
lean_dec_ref(x_19);
lean_dec(x_20);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_19);
lean_dec(x_20);
x_93 = !lean_is_exclusive(x_68);
if (x_93 == 0)
{
return x_68;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_68, 0);
lean_inc(x_94);
lean_dec(x_68);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_59, 0);
x_97 = lean_ctor_get(x_59, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_59);
x_98 = l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(x_39);
x_99 = lean_string_utf8_extract(x_52, x_96, x_47);
lean_dec(x_96);
x_100 = lean_string_append(x_61, x_99);
lean_dec_ref(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
x_102 = lean_array_size(x_98);
x_103 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_1, x_98, x_102, x_55, x_101, x_60);
lean_dec_ref(x_98);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_string_utf8_byte_size(x_52);
x_110 = lean_string_utf8_extract(x_52, x_47, x_109);
lean_dec(x_47);
lean_dec_ref(x_52);
x_111 = lean_string_append(x_107, x_110);
lean_dec_ref(x_110);
x_112 = l_IO_FS_writeFile(x_44, x_111);
lean_dec_ref(x_111);
lean_dec(x_44);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_112);
x_113 = lean_nat_add(x_20, x_33);
lean_dec(x_20);
if (lean_is_scalar(x_108)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_108;
}
lean_ctor_set(x_114, 0, x_19);
lean_ctor_set(x_114, 1, x_113);
x_8 = x_114;
x_9 = x_106;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_19);
lean_dec(x_20);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_19);
lean_dec(x_20);
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_119 = x_103;
} else {
 lean_dec_ref(x_103);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_39);
lean_dec_ref(x_19);
lean_dec(x_20);
x_121 = !lean_is_exclusive(x_56);
if (x_121 == 0)
{
return x_56;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_56, 0);
lean_inc(x_122);
lean_dec(x_56);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec(x_36);
lean_dec(x_32);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_19);
x_124 = lean_ctor_get(x_6, 4);
x_125 = lean_array_fget(x_21, x_22);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_array_uget(x_2, x_4);
x_128 = lean_nat_add(x_22, x_126);
lean_dec(x_22);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_21);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_23);
x_130 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_124, x_127);
lean_dec(x_127);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_task_get_own(x_125);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; 
lean_free_object(x_5);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_140);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_ctor_get(x_139, 2);
lean_inc_ref(x_144);
lean_dec(x_139);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc_ref(x_146);
lean_dec_ref(x_144);
x_147 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3;
x_148 = lean_array_size(x_145);
x_149 = 0;
lean_inc_ref(x_146);
x_150 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(x_146, x_132, x_145, x_148, x_149, x_147, x_6);
lean_dec(x_145);
lean_dec(x_132);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; size_t x_163; lean_object* x_164; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(x_133);
x_160 = lean_string_utf8_extract(x_146, x_156, x_141);
lean_dec(x_156);
x_161 = lean_string_append(x_155, x_160);
lean_dec_ref(x_160);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
x_163 = lean_array_size(x_159);
x_164 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_1, x_159, x_163, x_149, x_162, x_154);
lean_dec_ref(x_159);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_string_utf8_byte_size(x_146);
x_171 = lean_string_utf8_extract(x_146, x_141, x_170);
lean_dec(x_141);
lean_dec_ref(x_146);
x_172 = lean_string_append(x_168, x_171);
lean_dec_ref(x_171);
x_173 = l_IO_FS_writeFile(x_138, x_172);
lean_dec_ref(x_172);
lean_dec(x_138);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_173);
x_174 = lean_nat_add(x_20, x_126);
lean_dec(x_20);
if (lean_is_scalar(x_169)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_169;
}
lean_ctor_set(x_175, 0, x_129);
lean_ctor_set(x_175, 1, x_174);
x_8 = x_175;
x_9 = x_167;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec_ref(x_129);
lean_dec(x_20);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_146);
lean_dec(x_141);
lean_dec(x_138);
lean_dec_ref(x_129);
lean_dec(x_20);
x_179 = lean_ctor_get(x_164, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec_ref(x_146);
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_133);
lean_dec_ref(x_129);
lean_dec(x_20);
x_182 = lean_ctor_get(x_150, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_183 = x_150;
} else {
 lean_dec_ref(x_150);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
else
{
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_ctor_set(x_5, 0, x_129);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec(x_130);
lean_dec(x_125);
lean_ctor_set(x_5, 0, x_129);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_5, 0);
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_5);
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = lean_ctor_get(x_185, 2);
x_190 = lean_nat_dec_lt(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_186);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_6);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc_ref(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 x_194 = x_185;
} else {
 lean_dec_ref(x_185);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_6, 4);
x_196 = lean_array_fget(x_187, x_188);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_array_uget(x_2, x_4);
x_199 = lean_nat_add(x_188, x_197);
lean_dec(x_188);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_187);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_189);
x_201 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_195, x_198);
lean_dec(x_198);
if (lean_obj_tag(x_201) == 1)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_task_get_own(x_196);
if (lean_obj_tag(x_205) == 1)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; lean_object* x_221; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_ctor_get(x_207, 0);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_ctor_get(x_208, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_dec(x_208);
x_213 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_211);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = lean_ctor_get(x_210, 2);
lean_inc_ref(x_215);
lean_dec(x_210);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_217);
lean_dec_ref(x_215);
x_218 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3;
x_219 = lean_array_size(x_216);
x_220 = 0;
lean_inc_ref(x_217);
x_221 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(x_217, x_203, x_216, x_219, x_220, x_218, x_6);
lean_dec(x_216);
lean_dec(x_203);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; size_t x_234; lean_object* x_235; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_229 = x_224;
} else {
 lean_dec_ref(x_224);
 x_229 = lean_box(0);
}
x_230 = l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(x_204);
x_231 = lean_string_utf8_extract(x_217, x_227, x_212);
lean_dec(x_227);
x_232 = lean_string_append(x_226, x_231);
lean_dec_ref(x_231);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_229;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_228);
x_234 = lean_array_size(x_230);
x_235 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_1, x_230, x_234, x_220, x_233, x_225);
lean_dec_ref(x_230);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
x_241 = lean_string_utf8_byte_size(x_217);
x_242 = lean_string_utf8_extract(x_217, x_212, x_241);
lean_dec(x_212);
lean_dec_ref(x_217);
x_243 = lean_string_append(x_239, x_242);
lean_dec_ref(x_242);
x_244 = l_IO_FS_writeFile(x_209, x_243);
lean_dec_ref(x_243);
lean_dec(x_209);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_244);
x_245 = lean_nat_add(x_186, x_197);
lean_dec(x_186);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_240;
}
lean_ctor_set(x_246, 0, x_200);
lean_ctor_set(x_246, 1, x_245);
x_8 = x_246;
x_9 = x_238;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_240);
lean_dec(x_238);
lean_dec_ref(x_200);
lean_dec(x_186);
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_248 = x_244;
} else {
 lean_dec_ref(x_244);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec_ref(x_217);
lean_dec(x_212);
lean_dec(x_209);
lean_dec_ref(x_200);
lean_dec(x_186);
x_250 = lean_ctor_get(x_235, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_251 = x_235;
} else {
 lean_dec_ref(x_235);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_217);
lean_dec(x_212);
lean_dec(x_209);
lean_dec(x_204);
lean_dec_ref(x_200);
lean_dec(x_186);
x_253 = lean_ctor_get(x_221, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_254 = x_221;
} else {
 lean_dec_ref(x_221);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
else
{
lean_object* x_256; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_200);
lean_ctor_set(x_256, 1, x_186);
x_8 = x_256;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_257; 
lean_dec(x_201);
lean_dec(x_196);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_200);
lean_ctor_set(x_257, 1, x_186);
x_8 = x_257;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Shake_run___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint32_t x_9, lean_object* x_10, size_t x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_array_get_size(x_1);
lean_inc(x_2);
x_22 = l_Array_toSubarray___redArg(x_1, x_2, x_21);
x_23 = lean_array_get_size(x_3);
lean_inc(x_2);
x_24 = l_Array_toSubarray___redArg(x_3, x_2, x_23);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_25);
lean_inc_ref(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_inc(x_2);
x_28 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg(x_5, x_6, x_7, x_26, x_27, x_2, x_13);
lean_dec_ref(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (x_8 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec_ref(x_24);
x_38 = lean_ctor_get(x_31, 4);
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_nat_dec_eq(x_39, x_2);
lean_dec(x_2);
if (x_40 == 0)
{
uint32_t x_41; 
x_41 = 1;
x_33 = x_41;
goto block_37;
}
else
{
x_33 = x_9;
goto block_37;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_30);
x_42 = lean_ctor_get(x_10, 7);
lean_inc(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_2);
x_44 = lean_array_size(x_42);
x_45 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12(x_8, x_42, x_44, x_11, x_43, x_31);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_nat_dec_lt(x_2, x_49);
lean_dec(x_2);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__0));
x_52 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_15 = x_48;
x_16 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_53; 
lean_dec(x_48);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__1));
x_57 = l_Nat_reprFast(x_49);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
x_59 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__2));
x_60 = lean_string_append(x_58, x_59);
x_61 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_15 = x_48;
x_16 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_62; 
lean_dec(x_48);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_45);
if (x_65 == 0)
{
return x_45;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_45, 0);
lean_inc(x_66);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
block_37:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box_uint32(x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
if (lean_is_scalar(x_30)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_30;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_24);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_28);
if (x_68 == 0)
{
return x_28;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
lean_dec(x_28);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box_uint32(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Shake_run___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint32_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_8);
x_16 = lean_unbox_uint32(x_9);
lean_dec(x_9);
x_17 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_18 = l_Lake_Shake_run___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_16, x_10, x_17, x_12, x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_task_spawn(x_7, x_5);
x_11 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_12 = lean_array_push(x_4, x_10);
x_2 = x_9;
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Name_getRoot(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 7);
x_8 = lean_box(0);
x_9 = lean_array_uget(x_3, x_4);
x_10 = lean_array_get_borrowed(x_8, x_7, x_2);
x_11 = l_Lean_Name_isPrefixOf(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0;
x_2 = l_Lean_instInhabitedFileMap_default;
x_3 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2));
x_2 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3;
x_2 = l_System_instInhabitedFilePath_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_24; lean_object* x_31; uint8_t x_32; 
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_31 = lean_array_get_size(x_3);
x_32 = lean_nat_dec_lt(x_10, x_31);
if (x_32 == 0)
{
x_24 = x_4;
goto block_30;
}
else
{
if (x_32 == 0)
{
x_24 = x_4;
goto block_30;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_31);
x_35 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__2(x_1, x_6, x_3, x_33, x_34);
x_24 = x_35;
goto block_30;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_21 = lean_array_push(x_7, x_17);
x_5 = x_16;
x_6 = x_20;
x_7 = x_21;
x_8 = x_18;
goto _start;
}
block_30:
{
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6;
x_17 = x_25;
x_18 = x_8;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 7);
x_27 = lean_array_get_borrowed(x_14, x_26, x_6);
lean_inc(x_27);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_io_as_task(x_28, x_10);
x_17 = x_29;
x_18 = x_8;
x_19 = lean_box(0);
goto block_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
lean_dec(x_5);
x_7 = 1;
if (x_6 == 0)
{
return x_7;
}
else
{
if (x_4 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Shake_run___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Shake_run___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Shake_run___closed__0;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Shake_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 8);
x_16 = lean_ctor_get(x_1, 0);
x_17 = l_Lean_instInhabitedImportState_default;
x_18 = lean_st_mk_ref(x_17);
x_19 = lean_array_size(x_16);
x_20 = 0;
lean_inc_ref(x_16);
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0(x_19, x_20, x_16);
x_22 = lean_box(1);
lean_inc_ref(x_16);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(x_19, x_20, x_16);
x_24 = 2;
x_25 = 1;
lean_inc(x_18);
x_26 = l_Lean_importModulesCore(x_23, x_24, x_22, x_25, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_32; 
lean_dec_ref(x_26);
x_27 = lean_st_ref_get(x_18);
lean_dec(x_18);
x_28 = l_Lean_ImportState_markAllExported(x_27);
x_29 = l_Lean_Options_empty;
x_30 = 0;
x_31 = 0;
x_32 = l_Lean_finalizeImport(x_28, x_23, x_29, x_30, x_25, x_31, x_24, x_25);
lean_dec_ref(x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_108; uint8_t x_109; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_Environment_header(x_34);
x_36 = lean_ctor_get(x_35, 6);
lean_inc_ref(x_36);
lean_dec_ref(x_35);
x_37 = l_Lake_Shake_run___closed__1;
x_38 = lean_unsigned_to_nat(0u);
x_108 = lean_array_get_size(x_36);
x_109 = lean_nat_dec_lt(x_38, x_108);
if (x_109 == 0)
{
lean_dec_ref(x_36);
lean_free_object(x_32);
x_39 = x_31;
goto block_107;
}
else
{
if (x_109 == 0)
{
lean_dec_ref(x_36);
lean_free_object(x_32);
x_39 = x_31;
goto block_107;
}
else
{
size_t x_110; uint8_t x_111; 
x_110 = lean_usize_of_nat(x_108);
x_111 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(x_36, x_20, x_110);
lean_dec_ref(x_36);
if (x_111 == 0)
{
lean_free_object(x_32);
x_39 = x_111;
goto block_107;
}
else
{
lean_object* x_112; 
lean_dec(x_34);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_112 = ((lean_object*)(l_Lake_Shake_run___closed__4));
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_112);
return x_32;
}
}
}
block_107:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = l_Lean_indirectModUseExt;
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 2);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_41, 2);
x_44 = lean_box(0);
lean_inc(x_34);
x_45 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_37, x_41, x_34, x_43, x_44);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_dec(x_48);
lean_inc(x_34);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_29);
lean_inc_ref(x_47);
x_50 = lean_apply_3(x_42, x_47, x_49, lean_box(0));
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
lean_ctor_set(x_45, 1, x_51);
x_52 = lean_box(0);
x_53 = l_Lean_EnvExtension_setState___redArg(x_41, x_34, x_45, x_52);
x_54 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(x_53);
x_55 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_54);
x_56 = lean_array_get_size(x_55);
lean_dec_ref(x_55);
x_57 = lean_mk_empty_array_with_capacity(x_56);
lean_inc_ref(x_57);
lean_inc_ref(x_54);
x_58 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(x_54, x_56, x_38, x_57);
lean_inc(x_2);
lean_inc_ref(x_54);
x_59 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_54, x_2, x_21, x_39, x_56, x_38, x_57, x_54);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
if (x_15 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
x_64 = l_Lake_Shake_run___lam__0(x_58, x_38, x_61, x_56, x_21, x_2, x_1, x_15, x_30, x_54, x_20, x_63, x_62);
lean_dec_ref(x_54);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_64;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = ((lean_object*)(l_Lake_Shake_run___closed__2));
x_68 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lake_Shake_run___lam__0(x_58, x_38, x_65, x_56, x_21, x_2, x_1, x_15, x_30, x_54, x_20, x_69, x_66);
lean_dec_ref(x_54);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_70;
goto block_14;
}
else
{
uint8_t x_71; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_58);
lean_dec_ref(x_54);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_45);
lean_dec_ref(x_47);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_50);
if (x_74 == 0)
{
return x_50;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_50, 0);
lean_inc(x_75);
lean_dec(x_50);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_45, 0);
lean_inc(x_77);
lean_dec(x_45);
lean_inc(x_34);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_34);
lean_ctor_set(x_78, 1, x_29);
lean_inc_ref(x_77);
x_79 = lean_apply_3(x_42, x_77, x_78, lean_box(0));
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_box(0);
x_83 = l_Lean_EnvExtension_setState___redArg(x_41, x_34, x_81, x_82);
x_84 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(x_83);
x_85 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_84);
x_86 = lean_array_get_size(x_85);
lean_dec_ref(x_85);
x_87 = lean_mk_empty_array_with_capacity(x_86);
lean_inc_ref(x_87);
lean_inc_ref(x_84);
x_88 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(x_84, x_86, x_38, x_87);
lean_inc(x_2);
lean_inc_ref(x_84);
x_89 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_84, x_2, x_21, x_39, x_86, x_38, x_87, x_84);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
if (x_15 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_box(0);
x_94 = l_Lake_Shake_run___lam__0(x_88, x_38, x_91, x_86, x_21, x_2, x_1, x_15, x_30, x_84, x_20, x_93, x_92);
lean_dec_ref(x_84);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_94;
goto block_14;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_dec(x_90);
x_97 = ((lean_object*)(l_Lake_Shake_run___closed__2));
x_98 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lake_Shake_run___lam__0(x_88, x_38, x_95, x_86, x_21, x_2, x_1, x_15, x_30, x_84, x_20, x_99, x_96);
lean_dec_ref(x_84);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_100;
goto block_14;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_88);
lean_dec_ref(x_84);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_77);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_105 = x_79;
} else {
 lean_dec_ref(x_79);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_157; uint8_t x_158; 
x_113 = lean_ctor_get(x_32, 0);
lean_inc(x_113);
lean_dec(x_32);
x_114 = l_Lean_Environment_header(x_113);
x_115 = lean_ctor_get(x_114, 6);
lean_inc_ref(x_115);
lean_dec_ref(x_114);
x_116 = l_Lake_Shake_run___closed__1;
x_117 = lean_unsigned_to_nat(0u);
x_157 = lean_array_get_size(x_115);
x_158 = lean_nat_dec_lt(x_117, x_157);
if (x_158 == 0)
{
lean_dec_ref(x_115);
x_118 = x_31;
goto block_156;
}
else
{
if (x_158 == 0)
{
lean_dec_ref(x_115);
x_118 = x_31;
goto block_156;
}
else
{
size_t x_159; uint8_t x_160; 
x_159 = lean_usize_of_nat(x_157);
x_160 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(x_115, x_20, x_159);
lean_dec_ref(x_115);
if (x_160 == 0)
{
x_118 = x_160;
goto block_156;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_113);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = ((lean_object*)(l_Lake_Shake_run___closed__4));
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
block_156:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = l_Lean_indirectModUseExt;
x_120 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_119, 2);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_120, 2);
x_123 = lean_box(0);
lean_inc(x_113);
x_124 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_116, x_120, x_113, x_122, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
lean_inc(x_113);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_113);
lean_ctor_set(x_127, 1, x_29);
lean_inc_ref(x_125);
x_128 = lean_apply_3(x_121, x_125, x_127, lean_box(0));
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_box(0);
x_132 = l_Lean_EnvExtension_setState___redArg(x_120, x_113, x_130, x_131);
x_133 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(x_132);
x_134 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_133);
x_135 = lean_array_get_size(x_134);
lean_dec_ref(x_134);
x_136 = lean_mk_empty_array_with_capacity(x_135);
lean_inc_ref(x_136);
lean_inc_ref(x_133);
x_137 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(x_133, x_135, x_117, x_136);
lean_inc(x_2);
lean_inc_ref(x_133);
x_138 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_133, x_2, x_21, x_118, x_135, x_117, x_136, x_133);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
if (x_15 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_box(0);
x_143 = l_Lake_Shake_run___lam__0(x_137, x_117, x_140, x_135, x_21, x_2, x_1, x_15, x_30, x_133, x_20, x_142, x_141);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_143;
goto block_14;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = ((lean_object*)(l_Lake_Shake_run___closed__2));
x_147 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = l_Lake_Shake_run___lam__0(x_137, x_117, x_144, x_135, x_21, x_2, x_1, x_15, x_30, x_133, x_20, x_148, x_145);
lean_dec_ref(x_133);
lean_dec_ref(x_1);
lean_dec_ref(x_21);
x_4 = x_149;
goto block_14;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_137);
lean_dec_ref(x_133);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_120);
lean_dec(x_113);
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_128, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_154 = x_128;
} else {
 lean_dec_ref(x_128);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
}
}
else
{
uint8_t x_163; 
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_163 = !lean_is_exclusive(x_32);
if (x_163 == 0)
{
return x_32;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_32, 0);
lean_inc(x_164);
lean_dec(x_32);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_26);
if (x_166 == 0)
{
return x_26;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_26, 0);
lean_inc(x_167);
lean_dec(x_26);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
block_14:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Shake_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Shake_run(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lake_Shake_run_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Array_qsortOrd___at___00Lake_Shake_run_spec__10_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8_spec__9_spec__16___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Shake(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default);
l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10);
l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__1);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__2);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__3);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__4);
l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10);
l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13);
l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2);
l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1);
l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1);
l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2);
l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1);
l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2);
l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3);
l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0);
l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__1);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0);
l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0 = _init_l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__1);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__2 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__2();
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__3);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__4);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___closed__5);
l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0();
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2();
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2();
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4);
l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5 = _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5();
lean_mark_persistent(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5);
l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3);
l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4 = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4);
l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5);
l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6 = _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6);
l_Lake_Shake_run___closed__0 = _init_l_Lake_Shake_run___closed__0();
lean_mark_persistent(l_Lake_Shake_run___closed__0);
l_Lake_Shake_run___closed__1 = _init_l_Lake_Shake_run___closed__1();
lean_mark_persistent(l_Lake_Shake_run___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
