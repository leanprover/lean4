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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__8_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__8_value;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_pub___closed__0_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPub___closed__0_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_metaPriv___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all___closed__0_value;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "priv"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__6_value;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "metaPub"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__9_value;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10;
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metaPriv"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__12_value;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
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
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_simp_"};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_array_object l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
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
extern lean_object* l_Lean_instBEqModuleIdx;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0;
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0_value),((lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0_value;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2;
static const lean_array_object l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3_value;
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
static const lean_array_object l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0 = (const lean_object*)&l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0_value;
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
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "shake: keep"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0_value;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5;
static const lean_ctor_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6_value;
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
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "shake: keep-downstream"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__0_value;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0;
extern lean_object* l_Lean_instInhabitedFileMap_default;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3;
extern lean_object* l_System_instInhabitedFilePath_default;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5;
lean_object* lean_task_pure(lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Shake_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Shake_run___closed__0;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
static lean_once_cell_t l_Lake_Shake_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset(void) {
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__9);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__6));
x_3 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__7);
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
x_10 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10);
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset(void) {
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9(void) {
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
x_6 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__4);
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
x_19 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeedsKind_repr___redArg___closed__9);
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
x_24 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10);
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13(void) {
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
x_8 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__4);
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
x_21 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__7);
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
x_31 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__10);
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
x_41 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprNeeds_repr___redArg___closed__13);
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
x_46 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10, &l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instReprBitset_repr___redArg___closed__10);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_9 = x_1;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_3);
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 3);
lean_dec(x_27);
x_20 = x_1;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 3, x_3);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_3);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_2, 1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_32 = x_1;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_3);
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 3);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 2);
lean_dec(x_50);
x_43 = x_1;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 2, x_3);
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
x_11 = x_2;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_nat_lor(x_3, x_7);
lean_dec(x_7);
x_14 = lean_nat_lor(x_4, x_8);
lean_dec(x_8);
x_15 = lean_nat_lor(x_5, x_9);
lean_dec(x_9);
x_16 = lean_nat_lor(x_6, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 3, x_16);
lean_ctor_set(x_11, 2, x_15);
lean_ctor_set(x_11, 1, x_14);
lean_ctor_set(x_11, 0, x_13);
x_17 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
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
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_9, 0, x_7);
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
lean_ctor_set_uint8(x_13, 0, x_6);
lean_ctor_set_uint8(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_14, 0, x_7);
lean_ctor_set_uint8(x_14, 1, x_7);
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
x_6 = x_21;
x_7 = x_20;
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
x_6 = x_21;
x_7 = x_20;
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2(void) {
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
x_20 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2, &l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27___closed__2);
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
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
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1(void) {
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
x_14 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1, &l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f___closed__1);
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
x_15 = lean_array_uget_borrowed(x_4, x_6);
x_16 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_17 = lean_array_get_borrowed(x_16, x_14, x_2);
x_18 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_17, x_3, x_15);
if (x_18 == 0)
{
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_shiftl(x_20, x_15);
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
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
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
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1_spec__1___redArg(x_2, x_17);
return x_18;
}
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
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_40; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_3, 0);
x_20 = lean_ctor_get_uint8(x_3, 1);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
x_21 = x_3;
x_22 = x_40;
goto block_39;
}
else
{
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_23; 
if (x_20 == 0)
{
lean_dec_ref(x_2);
x_23 = x_20;
goto block_36;
}
else
{
uint8_t x_37; 
lean_inc(x_16);
x_37 = l___private_Lake_CLI_Shake_0__Lake_Shake_isDeclMeta_x27(x_2, x_16);
if (x_37 == 0)
{
x_23 = x_20;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_23 = x_38;
goto block_36;
}
}
block_36:
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_18, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
if (x_22 == 0)
{
x_25 = x_21;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_35, 0, x_19);
x_25 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_ctor_set_uint8(x_25, 1, x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_shiftl(x_27, x_18);
lean_dec(x_18);
x_29 = lean_nat_lor(x_26, x_28);
lean_dec(x_28);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_7, x_25, x_29);
x_31 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_5, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0));
x_8 = x_30;
x_9 = x_25;
x_10 = x_32;
goto block_14;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_8 = x_30;
x_9 = x_25;
x_10 = x_33;
goto block_14;
}
}
}
else
{
lean_del_object(x_21);
lean_dec(x_18);
lean_dec(x_16);
return x_7;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
else
{
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrSet___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2);
x_2 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__0);
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
x_9 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3);
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3(void) {
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
x_7 = lean_array_uget_borrowed(x_2, x_4);
x_21 = lean_ctor_get(x_7, 0);
x_22 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
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
x_24 = lean_array_uget_borrowed(x_4, x_6);
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
lean_inc(x_24);
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
x_18 = x_33;
x_19 = x_31;
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
x_18 = x_34;
x_19 = x_31;
x_20 = x_36;
goto block_22;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, 1, x_28);
x_13 = x_34;
x_14 = x_31;
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
x_13 = x_38;
x_14 = x_31;
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
x_16 = l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr(x_2, x_3, x_15, x_13, x_14);
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
x_21 = lean_array_uget_borrowed(x_3, x_20);
lean_inc(x_21);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_32; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_6 = x_2;
x_7 = x_32;
goto block_31;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_array_get_size(x_1);
x_11 = lean_uint64_of_nat(x_8);
x_12 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_9);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget_borrowed(x_1, x_24);
lean_inc(x_25);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_25);
x_26 = x_6;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_25);
x_26 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_27; 
x_27 = lean_array_uset(x_1, x_24, x_26);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_24; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
x_7 = x_3;
x_8 = x_24;
goto block_23;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = l_Lean_instBEqModuleIdx;
lean_inc(x_16);
lean_inc(x_14);
x_19 = lean_apply_2(x_18, x_14, x_16);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
goto block_13;
}
else
{
uint8_t x_21; 
x_21 = l___private_Lake_CLI_Shake_0__Lake_Shake_instBEqNeedsKind_beq(x_15, x_17);
if (x_21 == 0)
{
goto block_13;
}
else
{
lean_object* x_22; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_6);
return x_22;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_52; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
x_6 = x_1;
x_7 = x_52;
goto block_51;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_array_get_size(x_5);
x_11 = lean_uint64_of_nat(x_8);
x_12 = l___private_Lake_CLI_Shake_0__Lake_Shake_instHashableNeedsKind_hash(x_9);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget_borrowed(x_5, x_24);
lean_inc(x_25);
lean_inc_ref(x_2);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__0___redArg(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
lean_inc(x_25);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_5, x_24, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__1___redArg(x_30);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_28);
x_38 = x_6;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
lean_object* x_41; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_28);
x_41 = x_6;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_30);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_25);
x_44 = lean_box(0);
x_45 = lean_array_uset(x_5, x_24, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__0_spec__2___redArg(x_2, x_3, x_25);
x_47 = lean_array_uset(x_45, x_24, x_46);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_47);
x_48 = x_6;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
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
x_18 = lean_array_uget_borrowed(x_6, x_8);
x_19 = lean_array_get_borrowed(x_17, x_16, x_2);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_19, x_3, x_18);
if (x_20 == 0)
{
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
lean_inc(x_18);
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
x_19 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___lam__0___closed__0));
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
x_10 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__3);
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
x_14 = lean_array_uget_borrowed(x_4, x_6);
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
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_visitExpr(x_2, x_3, x_18, x_15, x_17, x_16);
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
lean_inc(x_14);
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
x_21 = x_31;
x_22 = x_33;
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
x_21 = x_31;
x_22 = x_34;
x_23 = x_36;
goto block_25;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, 1, x_28);
x_16 = x_31;
x_17 = x_34;
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
x_16 = x_31;
x_17 = x_38;
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
x_21 = lean_array_uget_borrowed(x_3, x_20);
lean_inc(x_21);
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
x_12 = lean_array_uget_borrowed(x_2, x_4);
x_22 = lean_ctor_get(x_12, 0);
x_23 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0, &l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__0);
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
x_9 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1, &l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations___closed__1);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_31; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_6 = x_2;
x_7 = x_31;
goto block_30;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_array_get_size(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint64_t x_28; 
x_28 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0);
x_9 = x_28;
goto block_27;
}
else
{
uint64_t x_29; 
x_29 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_9 = x_29;
goto block_27;
}
block_27:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_45; 
x_45 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0);
x_7 = x_45;
goto block_44;
}
else
{
uint64_t x_46; 
x_46 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_7 = x_46;
goto block_44;
}
block_44:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
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
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_41; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_21 = x_1;
x_22 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_19);
x_26 = lean_array_uset(x_5, x_18, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_24);
x_34 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_24);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_32; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
x_10 = x_6;
x_11 = x_32;
goto block_31;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_27; 
x_12 = lean_array_uget_borrowed(x_3, x_5);
x_13 = lean_ctor_get(x_12, 0);
x_14 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_27 = l_Lean_Environment_getModuleIdx_x3f(x_2, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_29 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_28);
x_15 = x_29;
goto block_26;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_15 = x_30;
goto block_26;
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_17 = lean_array_push(x_8, x_15);
x_18 = lean_array_get_borrowed(x_14, x_16, x_15);
x_19 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_9, x_12, x_15, x_18);
lean_dec(x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_17);
x_20 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_19);
x_20 = x_25;
goto block_24;
}
block_24:
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_5 = x_22;
x_6 = x_20;
goto _start;
}
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_33; 
x_7 = l_Lean_instInhabitedModuleData_default;
x_8 = lean_array_get_borrowed(x_7, x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0));
x_11 = lean_array_size(x_9);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(x_5, x_3, x_9, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
x_23 = x_5;
x_24 = x_33;
goto block_32;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_push(x_16, x_14);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_25);
x_26 = x_23;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_18);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_20);
lean_ctor_set(x_31, 6, x_21);
lean_ctor_set(x_31, 7, x_22);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_4 = x_28;
x_5 = x_26;
goto _start;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_33; 
x_7 = l_Lean_instInhabitedModuleData_default;
x_8 = lean_array_get_borrowed(x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg___closed__0));
x_11 = lean_array_size(x_9);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__1(x_5, x_1, x_9, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
x_23 = x_5;
x_24 = x_33;
goto block_32;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_23 = lean_box(0);
x_24 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_push(x_16, x_14);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_25);
x_26 = x_23;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_18);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_20);
lean_ctor_set(x_31, 6, x_21);
lean_ctor_set(x_31, 7, x_22);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
x_29 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__2_spec__3___redArg(x_2, x_3, x_1, x_28, x_26);
return x_29;
}
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_27; 
x_5 = lean_ctor_get(x_2, 0);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_6 = x_2;
x_7 = x_27;
goto block_26;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_11);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_9, x_9);
if (x_15 == 0)
{
if (x_10 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_16);
x_17 = x_6;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_del_object(x_6);
x_20 = 0;
x_21 = lean_usize_of_nat(x_9);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_5, x_20, x_21, x_3, x_4);
lean_dec_ref(x_5);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_del_object(x_6);
x_23 = 0;
x_24 = lean_usize_of_nat(x_9);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__12___redArg(x_1, x_5, x_23, x_24, x_3, x_4);
lean_dec_ref(x_5);
return x_25;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_2);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3_spec__6_spec__8_spec__10_spec__13___redArg(x_1, x_28, x_29, x_30, x_3, x_4);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
return x_31;
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
x_19 = lean_array_uget_borrowed(x_2, x_3);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_1);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_apply_4(x_1, x_5, x_20, x_21, x_6);
x_13 = x_22;
goto block_17;
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
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
x_8 = lean_array_uget_borrowed(x_2, x_3);
x_9 = lean_box(0);
lean_inc(x_8);
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__1));
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2, &l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__3));
x_6 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_7 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2, &l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr___closed__2);
lean_inc_ref(x_1);
x_36 = l_Lean_Environment_constants(x_1);
x_37 = l_Lean_SMap_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__3___redArg(x_36, x_2, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_8 = x_38;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_8 = x_40;
goto block_35;
}
block_35:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
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
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 3);
x_23 = lean_ctor_get(x_19, 4);
x_24 = lean_ctor_get(x_19, 5);
x_25 = lean_ctor_get(x_19, 6);
x_26 = lean_ctor_get(x_19, 7);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_19, 2);
lean_dec(x_34);
x_27 = x_19;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
lean_inc_ref(x_21);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_21);
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_22);
lean_ctor_set(x_31, 4, x_23);
lean_ctor_set(x_31, 5, x_24);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_name_eq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_51; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
x_6 = x_1;
x_7 = x_51;
goto block_50;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_array_get_size(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_48; 
x_48 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0___redArg___closed__0);
x_9 = x_48;
goto block_47;
}
else
{
uint64_t x_49; 
x_49 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_9 = x_49;
goto block_47;
}
block_47:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getDepConstName_x3f_spec__0_spec__0___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv_spec__0_spec__0___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0_spec__0___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_3);
x_8 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0));
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
x_14 = x_11;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_12, x_3);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_13);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_17);
return x_18;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove___closed__0));
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
x_14 = x_11;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_13, x_3);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
x_17 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_16);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Shake_0__Lake_Shake_Edits_remove_spec__0___redArg(x_1, x_2, x_17);
return x_18;
}
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
x_8 = lean_array_uget_borrowed(x_2, x_3);
lean_inc_ref(x_1);
lean_inc(x_8);
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_2, 0);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
x_5 = x_2;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_4);
x_9 = lean_box(0);
x_10 = lean_nat_dec_lt(x_7, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_9);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_9);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_8, x_8);
if (x_14 == 0)
{
if (x_10 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_9);
x_15 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_9);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_del_object(x_5);
x_18 = 0;
x_19 = lean_usize_of_nat(x_8);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_4, x_18, x_19, x_9);
lean_dec_ref(x_4);
return x_20;
}
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
lean_del_object(x_5);
x_21 = 0;
x_22 = lean_usize_of_nat(x_8);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_4, x_21, x_22, x_9);
lean_dec_ref(x_4);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_47; 
x_26 = lean_ctor_get(x_2, 0);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
x_27 = x_2;
x_28 = x_47;
goto block_46;
}
else
{
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_26);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_31);
x_33 = x_27;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_30, x_30);
if (x_36 == 0)
{
if (x_32 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_31);
x_37 = x_27;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_31);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
lean_del_object(x_27);
x_40 = 0;
x_41 = lean_usize_of_nat(x_30);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_26, x_40, x_41, x_31);
lean_dec_ref(x_26);
return x_42;
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
lean_del_object(x_27);
x_43 = 0;
x_44 = lean_usize_of_nat(x_30);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_26, x_43, x_44, x_31);
lean_dec_ref(x_26);
return x_45;
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
x_8 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_8);
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
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0(void) {
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
x_7 = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4___closed__0);
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
lean_object* x_18; uint8_t x_19; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_17, 0);
lean_dec(x_40);
x_18 = x_17;
x_19 = x_39;
goto block_38;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
x_22 = lean_array_get_size(x_6);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_23);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_22, x_22);
if (x_28 == 0)
{
if (x_24 == 0)
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_23);
x_29 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_23);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
lean_del_object(x_18);
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_usize_of_nat(x_22);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_32, x_33, x_23);
lean_dec_ref(x_6);
return x_34;
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
lean_del_object(x_18);
x_35 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_36 = lean_usize_of_nat(x_22);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__4_spec__6(x_1, x_6, x_35, x_36, x_23);
lean_dec_ref(x_6);
return x_37;
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
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_62; 
x_41 = lean_ctor_get(x_2, 0);
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
x_42 = x_2;
x_43 = x_62;
goto block_61;
}
else
{
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_usize_to_nat(x_3);
x_45 = lean_array_get_size(x_41);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_44);
lean_dec_ref(x_41);
lean_dec_ref(x_1);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_46);
x_48 = x_42;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_46);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_45, x_45);
if (x_51 == 0)
{
if (x_47 == 0)
{
lean_object* x_52; 
lean_dec(x_44);
lean_dec_ref(x_41);
lean_dec_ref(x_1);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_46);
x_52 = x_42;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_46);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
lean_del_object(x_42);
x_55 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_56 = lean_usize_of_nat(x_45);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_41, x_55, x_56, x_46);
lean_dec_ref(x_41);
return x_57;
}
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
lean_del_object(x_42);
x_58 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_59 = lean_usize_of_nat(x_45);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_41, x_58, x_59, x_46);
lean_dec_ref(x_41);
return x_60;
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
lean_object* x_7; uint8_t x_8; uint8_t x_27; 
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_6, 0);
lean_dec(x_28);
x_7 = x_6;
x_8 = x_27;
goto block_26;
}
else
{
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_5);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_10, x_10);
if (x_16 == 0)
{
if (x_12 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_17 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_11);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_del_object(x_7);
x_20 = 0;
x_21 = lean_usize_of_nat(x_10);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_20, x_21, x_11);
lean_dec_ref(x_5);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_del_object(x_7);
x_23 = 0;
x_24 = lean_usize_of_nat(x_10);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_5, x_23, x_24, x_11);
lean_dec_ref(x_5);
return x_25;
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
lean_object* x_14; uint8_t x_15; uint8_t x_33; 
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_13, 0);
lean_dec(x_34);
x_14 = x_13;
x_15 = x_33;
goto block_32;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_get_size(x_8);
x_17 = lean_box(0);
x_18 = lean_nat_dec_lt(x_5, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_16, x_16);
if (x_22 == 0)
{
if (x_18 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_23 = x_14;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_17);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_del_object(x_14);
x_26 = 0;
x_27 = lean_usize_of_nat(x_16);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_26, x_27, x_17);
lean_dec_ref(x_8);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_del_object(x_14);
x_29 = 0;
x_30 = lean_usize_of_nat(x_16);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_29, x_30, x_17);
lean_dec_ref(x_8);
return x_31;
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec_ref(x_7);
x_35 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_36 = lean_array_get_size(x_8);
x_37 = lean_box(0);
x_38 = lean_nat_dec_lt(x_35, x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_36, x_36);
if (x_40 == 0)
{
if (x_38 == 0)
{
lean_object* x_41; 
lean_dec(x_35);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = lean_usize_of_nat(x_36);
x_44 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_42, x_43, x_37);
lean_dec_ref(x_8);
return x_44;
}
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_46 = lean_usize_of_nat(x_36);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__5(x_1, x_8, x_45, x_46, x_37);
lean_dec_ref(x_8);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
x_48 = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2_spec__3_spec__6(x_1, x_2);
return x_48;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_73; 
x_8 = lean_ctor_get(x_7, 0);
x_73 = !lean_is_exclusive(x_7);
if (x_73 == 0)
{
x_9 = x_7;
x_10 = x_73;
goto block_72;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_71; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
x_13 = x_8;
x_14 = x_71;
goto block_70;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_29; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
x_44 = l_Lean_MessageLog_toList(x_43);
x_45 = l_List_isEmpty___redArg(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_del_object(x_13);
lean_dec(x_11);
lean_del_object(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_46 = lean_box(x_45);
x_47 = lean_alloc_closure((void*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___lam__0___boxed), 3, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = l_Lean_MessageLog_forM___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__2(x_43, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_48, 0);
lean_dec(x_57);
x_49 = x_48;
x_50 = x_56;
goto block_55;
}
else
{
lean_dec(x_48);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; 
x_51 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString___closed__1));
if (x_50 == 0)
{
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
x_58 = lean_ctor_get(x_48, 0);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
x_59 = x_48;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
uint8_t x_66; lean_object* x_67; 
lean_dec(x_43);
x_66 = 0;
x_67 = l_Lean_Syntax_getTailPos_x3f(x_11, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_42, 0);
lean_inc(x_68);
lean_dec(x_42);
x_29 = x_68;
goto block_41;
}
else
{
lean_object* x_69; 
lean_dec(x_42);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_29 = x_69;
goto block_41;
}
}
block_28:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_String_Slice_Pos_next_x21(x_15, x_18);
lean_dec(x_18);
lean_dec_ref(x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_19);
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_19);
x_20 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_22);
x_23 = x_9;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
block_41:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_string_utf8_byte_size(x_31);
lean_inc_ref(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_String_Slice_pos_x21(x_34, x_29);
lean_dec(x_29);
lean_inc(x_35);
lean_inc_ref(x_31);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_box(0);
x_38 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__0___redArg(x_36, x_35, x_31, x_32, x_37);
lean_dec_ref(x_31);
lean_dec_ref(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_nat_sub(x_33, x_35);
x_15 = x_34;
x_16 = x_35;
x_17 = x_39;
goto block_28;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_15 = x_34;
x_16 = x_35;
x_17 = x_40;
goto block_28;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_7, 0);
x_81 = !lean_is_exclusive(x_7);
if (x_81 == 0)
{
x_75 = x_7;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_7);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_6 = lean_ctor_get(x_5, 0);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
x_7 = x_5;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_del_object(x_7);
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_IO_FS_readFile(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString(x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_14 = x_10;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
x_21 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__1));
x_22 = 1;
x_23 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_25);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_5, 0);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
x_32 = x_5;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
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
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0(void) {
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
x_3 = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0, &l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0___closed__0);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; lean_object* x_22; lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__4));
lean_inc(x_1);
x_37 = l_Lean_Syntax_isOfKind(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_39 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_40 = lean_unsigned_to_nat(391u);
x_41 = lean_unsigned_to_nat(11u);
x_42 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_43 = lean_box(0);
x_44 = l_Lean_Syntax_formatStx(x_1, x_43, x_37);
x_45 = l_Std_Format_defWidth;
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Std_Format_pretty(x_44, x_45, x_46, x_46);
x_48 = lean_string_append(x_42, x_47);
lean_dec_ref(x_47);
x_49 = l_mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_48);
lean_dec_ref(x_48);
x_50 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_88; uint8_t x_89; 
x_51 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Syntax_getArg(x_1, x_51);
x_89 = l_Lean_Syntax_isNone(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_unsigned_to_nat(1u);
lean_inc(x_88);
x_91 = l_Lean_Syntax_matchesNull(x_88, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
x_92 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_93 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_94 = lean_unsigned_to_nat(391u);
x_95 = lean_unsigned_to_nat(11u);
x_96 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_97 = lean_box(0);
x_98 = l_Lean_Syntax_formatStx(x_1, x_97, x_91);
x_99 = l_Std_Format_defWidth;
x_100 = l_Std_Format_pretty(x_98, x_99, x_51, x_51);
x_101 = lean_string_append(x_96, x_100);
lean_dec_ref(x_100);
x_102 = l_mkPanicMessageWithDecl(x_92, x_93, x_94, x_95, x_101);
lean_dec_ref(x_101);
x_103 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Lean_Syntax_getArg(x_88, x_51);
lean_dec(x_88);
x_105 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__11));
lean_inc(x_104);
x_106 = l_Lean_Syntax_isOfKind(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_104);
x_107 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_108 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_109 = lean_unsigned_to_nat(391u);
x_110 = lean_unsigned_to_nat(11u);
x_111 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_112 = lean_box(0);
x_113 = l_Lean_Syntax_formatStx(x_1, x_112, x_106);
x_114 = l_Std_Format_defWidth;
x_115 = l_Std_Format_pretty(x_113, x_114, x_51, x_51);
x_116 = lean_string_append(x_111, x_115);
lean_dec_ref(x_115);
x_117 = l_mkPanicMessageWithDecl(x_107, x_108, x_109, x_110, x_116);
lean_dec_ref(x_116);
x_118 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_117);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Syntax_getArg(x_104, x_51);
lean_dec(x_104);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_52 = x_120;
goto block_87;
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_88);
x_121 = lean_box(0);
x_52 = x_121;
goto block_87;
}
block_87:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
x_55 = l_Lean_Syntax_isNone(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_inc(x_54);
x_56 = l_Lean_Syntax_matchesNull(x_54, x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_54);
lean_dec(x_52);
x_57 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_58 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_59 = lean_unsigned_to_nat(391u);
x_60 = lean_unsigned_to_nat(11u);
x_61 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_62 = lean_box(0);
x_63 = l_Lean_Syntax_formatStx(x_1, x_62, x_56);
x_64 = l_Std_Format_defWidth;
x_65 = l_Std_Format_pretty(x_63, x_64, x_51, x_51);
x_66 = lean_string_append(x_61, x_65);
lean_dec_ref(x_65);
x_67 = l_mkPanicMessageWithDecl(x_57, x_58, x_59, x_60, x_66);
lean_dec_ref(x_66);
x_68 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Syntax_getArg(x_54, x_51);
lean_dec(x_54);
x_70 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__9));
lean_inc(x_69);
x_71 = l_Lean_Syntax_isOfKind(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_69);
lean_dec(x_52);
x_72 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_73 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__6));
x_74 = lean_unsigned_to_nat(391u);
x_75 = lean_unsigned_to_nat(11u);
x_76 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__7));
x_77 = lean_box(0);
x_78 = l_Lean_Syntax_formatStx(x_1, x_77, x_71);
x_79 = l_Std_Format_defWidth;
x_80 = l_Std_Format_pretty(x_78, x_79, x_51, x_51);
x_81 = lean_string_append(x_76, x_80);
lean_dec_ref(x_80);
x_82 = l_mkPanicMessageWithDecl(x_72, x_73, x_74, x_75, x_81);
lean_dec_ref(x_81);
x_83 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader_spec__0(x_82);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Syntax_getArg(x_69, x_51);
lean_dec(x_69);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_21 = x_52;
x_22 = x_85;
goto block_35;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_54);
x_86 = lean_box(0);
x_21 = x_52;
x_22 = x_86;
goto block_35;
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
block_20:
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_13 = x_9;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
x_2 = x_8;
x_3 = x_10;
x_4 = x_15;
goto block_7;
}
}
}
}
block_35:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_8 = x_25;
x_9 = x_22;
x_10 = x_26;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_27 = lean_ctor_get(x_21, 0);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
x_28 = x_21;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_8 = x_25;
x_9 = x_22;
x_10 = x_30;
goto block_20;
}
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
uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__1));
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_21 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_22 = lean_unsigned_to_nat(396u);
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
x_137 = lean_unsigned_to_nat(396u);
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
x_152 = lean_unsigned_to_nat(396u);
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
x_42 = lean_unsigned_to_nat(396u);
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
x_11 = x_34;
x_12 = x_39;
x_13 = x_54;
x_14 = x_35;
x_15 = x_55;
goto block_17;
}
else
{
lean_dec_ref(x_36);
x_11 = x_34;
x_12 = x_39;
x_13 = x_54;
x_14 = x_35;
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
x_63 = l_Lean_Syntax_matchesNull(x_61, x_57);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_64 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_65 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_66 = lean_unsigned_to_nat(396u);
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
lean_dec(x_58);
x_79 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader___closed__5));
x_80 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport___closed__2));
x_81 = lean_unsigned_to_nat(396u);
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
x_35 = x_58;
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
x_35 = x_58;
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
x_102 = lean_unsigned_to_nat(396u);
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
x_117 = lean_unsigned_to_nat(396u);
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
x_57 = x_96;
x_58 = x_95;
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
x_57 = x_96;
x_58 = x_95;
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
lean_ctor_set(x_8, 0, x_5);
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
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_4);
return x_9;
}
}
block_17:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_16; 
x_16 = 0;
x_2 = x_15;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_16;
goto block_10;
}
else
{
lean_dec_ref(x_14);
x_2 = x_15;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_12;
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
lean_dec_ref(x_11);
lean_dec(x_12);
lean_dec_ref(x_4);
return x_7;
}
else
{
uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_15 = 0;
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
x_17 = lean_ctor_get_uint8(x_4, 1);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
x_18 = x_4;
x_19 = x_29;
goto block_28;
}
else
{
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_array_get_borrowed(x_13, x_9, x_12);
x_21 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_13, x_16, x_12, x_20);
lean_dec(x_12);
lean_dec_ref(x_16);
if (x_19 == 0)
{
x_22 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_27, 1, x_17);
x_22 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_23; 
lean_ctor_set_uint8(x_22, 0, x_14);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_21, x_22, x_3);
lean_dec_ref(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_24, 0, x_14);
lean_ctor_set_uint8(x_24, 1, x_15);
x_25 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_21, x_24, x_3);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
if (x_25 == 0)
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
lean_dec_ref(x_21);
if (x_23 == 0)
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
x_7 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_7);
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
x_10 = lean_array_uget_borrowed(x_3, x_4);
x_11 = lean_array_get_borrowed(x_9, x_8, x_2);
lean_inc(x_10);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_171; lean_object* x_172; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_202; lean_object* x_203; lean_object* x_213; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_array_uget_borrowed(x_6, x_8);
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_55 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_56 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
x_202 = 0;
x_213 = l_Lean_Environment_getModuleIdx_x3f(x_22, x_53);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_215 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_214);
x_203 = x_215;
goto block_212;
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
lean_dec_ref(x_213);
x_203 = x_216;
goto block_212;
}
block_28:
{
lean_object* x_27; 
lean_inc(x_23);
x_27 = lean_array_push(x_24, x_23);
x_12 = x_27;
x_13 = x_25;
x_14 = lean_box(0);
goto block_18;
}
block_47:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_34, x_29);
lean_dec_ref(x_29);
x_36 = lean_string_append(x_30, x_35);
lean_dec_ref(x_35);
x_37 = lean_string_append(x_36, x_31);
lean_dec_ref(x_31);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_39 = lean_ctor_get(x_38, 0);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
x_40 = x_38;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
block_52:
{
lean_object* x_51; 
lean_inc(x_23);
x_51 = lean_array_push(x_48, x_23);
x_12 = x_51;
x_13 = x_49;
x_14 = lean_box(0);
goto block_18;
}
block_67:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_string_append(x_60, x_62);
lean_dec_ref(x_62);
x_64 = lean_string_append(x_63, x_58);
lean_dec_ref(x_58);
if (x_54 == 0)
{
lean_object* x_65; 
x_65 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_29 = x_57;
x_30 = x_59;
x_31 = x_61;
x_32 = x_64;
x_33 = x_65;
goto block_47;
}
else
{
lean_object* x_66; 
x_66 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_29 = x_57;
x_30 = x_59;
x_31 = x_61;
x_32 = x_64;
x_33 = x_66;
goto block_47;
}
}
block_87:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_string_append(x_68, x_71);
lean_dec_ref(x_71);
lean_inc(x_53);
x_73 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_53, x_69);
x_74 = lean_string_append(x_72, x_73);
lean_dec_ref(x_73);
x_75 = lean_string_append(x_70, x_74);
lean_dec_ref(x_74);
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__0));
x_77 = lean_string_append(x_75, x_76);
x_78 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_79 = lean_ctor_get(x_78, 0);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
x_80 = x_78;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
block_97:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_string_append(x_88, x_91);
lean_dec_ref(x_91);
x_93 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_94 = lean_string_append(x_92, x_93);
if (x_54 == 0)
{
lean_object* x_95; 
x_95 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_68 = x_94;
x_69 = x_89;
x_70 = x_90;
x_71 = x_95;
goto block_87;
}
else
{
lean_object* x_96; 
x_96 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_68 = x_94;
x_69 = x_89;
x_70 = x_90;
x_71 = x_96;
goto block_87;
}
}
block_103:
{
if (x_56 == 0)
{
lean_object* x_101; 
x_101 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_88 = x_100;
x_89 = x_98;
x_90 = x_99;
x_91 = x_101;
goto block_97;
}
else
{
lean_object* x_102; 
x_102 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_88 = x_100;
x_89 = x_98;
x_90 = x_99;
x_91 = x_102;
goto block_97;
}
}
block_123:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_string_append(x_105, x_107);
lean_dec_ref(x_107);
lean_inc(x_53);
x_109 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_53, x_106);
x_110 = lean_string_append(x_108, x_109);
lean_dec_ref(x_109);
x_111 = lean_string_append(x_104, x_110);
lean_dec_ref(x_110);
x_112 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__1));
x_113 = lean_string_append(x_111, x_112);
x_114 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_114);
x_48 = x_9;
x_49 = x_10;
x_50 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_115 = lean_ctor_get(x_114, 0);
x_122 = !lean_is_exclusive(x_114);
if (x_122 == 0)
{
x_116 = x_114;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
block_133:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_string_append(x_125, x_127);
lean_dec_ref(x_127);
x_129 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_130 = lean_string_append(x_128, x_129);
if (x_54 == 0)
{
lean_object* x_131; 
x_131 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_104 = x_124;
x_105 = x_130;
x_106 = x_126;
x_107 = x_131;
goto block_123;
}
else
{
lean_object* x_132; 
x_132 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_104 = x_124;
x_105 = x_130;
x_106 = x_126;
x_107 = x_132;
goto block_123;
}
}
block_139:
{
if (x_56 == 0)
{
lean_object* x_137; 
x_137 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_124 = x_134;
x_125 = x_136;
x_126 = x_135;
x_127 = x_137;
goto block_133;
}
else
{
lean_object* x_138; 
x_138 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_124 = x_134;
x_125 = x_136;
x_126 = x_135;
x_127 = x_138;
goto block_133;
}
}
block_154:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_string_append(x_140, x_144);
lean_dec_ref(x_144);
lean_inc(x_53);
x_146 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_53, x_143);
x_147 = lean_string_append(x_145, x_146);
lean_inc_ref(x_142);
x_148 = lean_string_append(x_142, x_147);
lean_dec_ref(x_147);
x_149 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__2));
x_150 = lean_string_append(x_148, x_149);
x_151 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_56 == 0)
{
lean_object* x_152; 
x_152 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_57 = x_146;
x_58 = x_141;
x_59 = x_150;
x_60 = x_151;
x_61 = x_142;
x_62 = x_152;
goto block_67;
}
else
{
lean_object* x_153; 
x_153 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_57 = x_146;
x_58 = x_141;
x_59 = x_150;
x_60 = x_151;
x_61 = x_142;
x_62 = x_153;
goto block_67;
}
}
block_164:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_string_append(x_155, x_158);
lean_dec_ref(x_158);
x_160 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_161 = lean_string_append(x_159, x_160);
if (x_54 == 0)
{
lean_object* x_162; 
x_162 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_140 = x_161;
x_141 = x_160;
x_142 = x_156;
x_143 = x_157;
x_144 = x_162;
goto block_154;
}
else
{
lean_object* x_163; 
x_163 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_140 = x_161;
x_141 = x_160;
x_142 = x_156;
x_143 = x_157;
x_144 = x_163;
goto block_154;
}
}
block_170:
{
if (x_56 == 0)
{
lean_object* x_168; 
x_168 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_155 = x_167;
x_156 = x_165;
x_157 = x_166;
x_158 = x_168;
goto block_164;
}
else
{
lean_object* x_169; 
x_169 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_155 = x_167;
x_156 = x_165;
x_157 = x_166;
x_158 = x_169;
goto block_164;
}
}
block_186:
{
uint8_t x_173; lean_object* x_174; uint8_t x_175; uint8_t x_185; 
x_173 = lean_ctor_get_uint8(x_172, 1);
x_185 = !lean_is_exclusive(x_172);
if (x_185 == 0)
{
x_174 = x_172;
x_175 = x_185;
goto block_184;
}
else
{
lean_dec(x_172);
x_174 = lean_box(0);
x_175 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_176; 
if (x_175 == 0)
{
x_176 = x_174;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_183, 1, x_173);
x_176 = x_183;
goto block_182;
}
block_182:
{
uint8_t x_177; 
lean_ctor_set_uint8(x_176, 0, x_2);
x_177 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_3, x_176, x_171);
lean_dec(x_171);
lean_dec_ref(x_176);
if (x_177 == 0)
{
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_178; 
x_178 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
if (x_178 == 0)
{
x_24 = x_9;
x_25 = x_10;
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_179; 
x_179 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_55 == 0)
{
lean_object* x_180; 
x_180 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_165 = x_179;
x_166 = x_178;
x_167 = x_180;
goto block_170;
}
else
{
lean_object* x_181; 
x_181 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_165 = x_179;
x_166 = x_178;
x_167 = x_181;
goto block_170;
}
}
}
}
}
}
block_191:
{
if (x_190 == 0)
{
lean_dec_ref(x_188);
lean_dec(x_187);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
if (x_54 == 0)
{
x_171 = x_187;
x_172 = x_188;
goto block_186;
}
else
{
if (x_189 == 0)
{
lean_dec_ref(x_188);
lean_dec(x_187);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
x_171 = x_187;
x_172 = x_188;
goto block_186;
}
}
}
}
block_201:
{
uint8_t x_195; 
x_195 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_5, x_193, x_192);
if (x_195 == 0)
{
uint8_t x_196; 
lean_dec_ref(x_193);
lean_dec(x_192);
x_196 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
if (x_196 == 0)
{
x_48 = x_9;
x_49 = x_10;
x_50 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_197; 
x_197 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_55 == 0)
{
lean_object* x_198; 
x_198 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_134 = x_197;
x_135 = x_196;
x_136 = x_198;
goto block_139;
}
else
{
lean_object* x_199; 
x_199 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_134 = x_197;
x_135 = x_196;
x_136 = x_199;
goto block_139;
}
}
}
else
{
uint8_t x_200; 
x_200 = lean_ctor_get_uint8(x_193, 0);
if (x_200 == 0)
{
x_187 = x_192;
x_188 = x_193;
x_189 = x_194;
x_190 = x_195;
goto block_191;
}
else
{
x_187 = x_192;
x_188 = x_193;
x_189 = x_194;
x_190 = x_194;
goto block_191;
}
}
}
block_212:
{
uint8_t x_204; uint8_t x_205; lean_object* x_206; 
x_204 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_205 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
x_206 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
if (x_204 == 0)
{
x_192 = x_203;
x_193 = x_206;
x_194 = x_202;
goto block_201;
}
else
{
uint8_t x_207; 
x_207 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_3, x_206, x_203);
if (x_207 == 0)
{
x_192 = x_203;
x_193 = x_206;
x_194 = x_207;
goto block_201;
}
else
{
if (x_205 == 0)
{
lean_dec_ref(x_206);
lean_dec(x_203);
x_12 = x_9;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_208; 
x_208 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_5, x_206, x_203);
lean_dec(x_203);
lean_dec_ref(x_206);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_55 == 0)
{
lean_object* x_210; 
x_210 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_98 = x_205;
x_99 = x_209;
x_100 = x_210;
goto block_103;
}
else
{
lean_object* x_211; 
x_211 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_98 = x_205;
x_99 = x_209;
x_100 = x_211;
goto block_103;
}
}
else
{
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
x_33 = lean_array_uget_borrowed(x_5, x_7);
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
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_33, 0);
if (x_35 == 0)
{
x_24 = x_35;
goto block_31;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
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
static size_t _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
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
x_14 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
x_15 = lean_usize_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0);
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
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_instBEqImport_beq(x_1, x_6);
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
x_19 = lean_array_uget_borrowed(x_3, x_5);
x_20 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_19, 0);
x_24 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_29 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
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
x_9 = x_27;
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_152; 
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 0);
x_152 = !lean_is_exclusive(x_8);
if (x_152 == 0)
{
x_31 = x_8;
x_32 = x_152;
goto block_151;
}
else
{
lean_inc(x_29);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_box(0);
x_32 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_150; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
x_150 = !lean_is_exclusive(x_29);
if (x_150 == 0)
{
x_35 = x_29;
x_36 = x_150;
goto block_149;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_141; lean_object* x_145; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_array_uget(x_5, x_7);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
x_42 = lean_ctor_get_uint8(x_39, sizeof(void*)*1 + 1);
x_43 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_145 = l_Lean_Environment_getModuleIdx_x3f(x_37, x_40);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_147 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_146);
x_141 = x_147;
goto block_144;
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec_ref(x_145);
x_141 = x_148;
goto block_144;
}
block_68:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = lean_array_get_borrowed(x_43, x_38, x_47);
x_54 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_50, x_46, x_47, x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_shiftl(x_56, x_47);
lean_dec(x_47);
x_58 = lean_nat_lor(x_55, x_57);
lean_dec(x_57);
x_59 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_49, x_45, x_58);
lean_dec_ref(x_45);
x_60 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_3, x_46);
if (x_60 == 0)
{
if (x_44 == 0)
{
lean_dec_ref(x_46);
lean_del_object(x_35);
lean_del_object(x_31);
x_18 = lean_box(0);
x_19 = x_51;
x_20 = x_48;
x_21 = x_59;
x_22 = x_54;
goto block_25;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_array_push(x_48, x_46);
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_54);
lean_ctor_set(x_35, 0, x_59);
x_62 = x_35;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_54);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_62);
lean_ctor_set(x_31, 0, x_61);
x_63 = x_31;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
x_11 = x_63;
x_12 = x_51;
x_13 = lean_box(0);
goto block_17;
}
}
}
}
else
{
lean_dec_ref(x_46);
lean_del_object(x_35);
lean_del_object(x_31);
x_18 = lean_box(0);
x_19 = x_51;
x_20 = x_48;
x_21 = x_59;
x_22 = x_54;
goto block_25;
}
}
block_92:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_string_append(x_74, x_76);
lean_dec_ref(x_76);
x_78 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_40, x_69);
x_79 = lean_string_append(x_77, x_78);
lean_dec_ref(x_78);
x_80 = lean_string_append(x_72, x_79);
lean_dec_ref(x_79);
x_81 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11___closed__0));
x_82 = lean_string_append(x_80, x_81);
x_83 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_44 = x_71;
x_45 = x_70;
x_46 = x_73;
x_47 = x_75;
x_48 = x_30;
x_49 = x_33;
x_50 = x_34;
x_51 = x_9;
x_52 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_75);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_del_object(x_31);
lean_dec(x_30);
lean_dec_ref(x_9);
x_84 = lean_ctor_get(x_83, 0);
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
x_85 = x_83;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
block_104:
{
lean_object* x_100; lean_object* x_101; 
x_100 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_101 = lean_string_append(x_99, x_100);
if (x_41 == 0)
{
lean_object* x_102; 
x_102 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_69 = x_93;
x_70 = x_96;
x_71 = x_95;
x_72 = x_94;
x_73 = x_97;
x_74 = x_101;
x_75 = x_98;
x_76 = x_102;
goto block_92;
}
else
{
lean_object* x_103; 
x_103 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_69 = x_93;
x_70 = x_96;
x_71 = x_95;
x_72 = x_94;
x_73 = x_97;
x_74 = x_101;
x_75 = x_98;
x_76 = x_103;
goto block_92;
}
}
block_140:
{
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; uint8_t x_129; 
lean_inc(x_40);
x_129 = !lean_is_exclusive(x_39);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_39, 0);
lean_dec(x_130);
x_108 = x_39;
x_109 = x_129;
goto block_128;
}
else
{
lean_dec(x_39);
x_108 = lean_box(0);
x_109 = x_129;
goto block_128;
}
block_128:
{
uint8_t x_110; 
x_110 = l_Lean_Name_isPrefixOf(x_2, x_40);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_del_object(x_108);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_40);
lean_del_object(x_35);
lean_del_object(x_31);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_33);
lean_ctor_set(x_111, 1, x_34);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_30);
lean_ctor_set(x_112, 1, x_111);
x_11 = x_112;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_113; lean_object* x_114; uint8_t x_115; uint8_t x_127; 
x_113 = lean_ctor_get_uint8(x_105, 0);
x_127 = !lean_is_exclusive(x_105);
if (x_127 == 0)
{
x_114 = x_105;
x_115 = x_127;
goto block_126;
}
else
{
lean_dec(x_105);
x_114 = lean_box(0);
x_115 = x_127;
goto block_126;
}
block_126:
{
uint8_t x_116; lean_object* x_117; 
x_116 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
lean_inc(x_40);
if (x_109 == 0)
{
x_117 = x_108;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_125, 0, x_40);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_41);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 1, x_42);
x_117 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_118; 
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 2, x_107);
if (x_115 == 0)
{
x_118 = x_114;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_123, 0, x_113);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_ctor_set_uint8(x_118, 1, x_107);
if (x_116 == 0)
{
lean_dec(x_40);
x_44 = x_110;
x_45 = x_118;
x_46 = x_117;
x_47 = x_106;
x_48 = x_30;
x_49 = x_33;
x_50 = x_34;
x_51 = x_9;
x_52 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_119; 
x_119 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_42 == 0)
{
lean_object* x_120; 
x_120 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_93 = x_116;
x_94 = x_119;
x_95 = x_110;
x_96 = x_118;
x_97 = x_117;
x_98 = x_106;
x_99 = x_120;
goto block_104;
}
else
{
lean_object* x_121; 
x_121 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_93 = x_116;
x_94 = x_119;
x_95 = x_110;
x_96 = x_118;
x_97 = x_117;
x_98 = x_106;
x_99 = x_121;
goto block_104;
}
}
}
}
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_del_object(x_35);
lean_del_object(x_31);
x_131 = lean_array_get_borrowed(x_43, x_38, x_106);
x_132 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_34, x_39, x_106, x_131);
lean_dec(x_39);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_shiftl(x_134, x_106);
lean_dec(x_106);
x_136 = lean_nat_lor(x_133, x_135);
lean_dec(x_135);
x_137 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_33, x_105, x_136);
lean_dec_ref(x_105);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_30);
lean_ctor_set(x_139, 1, x_138);
x_11 = x_139;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_144:
{
lean_object* x_142; uint8_t x_143; 
x_142 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_39);
x_143 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_33, x_142, x_141);
if (x_143 == 0)
{
x_105 = x_142;
x_106 = x_141;
x_107 = x_41;
goto block_140;
}
else
{
x_105 = x_142;
x_106 = x_141;
x_107 = x_143;
goto block_140;
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
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_11 = x_24;
x_12 = x_19;
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
x_13 = lean_array_uget_borrowed(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
x_15 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_23 = l_Lean_Environment_getModuleIdx_x3f(x_11, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_332; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 0);
x_332 = !lean_is_exclusive(x_10);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_10, 1);
lean_dec(x_333);
x_26 = x_10;
x_27 = x_332;
goto block_331;
}
else
{
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_329; 
x_28 = lean_ctor_get(x_23, 0);
x_329 = !lean_is_exclusive(x_23);
if (x_329 == 0)
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_23, 1);
lean_dec(x_330);
x_29 = x_23;
x_30 = x_329;
goto block_328;
}
else
{
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = x_329;
goto block_328;
}
block_328:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_327; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_327 = !lean_is_exclusive(x_24);
if (x_327 == 0)
{
x_33 = x_24;
x_34 = x_327;
goto block_326;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_box(0);
x_34 = x_327;
goto block_326;
}
block_326:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_array_uget_borrowed(x_7, x_9);
x_46 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_45, x_1);
if (x_46 == 0)
{
goto block_44;
}
else
{
uint8_t x_47; 
x_47 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_31, x_45, x_1);
if (x_47 == 0)
{
if (x_46 == 0)
{
goto block_44;
}
else
{
uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get_uint8(x_45, 0);
x_49 = lean_ctor_get_uint8(x_45, 1);
x_50 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_50, 0, x_46);
lean_ctor_set_uint8(x_50, 1, x_49);
x_51 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_31, x_50, x_1);
lean_dec_ref(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_del_object(x_33);
lean_del_object(x_29);
lean_del_object(x_26);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 7);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
x_56 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 3);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
x_58 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_158 = lean_box(0);
x_288 = lean_array_get_borrowed(x_158, x_54, x_1);
lean_inc(x_288);
x_289 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*1, x_51);
lean_ctor_set_uint8(x_289, sizeof(void*)*1 + 1, x_48);
lean_ctor_set_uint8(x_289, sizeof(void*)*1 + 2, x_49);
if (x_57 == 0)
{
uint8_t x_304; 
x_304 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_45);
lean_inc(x_1);
x_271 = x_25;
x_272 = x_289;
x_273 = x_1;
x_274 = x_45;
x_275 = x_304;
x_276 = x_31;
x_277 = x_32;
x_278 = x_11;
x_279 = lean_box(0);
goto block_287;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_320; 
x_305 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12___closed__3));
if (x_48 == 0)
{
lean_object* x_324; 
x_324 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_320 = x_324;
goto block_323;
}
else
{
lean_object* x_325; 
x_325 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_320 = x_325;
goto block_323;
}
block_319:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_308 = lean_string_append(x_306, x_307);
lean_dec_ref(x_307);
x_309 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_310 = lean_string_append(x_308, x_309);
lean_inc(x_288);
x_311 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_288, x_57);
x_312 = lean_string_append(x_310, x_311);
lean_dec_ref(x_311);
x_313 = lean_string_append(x_305, x_312);
lean_dec_ref(x_312);
x_314 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__3));
x_315 = lean_string_append(x_313, x_314);
x_316 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_6, x_45, x_1);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_290 = x_315;
x_291 = x_317;
goto block_303;
}
else
{
lean_object* x_318; 
x_318 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__4));
x_290 = x_315;
x_291 = x_318;
goto block_303;
}
}
block_323:
{
if (x_49 == 0)
{
lean_object* x_321; 
x_321 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_306 = x_320;
x_307 = x_321;
goto block_319;
}
else
{
lean_object* x_322; 
x_322 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_306 = x_320;
x_307 = x_322;
goto block_319;
}
}
}
block_79:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_shiftl(x_69, x_60);
x_71 = lean_nat_lor(x_68, x_70);
lean_dec(x_70);
x_72 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_63, x_61, x_71);
lean_dec_ref(x_61);
x_73 = lean_array_get_borrowed(x_58, x_52, x_60);
x_74 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_64, x_62, x_60, x_73);
lean_dec(x_60);
lean_dec_ref(x_62);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_65);
x_76 = lean_box(x_59);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
x_13 = x_78;
x_14 = x_66;
x_15 = lean_box(0);
goto block_19;
}
block_91:
{
uint8_t x_89; 
x_89 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_3, x_82);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc_ref(x_82);
x_90 = lean_array_push(x_86, x_82);
x_59 = x_84;
x_60 = x_83;
x_61 = x_80;
x_62 = x_82;
x_63 = x_81;
x_64 = x_85;
x_65 = x_90;
x_66 = x_87;
x_67 = lean_box(0);
goto block_79;
}
else
{
x_59 = x_84;
x_60 = x_83;
x_61 = x_80;
x_62 = x_82;
x_63 = x_81;
x_64 = x_85;
x_65 = x_86;
x_66 = x_87;
x_67 = lean_box(0);
goto block_79;
}
}
block_120:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_string_append(x_99, x_104);
lean_dec_ref(x_104);
x_106 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_96, x_94);
x_107 = lean_string_append(x_105, x_106);
lean_dec_ref(x_106);
x_108 = lean_string_append(x_103, x_107);
lean_dec_ref(x_107);
x_109 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__0));
x_110 = lean_string_append(x_108, x_109);
x_111 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_80 = x_102;
x_81 = x_98;
x_82 = x_92;
x_83 = x_93;
x_84 = x_46;
x_85 = x_95;
x_86 = x_101;
x_87 = x_97;
x_88 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_95);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_1);
x_112 = lean_ctor_get(x_111, 0);
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
x_113 = x_111;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
block_140:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_string_append(x_123, x_134);
lean_dec_ref(x_134);
x_136 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_137 = lean_string_append(x_135, x_136);
if (x_124 == 0)
{
lean_object* x_138; 
x_138 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_92 = x_121;
x_93 = x_126;
x_94 = x_127;
x_95 = x_122;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_137;
x_100 = lean_box(0);
x_101 = x_125;
x_102 = x_132;
x_103 = x_133;
x_104 = x_138;
goto block_120;
}
else
{
lean_object* x_139; 
x_139 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_92 = x_121;
x_93 = x_126;
x_94 = x_127;
x_95 = x_122;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_137;
x_100 = lean_box(0);
x_101 = x_125;
x_102 = x_132;
x_103 = x_133;
x_104 = x_139;
goto block_120;
}
}
block_157:
{
if (x_143 == 0)
{
lean_object* x_155; 
x_155 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_121 = x_141;
x_122 = x_142;
x_123 = x_154;
x_124 = x_144;
x_125 = x_145;
x_126 = x_146;
x_127 = x_147;
x_128 = x_148;
x_129 = x_149;
x_130 = x_150;
x_131 = lean_box(0);
x_132 = x_152;
x_133 = x_153;
x_134 = x_155;
goto block_140;
}
else
{
lean_object* x_156; 
x_156 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_121 = x_141;
x_122 = x_142;
x_123 = x_154;
x_124 = x_144;
x_125 = x_145;
x_126 = x_146;
x_127 = x_147;
x_128 = x_148;
x_129 = x_149;
x_130 = x_150;
x_131 = lean_box(0);
x_132 = x_152;
x_133 = x_153;
x_134 = x_156;
goto block_140;
}
}
block_186:
{
if (x_55 == 0)
{
x_80 = x_162;
x_81 = x_159;
x_82 = x_160;
x_83 = x_161;
x_84 = x_163;
x_85 = x_164;
x_86 = x_165;
x_87 = x_166;
x_88 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_160, 0);
x_169 = lean_ctor_get_uint8(x_160, sizeof(void*)*1);
x_170 = lean_ctor_get_uint8(x_160, sizeof(void*)*1 + 1);
x_171 = lean_ctor_get_uint8(x_160, sizeof(void*)*1 + 2);
lean_inc_ref(x_162);
x_172 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule_tryPrefix(x_5, x_2, x_161, x_162, x_168);
if (lean_obj_tag(x_172) == 1)
{
lean_object* x_173; uint8_t x_174; uint8_t x_184; 
lean_dec(x_161);
x_184 = !lean_is_exclusive(x_160);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_160, 0);
lean_dec(x_185);
x_173 = x_160;
x_174 = x_184;
goto block_183;
}
else
{
lean_dec(x_160);
x_173 = lean_box(0);
x_174 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
lean_dec_ref(x_172);
x_176 = lean_array_get_borrowed(x_158, x_54, x_175);
lean_inc(x_176);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_176);
x_177 = x_173;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_169);
lean_ctor_set_uint8(x_182, sizeof(void*)*1 + 1, x_170);
lean_ctor_set_uint8(x_182, sizeof(void*)*1 + 2, x_171);
x_177 = x_182;
goto block_181;
}
block_181:
{
if (x_57 == 0)
{
x_80 = x_162;
x_81 = x_159;
x_82 = x_177;
x_83 = x_175;
x_84 = x_46;
x_85 = x_164;
x_86 = x_165;
x_87 = x_166;
x_88 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_178; 
x_178 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
if (x_170 == 0)
{
lean_object* x_179; 
x_179 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
lean_inc(x_176);
x_141 = x_177;
x_142 = x_164;
x_143 = x_171;
x_144 = x_169;
x_145 = x_165;
x_146 = x_175;
x_147 = x_57;
x_148 = x_176;
x_149 = x_166;
x_150 = x_159;
x_151 = lean_box(0);
x_152 = x_162;
x_153 = x_178;
x_154 = x_179;
goto block_157;
}
else
{
lean_object* x_180; 
x_180 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
lean_inc(x_176);
x_141 = x_177;
x_142 = x_164;
x_143 = x_171;
x_144 = x_169;
x_145 = x_165;
x_146 = x_175;
x_147 = x_57;
x_148 = x_176;
x_149 = x_166;
x_150 = x_159;
x_151 = lean_box(0);
x_152 = x_162;
x_153 = x_178;
x_154 = x_180;
goto block_157;
}
}
}
}
}
else
{
lean_dec(x_172);
x_80 = x_162;
x_81 = x_159;
x_82 = x_160;
x_83 = x_161;
x_84 = x_163;
x_85 = x_164;
x_86 = x_165;
x_87 = x_166;
x_88 = lean_box(0);
goto block_91;
}
}
}
block_216:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_string_append(x_192, x_200);
lean_dec_ref(x_200);
x_202 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_194, x_199);
x_203 = lean_string_append(x_201, x_202);
lean_dec_ref(x_202);
x_204 = lean_string_append(x_195, x_203);
lean_dec_ref(x_203);
x_205 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__2));
x_206 = lean_string_append(x_204, x_205);
x_207 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_207);
x_159 = x_187;
x_160 = x_188;
x_161 = x_190;
x_162 = x_189;
x_163 = x_193;
x_164 = x_191;
x_165 = x_198;
x_166 = x_196;
x_167 = lean_box(0);
goto block_186;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec_ref(x_191);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec(x_1);
x_208 = lean_ctor_get(x_207, 0);
x_215 = !lean_is_exclusive(x_207);
if (x_215 == 0)
{
x_209 = x_207;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
block_237:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_string_append(x_224, x_231);
lean_dec_ref(x_231);
x_233 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_234 = lean_string_append(x_232, x_233);
if (x_222 == 0)
{
lean_object* x_235; 
x_235 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_187 = x_217;
x_188 = x_218;
x_189 = x_219;
x_190 = x_220;
x_191 = x_221;
x_192 = x_234;
x_193 = x_223;
x_194 = x_225;
x_195 = x_226;
x_196 = x_227;
x_197 = lean_box(0);
x_198 = x_229;
x_199 = x_230;
x_200 = x_235;
goto block_216;
}
else
{
lean_object* x_236; 
x_236 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_187 = x_217;
x_188 = x_218;
x_189 = x_219;
x_190 = x_220;
x_191 = x_221;
x_192 = x_234;
x_193 = x_223;
x_194 = x_225;
x_195 = x_226;
x_196 = x_227;
x_197 = lean_box(0);
x_198 = x_229;
x_199 = x_230;
x_200 = x_236;
goto block_216;
}
}
block_270:
{
if (x_247 == 0)
{
x_159 = x_238;
x_160 = x_242;
x_161 = x_244;
x_162 = x_239;
x_163 = x_240;
x_164 = x_243;
x_165 = x_246;
x_166 = x_241;
x_167 = lean_box(0);
goto block_186;
}
else
{
uint8_t x_248; lean_object* x_249; uint8_t x_250; uint8_t x_269; 
x_248 = lean_ctor_get_uint8(x_239, 1);
x_269 = !lean_is_exclusive(x_239);
if (x_269 == 0)
{
x_249 = x_239;
x_250 = x_269;
goto block_268;
}
else
{
lean_dec(x_239);
x_249 = lean_box(0);
x_250 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; uint8_t x_255; uint8_t x_267; 
x_251 = lean_ctor_get(x_242, 0);
x_252 = lean_ctor_get_uint8(x_242, sizeof(void*)*1);
x_253 = lean_ctor_get_uint8(x_242, sizeof(void*)*1 + 2);
x_267 = !lean_is_exclusive(x_242);
if (x_267 == 0)
{
x_254 = x_242;
x_255 = x_267;
goto block_266;
}
else
{
lean_inc(x_251);
lean_dec(x_242);
x_254 = lean_box(0);
x_255 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_256; 
if (x_250 == 0)
{
x_256 = x_249;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_265, 1, x_248);
x_256 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_257; 
lean_ctor_set_uint8(x_256, 0, x_46);
lean_inc(x_251);
if (x_255 == 0)
{
x_257 = x_254;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_263, 0, x_251);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_252);
lean_ctor_set_uint8(x_263, sizeof(void*)*1 + 2, x_253);
x_257 = x_263;
goto block_262;
}
block_262:
{
lean_ctor_set_uint8(x_257, sizeof(void*)*1 + 1, x_46);
if (x_57 == 0)
{
lean_dec(x_251);
x_159 = x_238;
x_160 = x_257;
x_161 = x_244;
x_162 = x_256;
x_163 = x_240;
x_164 = x_243;
x_165 = x_246;
x_166 = x_241;
x_167 = lean_box(0);
goto block_186;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10___closed__1));
x_259 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
if (x_253 == 0)
{
lean_object* x_260; 
x_260 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_217 = x_238;
x_218 = x_257;
x_219 = x_256;
x_220 = x_244;
x_221 = x_243;
x_222 = x_252;
x_223 = x_240;
x_224 = x_259;
x_225 = x_251;
x_226 = x_258;
x_227 = x_241;
x_228 = lean_box(0);
x_229 = x_246;
x_230 = x_57;
x_231 = x_260;
goto block_237;
}
else
{
lean_object* x_261; 
x_261 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_217 = x_238;
x_218 = x_257;
x_219 = x_256;
x_220 = x_244;
x_221 = x_243;
x_222 = x_252;
x_223 = x_240;
x_224 = x_259;
x_225 = x_251;
x_226 = x_258;
x_227 = x_241;
x_228 = lean_box(0);
x_229 = x_246;
x_230 = x_57;
x_231 = x_261;
goto block_237;
}
}
}
}
}
}
}
}
block_287:
{
if (x_56 == 0)
{
x_159 = x_271;
x_160 = x_272;
x_161 = x_273;
x_162 = x_274;
x_163 = x_275;
x_164 = x_276;
x_165 = x_277;
x_166 = x_278;
x_167 = lean_box(0);
goto block_186;
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_274, 0);
if (x_280 == 0)
{
uint8_t x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_281 = lean_ctor_get_uint8(x_274, 1);
x_282 = lean_array_get_borrowed(x_58, x_53, x_5);
x_283 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_283, 0, x_46);
lean_ctor_set_uint8(x_283, 1, x_281);
x_284 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_282, x_283, x_273);
lean_dec_ref(x_283);
if (x_284 == 0)
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_285, 0, x_46);
lean_ctor_set_uint8(x_285, 1, x_46);
x_286 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_282, x_285, x_273);
lean_dec_ref(x_285);
x_238 = x_271;
x_239 = x_274;
x_240 = x_275;
x_241 = x_278;
x_242 = x_272;
x_243 = x_276;
x_244 = x_273;
x_245 = lean_box(0);
x_246 = x_277;
x_247 = x_286;
goto block_270;
}
else
{
x_238 = x_271;
x_239 = x_274;
x_240 = x_275;
x_241 = x_278;
x_242 = x_272;
x_243 = x_276;
x_244 = x_273;
x_245 = lean_box(0);
x_246 = x_277;
x_247 = x_284;
goto block_270;
}
}
else
{
x_159 = x_271;
x_160 = x_272;
x_161 = x_273;
x_162 = x_274;
x_163 = x_275;
x_164 = x_276;
x_165 = x_277;
x_166 = x_278;
x_167 = lean_box(0);
goto block_186;
}
}
}
block_303:
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_string_append(x_290, x_291);
lean_dec_ref(x_291);
x_293 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_292);
if (lean_obj_tag(x_293) == 0)
{
uint8_t x_294; 
lean_dec_ref(x_293);
x_294 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_45);
lean_inc(x_1);
x_271 = x_25;
x_272 = x_289;
x_273 = x_1;
x_274 = x_45;
x_275 = x_294;
x_276 = x_31;
x_277 = x_32;
x_278 = x_11;
x_279 = lean_box(0);
goto block_287;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_302; 
lean_dec_ref(x_289);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_11);
lean_dec(x_1);
x_295 = lean_ctor_get(x_293, 0);
x_302 = !lean_is_exclusive(x_293);
if (x_302 == 0)
{
x_296 = x_293;
x_297 = x_302;
goto block_301;
}
else
{
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_box(0);
x_297 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_298; 
if (x_297 == 0)
{
x_298 = x_296;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_295);
x_298 = x_300;
goto block_299;
}
block_299:
{
return x_298;
}
}
}
}
}
else
{
goto block_44;
}
}
}
else
{
goto block_44;
}
}
block_44:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_35);
x_36 = x_29;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_35);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_36);
x_37 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
x_13 = x_37;
x_14 = x_11;
x_15 = lean_box(0);
goto block_19;
}
}
}
}
}
}
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_53; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_9, 1);
lean_dec(x_54);
x_18 = x_9;
x_19 = x_53;
goto block_52;
}
else
{
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_50; 
x_20 = lean_ctor_get(x_15, 0);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_15, 1);
lean_dec(x_51);
x_21 = x_15;
x_22 = x_50;
goto block_49;
}
else
{
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_48; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
x_25 = x_16;
x_26 = x_48;
goto block_47;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_array_uget_borrowed(x_6, x_8);
x_28 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
if (x_26 == 0)
{
x_29 = x_25;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_24);
x_29 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_30; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_29);
x_30 = x_21;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_20);
lean_ctor_set(x_44, 1, x_29);
x_30 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_31; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_30);
x_31 = x_18;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_30);
x_31 = x_42;
goto block_41;
}
block_41:
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_usize_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0);
x_33 = 0;
lean_inc(x_27);
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__10(x_27, x_1, x_2, x_3, x_4, x_5, x_28, x_32, x_33, x_31, x_10);
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
x_39 = lean_usize_add(x_8, x_38);
x_8 = x_39;
x_9 = x_36;
x_10 = x_37;
goto _start;
}
else
{
return x_34;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_19; 
x_6 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_7 = x_2;
x_8 = x_19;
goto block_18;
}
else
{
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_nat_add(x_10, x_6);
lean_dec(x_6);
x_12 = lean_string_utf8_next_fast(x_9, x_11);
lean_dec(x_11);
x_13 = lean_nat_sub(x_12, x_10);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_13);
x_14 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_13);
x_14 = x_17;
goto block_16;
}
block_16:
{
x_2 = x_14;
x_3 = x_4;
goto _start;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_76; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_76 = !lean_is_exclusive(x_2);
if (x_76 == 0)
{
x_24 = x_2;
x_25 = x_76;
goto block_75;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 2);
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_nat_sub(x_22, x_23);
x_33 = lean_nat_sub(x_28, x_27);
x_34 = lean_nat_add(x_32, x_33);
x_35 = lean_nat_sub(x_31, x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_33);
lean_del_object(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_37 = lean_nat_dec_lt(x_32, x_35);
lean_dec(x_35);
lean_dec(x_32);
if (x_37 == 0)
{
return x_3;
}
else
{
lean_object* x_38; 
x_38 = lean_box(3);
x_2 = x_38;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_32);
x_40 = lean_nat_add(x_30, x_22);
x_41 = lean_string_get_byte_fast(x_29, x_40);
x_42 = lean_nat_add(x_27, x_23);
x_43 = lean_string_get_byte_fast(x_26, x_42);
x_44 = lean_uint8_dec_eq(x_41, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_33);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_23, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_23, x_47);
lean_dec(x_23);
x_49 = lean_array_fget_borrowed(x_21, x_48);
lean_dec(x_48);
x_50 = lean_nat_dec_eq(x_49, x_45);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_49);
if (x_25 == 0)
{
lean_ctor_set(x_24, 3, x_49);
x_51 = x_24;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_21);
lean_ctor_set(x_54, 2, x_22);
lean_ctor_set(x_54, 3, x_49);
x_51 = x_54;
goto block_53;
}
block_53:
{
x_2 = x_51;
x_3 = x_4;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_String_Slice_posGE___redArg(x_1, x_22);
if (x_25 == 0)
{
lean_ctor_set(x_24, 3, x_45);
lean_ctor_set(x_24, 2, x_55);
x_56 = x_24;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_59, 0, x_20);
lean_ctor_set(x_59, 1, x_21);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_45);
x_56 = x_59;
goto block_58;
}
block_58:
{
x_2 = x_56;
x_3 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_22, x_60);
lean_dec(x_22);
x_62 = l_String_Slice_posGE___redArg(x_1, x_61);
if (x_25 == 0)
{
lean_ctor_set(x_24, 3, x_45);
lean_ctor_set(x_24, 2, x_62);
x_63 = x_24;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_66, 0, x_20);
lean_ctor_set(x_66, 1, x_21);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_45);
x_63 = x_66;
goto block_65;
}
block_65:
{
x_2 = x_63;
x_3 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_23, x_67);
lean_dec(x_23);
x_69 = lean_nat_dec_eq(x_68, x_33);
lean_dec(x_33);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_nat_add(x_22, x_67);
lean_dec(x_22);
if (x_25 == 0)
{
lean_ctor_set(x_24, 3, x_68);
lean_ctor_set(x_24, 2, x_70);
x_71 = x_24;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_21);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_68);
x_71 = x_74;
goto block_73;
}
block_73:
{
x_2 = x_71;
goto _start;
}
}
else
{
lean_dec(x_68);
lean_del_object(x_24);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
return x_69;
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
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1);
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3);
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__4);
x_3 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__3);
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
x_6 = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__5);
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6));
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_66; lean_object* x_67; lean_object* x_79; lean_object* x_80; lean_object* x_98; lean_object* x_105; lean_object* x_106; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget_borrowed(x_5, x_7);
lean_inc(x_22);
x_23 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_22);
x_105 = lean_ctor_get(x_23, 0);
lean_inc(x_105);
x_106 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_105);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_108 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_107);
x_98 = x_108;
goto block_104;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec_ref(x_106);
x_98 = x_109;
goto block_104;
}
block_45:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec_ref(x_23);
x_30 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_31 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_29, x_26);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_24, x_32);
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
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_25);
lean_dec_ref(x_9);
x_37 = lean_ctor_get(x_36, 0);
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
x_38 = x_36;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
block_57:
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_52 = lean_string_append(x_48, x_50);
lean_dec_ref(x_50);
x_53 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_54 = lean_string_append(x_52, x_53);
if (x_51 == 0)
{
lean_object* x_55; 
x_55 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_24 = x_46;
x_25 = x_47;
x_26 = x_49;
x_27 = x_54;
x_28 = x_55;
goto block_45;
}
else
{
lean_object* x_56; 
x_56 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_24 = x_46;
x_25 = x_47;
x_26 = x_49;
x_27 = x_54;
x_28 = x_56;
goto block_45;
}
}
block_65:
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_46 = x_58;
x_47 = x_59;
x_48 = x_61;
x_49 = x_60;
x_50 = x_63;
goto block_57;
}
else
{
lean_object* x_64; 
x_64 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_46 = x_58;
x_47 = x_59;
x_48 = x_61;
x_49 = x_60;
x_50 = x_64;
goto block_57;
}
}
block_78:
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_shiftl(x_70, x_67);
lean_dec(x_67);
x_72 = lean_nat_lor(x_69, x_71);
lean_dec(x_71);
x_73 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_8, x_66, x_72);
lean_dec_ref(x_66);
if (x_68 == 0)
{
lean_dec_ref(x_23);
x_11 = x_73;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_74; lean_object* x_75; 
x_74 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_75 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__1));
if (x_74 == 0)
{
lean_object* x_76; 
x_76 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_58 = x_75;
x_59 = x_73;
x_60 = x_68;
x_61 = x_76;
goto block_65;
}
else
{
lean_object* x_77; 
x_77 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_58 = x_75;
x_59 = x_73;
x_60 = x_68;
x_61 = x_77;
goto block_65;
}
}
}
block_97:
{
lean_object* x_81; 
x_81 = l_Lean_Syntax_getTrailing_x3f(x_22);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_23);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_96; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_ctor_get(x_82, 2);
x_96 = !lean_is_exclusive(x_82);
if (x_96 == 0)
{
x_86 = x_82;
x_87 = x_96;
goto block_95;
}
else
{
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_82);
x_86 = lean_box(0);
x_87 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_string_utf8_extract(x_83, x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_string_utf8_byte_size(x_88);
if (x_87 == 0)
{
lean_ctor_set(x_86, 2, x_90);
lean_ctor_set(x_86, 1, x_89);
lean_ctor_set(x_86, 0, x_88);
x_91 = x_86;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_90);
x_91 = x_94;
goto block_93;
}
block_93:
{
uint8_t x_92; 
x_92 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8(x_91);
lean_dec_ref(x_91);
if (x_92 == 0)
{
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_23);
x_11 = x_8;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
x_66 = x_79;
x_67 = x_80;
goto block_78;
}
}
}
}
}
block_104:
{
lean_object* x_99; 
x_99 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
if (x_2 == 0)
{
uint8_t x_100; 
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_100 == 0)
{
x_79 = x_99;
x_80 = x_98;
goto block_97;
}
else
{
uint8_t x_101; 
x_101 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
if (x_101 == 0)
{
x_79 = x_99;
x_80 = x_98;
goto block_97;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3));
x_103 = l_Lean_Name_isPrefixOf(x_102, x_3);
if (x_103 == 0)
{
x_66 = x_99;
x_67 = x_98;
goto block_78;
}
else
{
x_79 = x_99;
x_80 = x_98;
goto block_97;
}
}
}
}
else
{
x_66 = x_99;
x_67 = x_98;
goto block_78;
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
x_6 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_1);
x_7 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_1);
x_8 = l_Lean_instBEqImport_beq(x_6, x_7);
lean_dec_ref(x_7);
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
x_24 = lean_array_uget_borrowed(x_4, x_6);
x_25 = 0;
x_26 = lean_usize_of_nat(x_22);
lean_inc(x_24);
x_27 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__19(x_24, x_1, x_25, x_26);
if (x_27 == 0)
{
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_54; lean_object* x_55; 
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_unsigned_to_nat(1u);
x_54 = 0;
x_55 = l_Lean_Syntax_getPos_x3f(x_24, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_57 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_56);
x_30 = x_57;
goto block_53;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec_ref(x_55);
x_30 = x_58;
goto block_53;
}
block_53:
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
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_44, 0);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
x_46 = x_44;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
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
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1);
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3);
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__4);
x_3 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__3);
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___closed__5);
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6));
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
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
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
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_Name_isPrefixOf(x_6, x_1);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29_spec__36(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0(void) {
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
x_3 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15___lam__0___closed__0);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_97; uint8_t x_104; lean_object* x_105; lean_object* x_121; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget_borrowed(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_box(0);
x_104 = 0;
x_121 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_123 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_122);
x_105 = x_123;
goto block_120;
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec_ref(x_121);
x_105 = x_124;
goto block_120;
}
block_78:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
lean_inc(x_29);
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
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec_ref(x_9);
x_52 = lean_ctor_get(x_51, 0);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
x_53 = x_51;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_27);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_61 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_11 = x_24;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_9);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec(x_27);
lean_dec_ref(x_9);
x_70 = lean_ctor_get(x_36, 0);
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
x_71 = x_36;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_36);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
block_89:
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_84 = lean_string_append(x_79, x_82);
lean_dec_ref(x_82);
x_85 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_86 = lean_string_append(x_84, x_85);
if (x_83 == 0)
{
lean_object* x_87; 
x_87 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_25 = x_80;
x_26 = x_86;
x_27 = x_81;
x_28 = x_87;
goto block_78;
}
else
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_25 = x_80;
x_26 = x_86;
x_27 = x_81;
x_28 = x_88;
goto block_78;
}
}
block_96:
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_79 = x_92;
x_80 = x_90;
x_81 = x_91;
x_82 = x_94;
goto block_89;
}
else
{
lean_object* x_95; 
x_95 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_79 = x_92;
x_80 = x_90;
x_81 = x_91;
x_82 = x_95;
goto block_89;
}
}
block_103:
{
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_100 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_99 == 0)
{
lean_object* x_101; 
x_101 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_90 = x_100;
x_91 = x_98;
x_92 = x_101;
goto block_96;
}
else
{
lean_object* x_102; 
x_102 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_90 = x_100;
x_91 = x_98;
x_92 = x_102;
goto block_96;
}
}
else
{
lean_dec(x_97);
x_11 = x_24;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_120:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_22);
lean_inc_ref(x_106);
lean_inc(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
if (x_109 == 0)
{
lean_dec_ref(x_106);
lean_dec(x_105);
x_97 = x_108;
goto block_103;
}
else
{
uint8_t x_110; lean_object* x_111; uint8_t x_112; uint8_t x_119; 
x_110 = lean_ctor_get_uint8(x_106, 1);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
x_111 = x_106;
x_112 = x_119;
goto block_118;
}
else
{
lean_dec(x_106);
x_111 = lean_box(0);
x_112 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_117, 1, x_110);
x_113 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
lean_ctor_set_uint8(x_113, 0, x_104);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_114);
x_97 = x_115;
goto block_103;
}
}
}
}
else
{
lean_dec_ref(x_106);
lean_dec(x_105);
x_97 = x_108;
goto block_103;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_98; lean_object* x_105; lean_object* x_121; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget_borrowed(x_5, x_7);
x_23 = lean_ctor_get(x_22, 0);
x_24 = 0;
x_25 = lean_box(0);
x_121 = l_Lean_Environment_getModuleIdx_x3f(x_21, x_23);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_123 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_122);
x_105 = x_123;
goto block_120;
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec_ref(x_121);
x_105 = x_124;
goto block_120;
}
block_79:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
lean_inc(x_30);
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_30, x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = lean_string_append(x_26, x_33);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_36 = lean_string_append(x_34, x_35);
x_37 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec_ref(x_28);
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
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec_ref(x_9);
x_53 = lean_ctor_get(x_52, 0);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
x_54 = x_52;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_28);
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_62 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec_ref(x_9);
x_63 = lean_ctor_get(x_62, 0);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
x_64 = x_62;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_28);
lean_dec_ref(x_9);
x_71 = lean_ctor_get(x_37, 0);
x_78 = !lean_is_exclusive(x_37);
if (x_78 == 0)
{
x_72 = x_37;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_37);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
block_90:
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_85 = lean_string_append(x_81, x_83);
lean_dec_ref(x_83);
x_86 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_87 = lean_string_append(x_85, x_86);
if (x_84 == 0)
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_26 = x_80;
x_27 = x_87;
x_28 = x_82;
x_29 = x_88;
goto block_79;
}
else
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_26 = x_80;
x_27 = x_87;
x_28 = x_82;
x_29 = x_89;
goto block_79;
}
}
block_97:
{
uint8_t x_94; 
x_94 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_80 = x_91;
x_81 = x_93;
x_82 = x_92;
x_83 = x_95;
goto block_90;
}
else
{
lean_object* x_96; 
x_96 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_80 = x_91;
x_81 = x_93;
x_82 = x_92;
x_83 = x_96;
goto block_90;
}
}
block_104:
{
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_101 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_100 == 0)
{
lean_object* x_102; 
x_102 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_91 = x_101;
x_92 = x_99;
x_93 = x_102;
goto block_97;
}
else
{
lean_object* x_103; 
x_103 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_91 = x_101;
x_92 = x_99;
x_93 = x_103;
goto block_97;
}
}
else
{
lean_dec(x_98);
x_11 = x_25;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
block_120:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_22);
lean_inc_ref(x_106);
lean_inc(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
if (x_109 == 0)
{
lean_dec_ref(x_106);
lean_dec(x_105);
x_98 = x_108;
goto block_104;
}
else
{
uint8_t x_110; lean_object* x_111; uint8_t x_112; uint8_t x_119; 
x_110 = lean_ctor_get_uint8(x_106, 1);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
x_111 = x_106;
x_112 = x_119;
goto block_118;
}
else
{
lean_dec(x_106);
x_111 = lean_box(0);
x_112 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_117, 1, x_110);
x_113 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
lean_ctor_set_uint8(x_113, 0, x_24);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_2, x_114);
x_98 = x_115;
goto block_104;
}
}
}
}
else
{
lean_dec_ref(x_106);
lean_dec(x_105);
x_98 = x_108;
goto block_104;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_24; 
x_4 = lean_ctor_get(x_1, 1);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_5 = x_1;
x_6 = x_24;
goto block_23;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_22; 
x_7 = lean_ctor_get(x_3, 0);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
x_8 = x_3;
x_9 = x_22;
goto block_21;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_7, x_4);
if (x_10 == 0)
{
lean_del_object(x_8);
lean_dec(x_7);
lean_del_object(x_5);
lean_dec(x_4);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_12);
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; 
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_13);
x_14 = x_5;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_4);
x_14 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_15; 
x_15 = lean_array_push(x_2, x_7);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
}
}
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
x_23 = lean_array_uget_borrowed(x_6, x_8);
x_24 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_99; lean_object* x_106; lean_object* x_122; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_23, 0);
x_122 = l_Lean_Environment_getModuleIdx_x3f(x_25, x_26);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_124 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_123);
x_106 = x_124;
goto block_121;
}
else
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec_ref(x_122);
x_106 = x_125;
goto block_121;
}
block_80:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_string_append(x_27, x_30);
lean_dec_ref(x_30);
lean_inc(x_31);
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_31, x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_29, x_34);
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
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_10);
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_28);
x_62 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_63 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec_ref(x_10);
x_64 = lean_ctor_get(x_63, 0);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
x_65 = x_63;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_28);
lean_dec_ref(x_10);
x_72 = lean_ctor_get(x_38, 0);
x_79 = !lean_is_exclusive(x_38);
if (x_79 == 0)
{
x_73 = x_38;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_38);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
block_91:
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_86 = lean_string_append(x_81, x_84);
lean_dec_ref(x_84);
x_87 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_88 = lean_string_append(x_86, x_87);
if (x_85 == 0)
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_27 = x_88;
x_28 = x_82;
x_29 = x_83;
x_30 = x_89;
goto block_80;
}
else
{
lean_object* x_90; 
x_90 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_27 = x_88;
x_28 = x_82;
x_29 = x_83;
x_30 = x_90;
goto block_80;
}
}
block_98:
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_81 = x_94;
x_82 = x_92;
x_83 = x_93;
x_84 = x_96;
goto block_91;
}
else
{
lean_object* x_97; 
x_97 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_81 = x_94;
x_82 = x_92;
x_83 = x_93;
x_84 = x_97;
goto block_91;
}
}
block_105:
{
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_102 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_101 == 0)
{
lean_object* x_103; 
x_103 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_92 = x_100;
x_93 = x_102;
x_94 = x_103;
goto block_98;
}
else
{
lean_object* x_104; 
x_104 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_92 = x_100;
x_93 = x_102;
x_94 = x_104;
goto block_98;
}
}
else
{
lean_dec(x_99);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_121:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
lean_inc_ref(x_107);
lean_inc(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 3);
if (x_110 == 0)
{
lean_dec_ref(x_107);
lean_dec(x_106);
x_99 = x_109;
goto block_105;
}
else
{
uint8_t x_111; lean_object* x_112; uint8_t x_113; uint8_t x_120; 
x_111 = lean_ctor_get_uint8(x_107, 1);
x_120 = !lean_is_exclusive(x_107);
if (x_120 == 0)
{
x_112 = x_107;
x_113 = x_120;
goto block_119;
}
else
{
lean_dec(x_107);
x_112 = lean_box(0);
x_113 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_118, 1, x_111);
x_114 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_115; lean_object* x_116; 
lean_ctor_set_uint8(x_114, 0, x_24);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_115);
x_99 = x_116;
goto block_105;
}
}
}
}
else
{
lean_dec_ref(x_107);
lean_dec(x_106);
x_99 = x_109;
goto block_105;
}
}
}
else
{
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
x_23 = lean_array_uget_borrowed(x_6, x_8);
x_24 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_99; lean_object* x_106; lean_object* x_122; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_23, 0);
x_122 = l_Lean_Environment_getModuleIdx_x3f(x_25, x_26);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_124 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_123);
x_106 = x_124;
goto block_121;
}
else
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec_ref(x_122);
x_106 = x_125;
goto block_121;
}
block_80:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
lean_inc(x_31);
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_31, x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_28, x_34);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__0));
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec_ref(x_27);
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
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_10);
x_54 = lean_ctor_get(x_53, 0);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
x_55 = x_53;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_27);
x_62 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__3));
x_63 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec_ref(x_10);
x_64 = lean_ctor_get(x_63, 0);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
x_65 = x_63;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_27);
lean_dec_ref(x_10);
x_72 = lean_ctor_get(x_38, 0);
x_79 = !lean_is_exclusive(x_38);
if (x_79 == 0)
{
x_73 = x_38;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_38);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
block_91:
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_86 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_87 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_88 = lean_string_append(x_86, x_87);
if (x_85 == 0)
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_27 = x_81;
x_28 = x_82;
x_29 = x_88;
x_30 = x_89;
goto block_80;
}
else
{
lean_object* x_90; 
x_90 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_27 = x_81;
x_28 = x_82;
x_29 = x_88;
x_30 = x_90;
goto block_80;
}
}
block_98:
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_81 = x_92;
x_82 = x_93;
x_83 = x_94;
x_84 = x_96;
goto block_91;
}
else
{
lean_object* x_97; 
x_97 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_81 = x_92;
x_82 = x_93;
x_83 = x_94;
x_84 = x_97;
goto block_91;
}
}
block_105:
{
if (lean_obj_tag(x_99) == 1)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_102 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16_spec__21___closed__4));
if (x_101 == 0)
{
lean_object* x_103; 
x_103 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_92 = x_100;
x_93 = x_102;
x_94 = x_103;
goto block_98;
}
else
{
lean_object* x_104; 
x_104 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_92 = x_100;
x_93 = x_102;
x_94 = x_104;
goto block_98;
}
}
else
{
lean_dec(x_99);
x_12 = x_22;
x_13 = x_10;
x_14 = lean_box(0);
goto block_18;
}
}
block_121:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_ofImport(x_23);
lean_inc_ref(x_107);
lean_inc(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 3);
if (x_110 == 0)
{
lean_dec_ref(x_107);
lean_dec(x_106);
x_99 = x_109;
goto block_105;
}
else
{
uint8_t x_111; lean_object* x_112; uint8_t x_113; uint8_t x_120; 
x_111 = lean_ctor_get_uint8(x_107, 1);
x_120 = !lean_is_exclusive(x_107);
if (x_120 == 0)
{
x_112 = x_107;
x_113 = x_120;
goto block_119;
}
else
{
lean_dec(x_107);
x_112 = lean_box(0);
x_113 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_118, 1, x_111);
x_114 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_115; lean_object* x_116; 
lean_ctor_set_uint8(x_114, 0, x_24);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_getExplanations_addExplanation_spec__1___redArg(x_3, x_115);
x_99 = x_116;
goto block_105;
}
}
}
}
else
{
lean_dec_ref(x_107);
lean_dec(x_106);
x_99 = x_109;
goto block_105;
}
}
}
else
{
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_109; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 0);
x_109 = !lean_is_exclusive(x_8);
if (x_109 == 0)
{
x_23 = x_8;
x_24 = x_109;
goto block_108;
}
else
{
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_107; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_107 = !lean_is_exclusive(x_21);
if (x_107 == 0)
{
x_27 = x_21;
x_28 = x_107;
goto block_106;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_uget_borrowed(x_5, x_7);
x_30 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_22, x_29, x_1);
if (x_30 == 0)
{
lean_object* x_31; 
if (x_28 == 0)
{
x_31 = x_27;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_31);
x_32 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_11 = x_32;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_96; uint8_t x_102; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 7);
x_39 = lean_ctor_get_uint8(x_29, 0);
x_40 = lean_ctor_get_uint8(x_29, 1);
x_41 = lean_box(0);
x_42 = 0;
x_43 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_44 = lean_array_get_borrowed(x_41, x_38, x_1);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 2, x_40);
x_102 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_26, x_45);
if (x_102 == 0)
{
lean_del_object(x_27);
lean_del_object(x_23);
goto block_95;
}
else
{
uint8_t x_103; 
x_103 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_29, x_1);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_104, 0, x_4);
lean_ctor_set_uint8(x_104, 1, x_40);
x_105 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_25, x_104, x_1);
lean_dec_ref(x_104);
x_96 = x_105;
goto block_101;
}
else
{
x_96 = x_103;
goto block_101;
}
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_Array_erase___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__2(x_47, x_45);
lean_dec_ref(x_45);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_shiftl(x_52, x_1);
x_54 = lean_nat_lor(x_51, x_53);
lean_dec(x_53);
x_55 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_sub(x_46, x_29, x_54);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_50);
x_56 = x_27;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_50);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_56);
lean_ctor_set(x_23, 0, x_55);
x_57 = x_23;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
x_11 = x_57;
x_12 = x_48;
x_13 = lean_box(0);
goto block_17;
}
}
}
block_84:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_string_append(x_65, x_66);
lean_dec_ref(x_66);
x_68 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_69 = lean_string_append(x_67, x_68);
lean_inc(x_44);
x_70 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_44, x_63);
x_71 = lean_string_append(x_69, x_70);
lean_dec_ref(x_70);
x_72 = lean_string_append(x_64, x_71);
lean_dec_ref(x_71);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__0));
x_74 = lean_string_append(x_72, x_73);
x_75 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
x_46 = x_22;
x_47 = x_26;
x_48 = x_9;
x_49 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec_ref(x_45);
lean_del_object(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_76 = lean_ctor_get(x_75, 0);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
x_77 = x_75;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
block_90:
{
if (x_40 == 0)
{
lean_object* x_88; 
x_88 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_63 = x_85;
x_64 = x_86;
x_65 = x_87;
x_66 = x_88;
goto block_84;
}
else
{
lean_object* x_89; 
x_89 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_63 = x_85;
x_64 = x_86;
x_65 = x_87;
x_66 = x_89;
goto block_84;
}
}
block_95:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_array_get_borrowed(x_43, x_37, x_1);
x_92 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_25, x_45, x_1, x_91);
lean_dec_ref(x_45);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_26);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_22);
lean_ctor_set(x_94, 1, x_93);
x_11 = x_94;
x_12 = x_9;
x_13 = lean_box(0);
goto block_17;
}
block_101:
{
if (x_96 == 0)
{
lean_del_object(x_27);
lean_del_object(x_23);
goto block_95;
}
else
{
uint8_t x_97; 
x_97 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 7);
if (x_97 == 0)
{
x_46 = x_22;
x_47 = x_26;
x_48 = x_9;
x_49 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_98; 
x_98 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5___closed__1));
if (x_39 == 0)
{
lean_object* x_99; 
x_99 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_85 = x_97;
x_86 = x_98;
x_87 = x_99;
goto block_90;
}
else
{
lean_object* x_100; 
x_100 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_85 = x_97;
x_86 = x_98;
x_87 = x_100;
goto block_90;
}
}
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_41; 
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 0);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_15 = x_7;
x_16 = x_41;
goto block_40;
}
else
{
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_39; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
x_19 = x_13;
x_20 = x_39;
goto block_38;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_array_uget_borrowed(x_4, x_6);
x_22 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
if (x_20 == 0)
{
x_23 = x_19;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_18);
x_23 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_24; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_23);
x_24 = x_15;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_23);
x_24 = x_35;
goto block_34;
}
block_34:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0);
x_26 = 0;
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__5(x_21, x_1, x_2, x_3, x_22, x_25, x_26, x_24, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_6, x_31);
x_6 = x_32;
x_7 = x_29;
x_8 = x_30;
goto _start;
}
else
{
return x_27;
}
}
}
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
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1);
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3);
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__4);
x_3 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__3);
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
x_6 = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28___closed__5);
x_2 = x_7;
goto block_5;
}
else
{
lean_object* x_8; 
x_8 = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__8___closed__6));
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
x_12 = lean_array_uget_borrowed(x_3, x_5);
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
x_19 = lean_array_uget_borrowed(x_3, x_5);
x_20 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_has(x_6, x_19, x_1);
if (x_20 == 0)
{
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
x_23 = 0;
x_24 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
x_25 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_22);
x_28 = l___private_Lake_CLI_Shake_0__Lake_Shake_addTransitiveImps(x_25, x_27, x_1, x_2);
lean_dec_ref(x_27);
x_29 = lean_usize_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0);
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
x_15 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_NeedsKind_all));
x_16 = lean_usize_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg___closed__0);
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
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_160; lean_object* x_161; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; size_t x_176; lean_object* x_177; lean_object* x_178; size_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_227; lean_object* x_228; size_t x_229; lean_object* x_230; size_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_255; lean_object* x_256; size_t x_257; lean_object* x_258; lean_object* x_259; size_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_305; lean_object* x_306; size_t x_307; lean_object* x_308; lean_object* x_309; size_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; size_t x_322; lean_object* x_323; size_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; size_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; size_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; size_t x_359; lean_object* x_360; lean_object* x_361; size_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_400; size_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_517; size_t x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; uint8_t x_534; size_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_553; size_t x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; uint8_t x_561; uint8_t x_606; size_t x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; lean_object* x_614; uint8_t x_615; uint8_t x_633; size_t x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_646; size_t x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; lean_object* x_662; lean_object* x_669; lean_object* x_670; uint8_t x_719; 
x_166 = lean_ctor_get(x_8, 0);
x_167 = lean_ctor_get(x_8, 1);
x_168 = lean_ctor_get(x_8, 2);
x_169 = lean_ctor_get(x_8, 3);
x_170 = lean_ctor_get(x_8, 4);
x_171 = lean_ctor_get(x_8, 5);
x_172 = lean_ctor_get(x_8, 6);
x_173 = lean_ctor_get(x_8, 7);
x_174 = lean_box(0);
x_354 = l_Lean_instInhabitedModuleData_default;
x_355 = lean_array_get(x_174, x_173, x_3);
x_719 = l_Lean_isExtraRevModUse(x_166, x_3);
if (x_719 == 0)
{
x_669 = x_8;
x_670 = lean_box(0);
goto block_718;
}
else
{
lean_object* x_720; uint8_t x_721; uint8_t x_752; 
lean_inc_ref(x_173);
lean_inc_ref(x_172);
lean_inc_ref(x_171);
lean_inc_ref(x_170);
lean_inc_ref(x_169);
lean_inc_ref(x_168);
lean_inc_ref(x_167);
lean_inc_ref(x_166);
x_752 = !lean_is_exclusive(x_8);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_753 = lean_ctor_get(x_8, 7);
lean_dec(x_753);
x_754 = lean_ctor_get(x_8, 6);
lean_dec(x_754);
x_755 = lean_ctor_get(x_8, 5);
lean_dec(x_755);
x_756 = lean_ctor_get(x_8, 4);
lean_dec(x_756);
x_757 = lean_ctor_get(x_8, 3);
lean_dec(x_757);
x_758 = lean_ctor_get(x_8, 2);
lean_dec(x_758);
x_759 = lean_ctor_get(x_8, 1);
lean_dec(x_759);
x_760 = lean_ctor_get(x_8, 0);
lean_dec(x_760);
x_720 = x_8;
x_721 = x_752;
goto block_751;
}
else
{
lean_dec(x_8);
x_720 = lean_box(0);
x_721 = x_752;
goto block_751;
}
block_751:
{
uint8_t x_722; uint8_t x_723; lean_object* x_724; 
x_722 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 3);
x_723 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 7);
if (x_722 == 0)
{
lean_object* x_748; 
x_748 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_748, 0, x_722);
lean_ctor_set_uint8(x_748, 1, x_722);
x_724 = x_748;
goto block_747;
}
else
{
uint8_t x_749; lean_object* x_750; 
x_749 = 0;
x_750 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_750, 0, x_719);
lean_ctor_set_uint8(x_750, 1, x_749);
x_724 = x_750;
goto block_747;
}
block_747:
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_725 = lean_unsigned_to_nat(0u);
x_726 = lean_unsigned_to_nat(1u);
x_727 = lean_nat_shiftl(x_726, x_3);
x_728 = lean_nat_lor(x_725, x_727);
lean_dec(x_727);
x_729 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_169, x_724, x_728);
lean_dec_ref(x_724);
if (x_721 == 0)
{
lean_ctor_set(x_720, 3, x_729);
x_730 = x_720;
goto block_745;
}
else
{
lean_object* x_746; 
x_746 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_746, 0, x_166);
lean_ctor_set(x_746, 1, x_167);
lean_ctor_set(x_746, 2, x_168);
lean_ctor_set(x_746, 3, x_729);
lean_ctor_set(x_746, 4, x_170);
lean_ctor_set(x_746, 5, x_171);
lean_ctor_set(x_746, 6, x_172);
lean_ctor_set(x_746, 7, x_173);
x_730 = x_746;
goto block_745;
}
block_745:
{
if (x_723 == 0)
{
x_669 = x_730;
x_670 = lean_box(0);
goto block_718;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_731 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__5));
lean_inc(x_355);
x_732 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_355, x_723);
x_733 = lean_string_append(x_731, x_732);
lean_dec_ref(x_732);
x_734 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__6));
x_735 = lean_string_append(x_733, x_734);
x_736 = l_IO_eprintln___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__3(x_735);
if (lean_obj_tag(x_736) == 0)
{
lean_dec_ref(x_736);
x_669 = x_730;
x_670 = lean_box(0);
goto block_718;
}
else
{
lean_object* x_737; lean_object* x_738; uint8_t x_739; uint8_t x_744; 
lean_dec_ref(x_730);
lean_dec(x_355);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_737 = lean_ctor_get(x_736, 0);
x_744 = !lean_is_exclusive(x_736);
if (x_744 == 0)
{
x_738 = x_736;
x_739 = x_744;
goto block_743;
}
else
{
lean_inc(x_737);
lean_dec(x_736);
x_738 = lean_box(0);
x_739 = x_744;
goto block_743;
}
block_743:
{
lean_object* x_740; 
if (x_739 == 0)
{
x_740 = x_738;
goto block_741;
}
else
{
lean_object* x_742; 
x_742 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_742, 0, x_737);
x_740 = x_742;
goto block_741;
}
block_741:
{
return x_740;
}
}
}
}
}
}
}
}
block_99:
{
lean_object* x_19; 
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__13(x_15, x_16, x_12, x_13, x_11, x_10, x_17);
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
x_23 = lean_array_size(x_14);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__14(x_15, x_14, x_23, x_11, x_21, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_82; 
x_25 = lean_ctor_get(x_24, 0);
x_82 = !lean_is_exclusive(x_24);
if (x_82 == 0)
{
x_26 = x_24;
x_27 = x_82;
goto block_81;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_80; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 0);
x_80 = !lean_is_exclusive(x_25);
if (x_80 == 0)
{
x_30 = x_25;
x_31 = x_80;
goto block_79;
}
else
{
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_78; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
x_34 = lean_ctor_get(x_28, 2);
x_35 = lean_ctor_get(x_28, 3);
x_36 = lean_ctor_get(x_28, 4);
x_37 = lean_ctor_get(x_28, 5);
x_38 = lean_ctor_get(x_28, 6);
x_39 = lean_ctor_get(x_28, 7);
x_78 = !lean_is_exclusive(x_28);
if (x_78 == 0)
{
x_40 = x_28;
x_41 = x_78;
goto block_77;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_40 = lean_box(0);
x_41 = x_78;
goto block_77;
}
block_77:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 6);
x_43 = lean_array_set(x_33, x_3, x_29);
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_43);
x_44 = x_40;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_76, 0, x_32);
lean_ctor_set(x_76, 1, x_43);
lean_ctor_set(x_76, 2, x_34);
lean_ctor_set(x_76, 3, x_35);
lean_ctor_set(x_76, 4, x_36);
lean_ctor_set(x_76, 5, x_37);
lean_ctor_set(x_76, 6, x_38);
lean_ctor_set(x_76, 7, x_39);
x_44 = x_76;
goto block_75;
}
block_75:
{
if (x_42 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_3);
x_45 = lean_box(0);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_44);
lean_ctor_set(x_30, 0, x_45);
x_46 = x_30;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_44);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_46);
x_47 = x_26;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_del_object(x_30);
lean_del_object(x_26);
lean_inc_ref(x_15);
x_52 = l___private_Lake_CLI_Shake_0__Lake_Shake_getExplanations(x_15, x_3);
x_53 = lean_box(0);
x_54 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__15(x_16, x_42, x_52, x_6, x_15, x_12, x_13, x_11, x_53, x_44);
lean_dec_ref(x_12);
lean_dec_ref(x_16);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__16(x_42, x_52, x_6, x_15, x_14, x_23, x_11, x_53, x_56);
lean_dec_ref(x_14);
lean_dec_ref(x_15);
lean_dec_ref(x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_74; 
x_58 = lean_ctor_get(x_57, 0);
x_74 = !lean_is_exclusive(x_57);
if (x_74 == 0)
{
x_59 = x_57;
x_60 = x_74;
goto block_73;
}
else
{
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_71; 
x_61 = lean_ctor_get(x_58, 1);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_58, 0);
lean_dec(x_72);
x_62 = x_58;
x_63 = x_71;
goto block_70;
}
else
{
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_64; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_53);
x_64 = x_62;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_61);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_64);
x_65 = x_59;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
else
{
return x_57;
}
}
else
{
lean_dec_ref(x_52);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
return x_54;
}
}
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_3);
x_83 = lean_ctor_get(x_24, 0);
x_90 = !lean_is_exclusive(x_24);
if (x_90 == 0)
{
x_84 = x_24;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_24);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_3);
x_91 = lean_ctor_get(x_19, 0);
x_98 = !lean_is_exclusive(x_19);
if (x_98 == 0)
{
x_92 = x_19;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_19);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
block_133:
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_106);
lean_ctor_set(x_116, 2, x_105);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_113);
lean_ctor_set(x_116, 6, x_103);
lean_ctor_set(x_116, 7, x_108);
x_117 = l_Array_isEmpty___redArg(x_104);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__0));
x_119 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_104);
x_120 = lean_array_to_list(x_104);
x_121 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_120);
x_122 = lean_string_append(x_119, x_121);
lean_dec_ref(x_121);
x_123 = lean_string_append(x_118, x_122);
lean_dec_ref(x_122);
x_124 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_dec_ref(x_124);
x_10 = x_100;
x_11 = x_101;
x_12 = x_109;
x_13 = x_111;
x_14 = x_104;
x_15 = x_112;
x_16 = x_114;
x_17 = x_116;
x_18 = lean_box(0);
goto block_99;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec_ref(x_116);
lean_dec_ref(x_114);
lean_dec_ref(x_112);
lean_dec_ref(x_109);
lean_dec_ref(x_104);
lean_dec_ref(x_100);
lean_dec(x_3);
x_125 = lean_ctor_get(x_124, 0);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
x_126 = x_124;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
x_10 = x_100;
x_11 = x_101;
x_12 = x_109;
x_13 = x_111;
x_14 = x_104;
x_15 = x_112;
x_16 = x_114;
x_17 = x_116;
x_18 = lean_box(0);
goto block_99;
}
}
block_159:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_142, 2);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_142, 3);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_142, 4);
lean_inc_ref(x_148);
x_149 = lean_ctor_get(x_142, 5);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_142, 6);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_142, 7);
lean_inc_ref(x_151);
x_152 = lean_array_get_size(x_138);
x_153 = lean_nat_dec_lt(x_141, x_152);
lean_dec(x_141);
if (x_153 == 0)
{
lean_dec_ref(x_142);
x_100 = x_134;
x_101 = x_136;
x_102 = x_144;
x_103 = x_150;
x_104 = x_138;
x_105 = x_146;
x_106 = x_145;
x_107 = lean_box(0);
x_108 = x_151;
x_109 = x_135;
x_110 = x_147;
x_111 = x_137;
x_112 = x_139;
x_113 = x_149;
x_114 = x_140;
x_115 = x_148;
goto block_133;
}
else
{
uint8_t x_154; 
x_154 = lean_nat_dec_le(x_152, x_152);
if (x_154 == 0)
{
if (x_153 == 0)
{
lean_dec_ref(x_142);
x_100 = x_134;
x_101 = x_136;
x_102 = x_144;
x_103 = x_150;
x_104 = x_138;
x_105 = x_146;
x_106 = x_145;
x_107 = lean_box(0);
x_108 = x_151;
x_109 = x_135;
x_110 = x_147;
x_111 = x_137;
x_112 = x_139;
x_113 = x_149;
x_114 = x_140;
x_115 = x_148;
goto block_133;
}
else
{
size_t x_155; lean_object* x_156; 
x_155 = lean_usize_of_nat(x_152);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(x_142, x_3, x_138, x_136, x_155, x_148);
lean_dec_ref(x_142);
x_100 = x_134;
x_101 = x_136;
x_102 = x_144;
x_103 = x_150;
x_104 = x_138;
x_105 = x_146;
x_106 = x_145;
x_107 = lean_box(0);
x_108 = x_151;
x_109 = x_135;
x_110 = x_147;
x_111 = x_137;
x_112 = x_139;
x_113 = x_149;
x_114 = x_140;
x_115 = x_156;
goto block_133;
}
}
else
{
size_t x_157; lean_object* x_158; 
x_157 = lean_usize_of_nat(x_152);
x_158 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__18(x_142, x_3, x_138, x_136, x_157, x_148);
lean_dec_ref(x_142);
x_100 = x_134;
x_101 = x_136;
x_102 = x_144;
x_103 = x_150;
x_104 = x_138;
x_105 = x_146;
x_106 = x_145;
x_107 = lean_box(0);
x_108 = x_151;
x_109 = x_135;
x_110 = x_147;
x_111 = x_137;
x_112 = x_139;
x_113 = x_149;
x_114 = x_140;
x_115 = x_158;
goto block_133;
}
}
}
block_165:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
block_226:
{
uint8_t x_186; 
x_186 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 5);
if (x_186 == 0)
{
lean_dec(x_2);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_184;
x_143 = lean_box(0);
goto block_159;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_181, 7);
x_188 = lean_array_get_borrowed(x_174, x_187, x_3);
lean_inc(x_188);
x_189 = l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader(x_2, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; lean_object* x_202; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec(x_192);
x_197 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_195);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_box(0);
x_201 = lean_array_size(x_199);
lean_inc_ref(x_184);
lean_inc(x_193);
lean_inc(x_194);
x_202 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21(x_182, x_194, x_193, x_199, x_201, x_176, x_200, x_184);
lean_dec(x_199);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Array_isEmpty___redArg(x_180);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_206 = lean_ctor_get(x_194, 2);
lean_inc_ref(x_206);
lean_dec(x_194);
x_207 = l_Lean_FileMap_toPosition(x_206, x_196);
lean_dec(x_196);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_210 = lean_string_append(x_193, x_209);
x_211 = lean_nat_sub(x_208, x_178);
lean_dec(x_208);
x_212 = l_Nat_reprFast(x_211);
x_213 = lean_string_append(x_210, x_212);
lean_dec_ref(x_212);
x_214 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__2));
x_215 = lean_string_append(x_213, x_214);
x_216 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_180);
x_217 = lean_array_to_list(x_180);
x_218 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_217);
x_219 = lean_string_append(x_216, x_218);
lean_dec_ref(x_218);
x_220 = lean_string_append(x_215, x_219);
lean_dec_ref(x_219);
x_221 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__3));
x_222 = lean_string_append(x_220, x_221);
x_223 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_dec_ref(x_223);
lean_dec_ref(x_184);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_204;
x_143 = lean_box(0);
goto block_159;
}
else
{
lean_dec_ref(x_223);
lean_dec(x_204);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_184;
x_143 = lean_box(0);
goto block_159;
}
}
else
{
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_184);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_204;
x_143 = lean_box(0);
goto block_159;
}
}
else
{
lean_dec(x_196);
lean_dec(x_194);
lean_dec(x_193);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec_ref(x_184);
x_224 = lean_ctor_get(x_202, 0);
lean_inc(x_224);
lean_dec_ref(x_202);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_225;
x_143 = lean_box(0);
goto block_159;
}
else
{
lean_dec_ref(x_202);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_184;
x_143 = lean_box(0);
goto block_159;
}
}
}
else
{
lean_dec_ref(x_189);
x_134 = x_175;
x_135 = x_177;
x_136 = x_176;
x_137 = x_179;
x_138 = x_180;
x_139 = x_181;
x_140 = x_182;
x_141 = x_183;
x_142 = x_184;
x_143 = lean_box(0);
goto block_159;
}
}
}
block_254:
{
uint8_t x_238; 
x_238 = l_Array_isEmpty___redArg(x_234);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_239 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__4));
x_240 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule___closed__1));
lean_inc_ref(x_234);
x_241 = lean_array_to_list(x_234);
x_242 = l_List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17(x_241);
x_243 = lean_string_append(x_240, x_242);
lean_dec_ref(x_242);
x_244 = lean_string_append(x_239, x_243);
lean_dec_ref(x_243);
x_245 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_dec_ref(x_245);
x_175 = x_227;
x_176 = x_229;
x_177 = x_228;
x_178 = x_230;
x_179 = x_231;
x_180 = x_232;
x_181 = x_233;
x_182 = x_234;
x_183 = x_235;
x_184 = x_236;
x_185 = lean_box(0);
goto block_226;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_253; 
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_245, 0);
x_253 = !lean_is_exclusive(x_245);
if (x_253 == 0)
{
x_247 = x_245;
x_248 = x_253;
goto block_252;
}
else
{
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_box(0);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_248 == 0)
{
x_249 = x_247;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_246);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
else
{
x_175 = x_227;
x_176 = x_229;
x_177 = x_228;
x_178 = x_230;
x_179 = x_231;
x_180 = x_232;
x_181 = x_233;
x_182 = x_234;
x_183 = x_235;
x_184 = x_236;
x_185 = lean_box(0);
goto block_226;
}
}
block_304:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_263, 7);
x_268 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_parseHeader___closed__0));
x_269 = lean_array_get_borrowed(x_174, x_267, x_3);
lean_inc(x_269);
lean_inc(x_2);
x_270 = l_Lean_SearchPath_findModuleWithExt(x_2, x_268, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
if (lean_obj_tag(x_271) == 1)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_273 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_274 = lean_string_append(x_272, x_273);
x_275 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_dec_ref(x_275);
x_227 = x_256;
x_228 = x_258;
x_229 = x_257;
x_230 = x_259;
x_231 = x_260;
x_232 = x_262;
x_233 = x_263;
x_234 = x_264;
x_235 = x_265;
x_236 = x_261;
x_237 = lean_box(0);
goto block_254;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_283; 
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_258);
lean_dec_ref(x_256);
lean_dec(x_3);
lean_dec(x_2);
x_276 = lean_ctor_get(x_275, 0);
x_283 = !lean_is_exclusive(x_275);
if (x_283 == 0)
{
x_277 = x_275;
x_278 = x_283;
goto block_282;
}
else
{
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_box(0);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_278 == 0)
{
x_279 = x_277;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_276);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_271);
lean_inc(x_269);
x_284 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_269, x_266);
x_285 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__21___closed__0));
x_286 = lean_string_append(x_284, x_285);
x_287 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_dec_ref(x_287);
x_227 = x_256;
x_228 = x_258;
x_229 = x_257;
x_230 = x_259;
x_231 = x_260;
x_232 = x_262;
x_233 = x_263;
x_234 = x_264;
x_235 = x_265;
x_236 = x_261;
x_237 = lean_box(0);
goto block_254;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_295; 
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_258);
lean_dec_ref(x_256);
lean_dec(x_3);
lean_dec(x_2);
x_288 = lean_ctor_get(x_287, 0);
x_295 = !lean_is_exclusive(x_287);
if (x_295 == 0)
{
x_289 = x_287;
x_290 = x_295;
goto block_294;
}
else
{
lean_inc(x_288);
lean_dec(x_287);
x_289 = lean_box(0);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_290 == 0)
{
x_291 = x_289;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_303; 
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec_ref(x_263);
lean_dec_ref(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_258);
lean_dec_ref(x_256);
lean_dec(x_3);
lean_dec(x_2);
x_296 = lean_ctor_get(x_270, 0);
x_303 = !lean_is_exclusive(x_270);
if (x_303 == 0)
{
x_297 = x_270;
x_298 = x_303;
goto block_302;
}
else
{
lean_inc(x_296);
lean_dec(x_270);
x_297 = lean_box(0);
x_298 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_299; 
if (x_298 == 0)
{
x_299 = x_297;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_296);
x_299 = x_301;
goto block_300;
}
block_300:
{
return x_299;
}
}
}
}
block_317:
{
uint8_t x_316; 
x_316 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 6);
if (x_316 == 0)
{
x_227 = x_306;
x_228 = x_308;
x_229 = x_307;
x_230 = x_309;
x_231 = x_310;
x_232 = x_312;
x_233 = x_313;
x_234 = x_314;
x_235 = x_315;
x_236 = x_311;
x_237 = lean_box(0);
goto block_254;
}
else
{
x_255 = lean_box(0);
x_256 = x_306;
x_257 = x_307;
x_258 = x_308;
x_259 = x_309;
x_260 = x_310;
x_261 = x_311;
x_262 = x_312;
x_263 = x_313;
x_264 = x_314;
x_265 = x_315;
x_266 = x_316;
goto block_304;
}
}
block_331:
{
uint8_t x_330; 
x_330 = l_Array_isEmpty___redArg(x_328);
if (x_330 == 0)
{
if (x_319 == 0)
{
x_305 = lean_box(0);
x_306 = x_320;
x_307 = x_322;
x_308 = x_321;
x_309 = x_323;
x_310 = x_324;
x_311 = x_325;
x_312 = x_326;
x_313 = x_327;
x_314 = x_328;
x_315 = x_329;
goto block_317;
}
else
{
x_255 = lean_box(0);
x_256 = x_320;
x_257 = x_322;
x_258 = x_321;
x_259 = x_323;
x_260 = x_324;
x_261 = x_325;
x_262 = x_326;
x_263 = x_327;
x_264 = x_328;
x_265 = x_329;
x_266 = x_319;
goto block_304;
}
}
else
{
x_305 = lean_box(0);
x_306 = x_320;
x_307 = x_322;
x_308 = x_321;
x_309 = x_323;
x_310 = x_324;
x_311 = x_325;
x_312 = x_326;
x_313 = x_327;
x_314 = x_328;
x_315 = x_329;
goto block_317;
}
}
block_353:
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_351, 0, x_343);
lean_ctor_set(x_351, 1, x_346);
lean_ctor_set(x_351, 2, x_347);
lean_ctor_set(x_351, 3, x_348);
lean_ctor_set(x_351, 4, x_350);
lean_ctor_set(x_351, 5, x_341);
lean_ctor_set(x_351, 6, x_335);
lean_ctor_set(x_351, 7, x_339);
x_352 = l_Array_isEmpty___redArg(x_338);
if (x_352 == 0)
{
if (x_332 == 0)
{
x_318 = lean_box(0);
x_319 = x_332;
x_320 = x_334;
x_321 = x_342;
x_322 = x_336;
x_323 = x_337;
x_324 = x_344;
x_325 = x_351;
x_326 = x_338;
x_327 = x_345;
x_328 = x_349;
x_329 = x_340;
goto block_331;
}
else
{
x_255 = lean_box(0);
x_256 = x_334;
x_257 = x_336;
x_258 = x_342;
x_259 = x_337;
x_260 = x_344;
x_261 = x_351;
x_262 = x_338;
x_263 = x_345;
x_264 = x_349;
x_265 = x_340;
x_266 = x_332;
goto block_304;
}
}
else
{
x_318 = lean_box(0);
x_319 = x_332;
x_320 = x_334;
x_321 = x_342;
x_322 = x_336;
x_323 = x_337;
x_324 = x_344;
x_325 = x_351;
x_326 = x_338;
x_327 = x_345;
x_328 = x_349;
x_329 = x_340;
goto block_331;
}
}
block_399:
{
lean_object* x_371; 
x_371 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__12(x_364, x_357, x_367, x_6, x_366, x_360, x_362, x_359, x_363, x_369);
lean_dec_ref(x_366);
lean_dec_ref(x_367);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
lean_dec_ref(x_371);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 0);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_ctor_get(x_373, 0);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_373, 1);
lean_inc_ref(x_376);
x_377 = lean_ctor_get(x_373, 2);
lean_inc_ref(x_377);
x_378 = lean_ctor_get(x_373, 3);
lean_inc_ref(x_378);
x_379 = lean_ctor_get(x_373, 4);
lean_inc_ref(x_379);
x_380 = lean_ctor_get(x_373, 5);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_373, 6);
lean_inc_ref(x_381);
x_382 = lean_ctor_get(x_373, 7);
lean_inc_ref(x_382);
lean_dec(x_373);
x_383 = l_Array_append___redArg(x_356, x_368);
lean_dec_ref(x_368);
x_384 = lean_array_get_size(x_374);
x_385 = lean_nat_dec_lt(x_365, x_384);
if (x_385 == 0)
{
lean_dec(x_355);
x_332 = x_357;
x_333 = lean_box(0);
x_334 = x_358;
x_335 = x_381;
x_336 = x_359;
x_337 = x_361;
x_338 = x_383;
x_339 = x_382;
x_340 = x_365;
x_341 = x_380;
x_342 = x_360;
x_343 = x_375;
x_344 = x_362;
x_345 = x_364;
x_346 = x_376;
x_347 = x_377;
x_348 = x_378;
x_349 = x_374;
x_350 = x_379;
goto block_353;
}
else
{
uint8_t x_386; 
x_386 = lean_nat_dec_le(x_384, x_384);
if (x_386 == 0)
{
if (x_385 == 0)
{
lean_dec(x_355);
x_332 = x_357;
x_333 = lean_box(0);
x_334 = x_358;
x_335 = x_381;
x_336 = x_359;
x_337 = x_361;
x_338 = x_383;
x_339 = x_382;
x_340 = x_365;
x_341 = x_380;
x_342 = x_360;
x_343 = x_375;
x_344 = x_362;
x_345 = x_364;
x_346 = x_376;
x_347 = x_377;
x_348 = x_378;
x_349 = x_374;
x_350 = x_379;
goto block_353;
}
else
{
size_t x_387; lean_object* x_388; 
x_387 = lean_usize_of_nat(x_384);
x_388 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(x_355, x_374, x_359, x_387, x_379);
x_332 = x_357;
x_333 = lean_box(0);
x_334 = x_358;
x_335 = x_381;
x_336 = x_359;
x_337 = x_361;
x_338 = x_383;
x_339 = x_382;
x_340 = x_365;
x_341 = x_380;
x_342 = x_360;
x_343 = x_375;
x_344 = x_362;
x_345 = x_364;
x_346 = x_376;
x_347 = x_377;
x_348 = x_378;
x_349 = x_374;
x_350 = x_388;
goto block_353;
}
}
else
{
size_t x_389; lean_object* x_390; 
x_389 = lean_usize_of_nat(x_384);
x_390 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__22(x_355, x_374, x_359, x_389, x_379);
x_332 = x_357;
x_333 = lean_box(0);
x_334 = x_358;
x_335 = x_381;
x_336 = x_359;
x_337 = x_361;
x_338 = x_383;
x_339 = x_382;
x_340 = x_365;
x_341 = x_380;
x_342 = x_360;
x_343 = x_375;
x_344 = x_362;
x_345 = x_364;
x_346 = x_376;
x_347 = x_377;
x_348 = x_378;
x_349 = x_374;
x_350 = x_390;
goto block_353;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_398; 
lean_dec_ref(x_368);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_360);
lean_dec_ref(x_358);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec(x_3);
lean_dec(x_2);
x_391 = lean_ctor_get(x_371, 0);
x_398 = !lean_is_exclusive(x_371);
if (x_398 == 0)
{
x_392 = x_371;
x_393 = x_398;
goto block_397;
}
else
{
lean_inc(x_391);
lean_dec(x_371);
x_392 = lean_box(0);
x_393 = x_398;
goto block_397;
}
block_397:
{
lean_object* x_394; 
if (x_393 == 0)
{
x_394 = x_392;
goto block_395;
}
else
{
lean_object* x_396; 
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_391);
x_394 = x_396;
goto block_395;
}
block_395:
{
return x_394;
}
}
}
}
block_516:
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; size_t x_417; lean_object* x_418; 
x_411 = lean_array_get(x_354, x_405, x_3);
lean_dec_ref(x_405);
x_412 = lean_ctor_get(x_411, 0);
lean_inc_ref(x_412);
lean_dec(x_411);
x_413 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeeds_default));
x_414 = lean_mk_empty_array_with_capacity(x_407);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_408);
lean_ctor_set(x_415, 1, x_413);
lean_inc_ref(x_414);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = lean_array_size(x_412);
x_418 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__11(x_404, x_355, x_412, x_6, x_412, x_417, x_401, x_416, x_409);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; uint8_t x_506; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_419, 1);
x_506 = !lean_is_exclusive(x_419);
if (x_506 == 0)
{
lean_object* x_507; 
x_507 = lean_ctor_get(x_419, 0);
lean_dec(x_507);
x_423 = x_419;
x_424 = x_506;
goto block_505;
}
else
{
lean_inc(x_422);
lean_dec(x_419);
x_423 = lean_box(0);
x_424 = x_506;
goto block_505;
}
block_505:
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; uint8_t x_503; 
x_425 = lean_ctor_get(x_420, 0);
x_503 = !lean_is_exclusive(x_420);
if (x_503 == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_420, 1);
lean_dec(x_504);
x_426 = x_420;
x_427 = x_503;
goto block_502;
}
else
{
lean_inc(x_425);
lean_dec(x_420);
x_426 = lean_box(0);
x_427 = x_503;
goto block_502;
}
block_502:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_501; 
x_428 = lean_ctor_get(x_421, 0);
x_429 = lean_ctor_get(x_421, 1);
x_501 = !lean_is_exclusive(x_421);
if (x_501 == 0)
{
x_430 = x_421;
x_431 = x_501;
goto block_500;
}
else
{
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_421);
x_430 = lean_box(0);
x_431 = x_501;
goto block_500;
}
block_500:
{
lean_object* x_432; lean_object* x_433; 
lean_inc(x_407);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_407);
if (x_424 == 0)
{
lean_ctor_set(x_423, 1, x_403);
lean_ctor_set(x_423, 0, x_432);
x_433 = x_423;
goto block_498;
}
else
{
lean_object* x_499; 
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_432);
lean_ctor_set(x_499, 1, x_403);
x_433 = x_499;
goto block_498;
}
block_498:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_inc_ref(x_414);
x_434 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__23___redArg(x_433, x_414);
x_435 = l_Array_reverse___redArg(x_434);
lean_inc_ref(x_414);
lean_inc(x_429);
if (x_431 == 0)
{
lean_ctor_set(x_430, 1, x_414);
lean_ctor_set(x_430, 0, x_429);
x_436 = x_430;
goto block_496;
}
else
{
lean_object* x_497; 
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_429);
lean_ctor_set(x_497, 1, x_414);
x_436 = x_497;
goto block_496;
}
block_496:
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_box(x_406);
if (x_427 == 0)
{
lean_ctor_set(x_426, 1, x_436);
lean_ctor_set(x_426, 0, x_437);
x_438 = x_426;
goto block_494;
}
else
{
lean_object* x_495; 
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_437);
lean_ctor_set(x_495, 1, x_436);
x_438 = x_495;
goto block_494;
}
block_494:
{
lean_object* x_439; size_t x_440; lean_object* x_441; 
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_428);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_array_size(x_435);
x_441 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__24(x_404, x_412, x_6, x_3, x_4, x_435, x_440, x_401, x_439, x_422);
lean_dec_ref(x_4);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; uint8_t x_485; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_dec_ref(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_444, 1);
x_446 = lean_ctor_get(x_444, 0);
x_485 = !lean_is_exclusive(x_444);
if (x_485 == 0)
{
x_447 = x_444;
x_448 = x_485;
goto block_484;
}
else
{
lean_inc(x_445);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_box(0);
x_448 = x_485;
goto block_484;
}
block_484:
{
uint8_t x_449; 
x_449 = lean_unbox(x_446);
lean_dec(x_446);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_del_object(x_447);
lean_dec_ref(x_435);
lean_dec(x_429);
x_450 = lean_ctor_get(x_442, 1);
lean_inc(x_450);
lean_dec(x_442);
x_451 = lean_ctor_get(x_443, 0);
lean_inc(x_451);
lean_dec(x_443);
x_452 = lean_ctor_get(x_445, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_445, 1);
lean_inc(x_453);
lean_dec(x_445);
x_356 = x_425;
x_357 = x_400;
x_358 = x_413;
x_359 = x_401;
x_360 = x_412;
x_361 = x_402;
x_362 = x_417;
x_363 = x_414;
x_364 = x_404;
x_365 = x_407;
x_366 = x_451;
x_367 = x_452;
x_368 = x_453;
x_369 = x_450;
x_370 = lean_box(0);
goto block_399;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_482; 
x_454 = lean_ctor_get(x_442, 1);
lean_inc(x_454);
lean_dec(x_442);
x_455 = lean_ctor_get(x_443, 0);
lean_inc(x_455);
lean_dec(x_443);
x_456 = lean_ctor_get(x_445, 1);
x_482 = !lean_is_exclusive(x_445);
if (x_482 == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_445, 0);
lean_dec(x_483);
x_457 = x_445;
x_458 = x_482;
goto block_481;
}
else
{
lean_inc(x_456);
lean_dec(x_445);
x_457 = lean_box(0);
x_458 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_459; 
if (x_458 == 0)
{
lean_ctor_set(x_457, 0, x_429);
x_459 = x_457;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_429);
lean_ctor_set(x_480, 1, x_456);
x_459 = x_480;
goto block_479;
}
block_479:
{
lean_object* x_460; 
if (x_448 == 0)
{
lean_ctor_set(x_447, 1, x_459);
lean_ctor_set(x_447, 0, x_455);
x_460 = x_447;
goto block_477;
}
else
{
lean_object* x_478; 
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_455);
lean_ctor_set(x_478, 1, x_459);
x_460 = x_478;
goto block_477;
}
block_477:
{
lean_object* x_461; 
x_461 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__25(x_404, x_6, x_400, x_435, x_440, x_401, x_460, x_454);
lean_dec_ref(x_435);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_dec_ref(x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_dec(x_462);
x_466 = lean_ctor_get(x_463, 0);
lean_inc(x_466);
lean_dec(x_463);
x_467 = lean_ctor_get(x_464, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_464, 1);
lean_inc(x_468);
lean_dec(x_464);
x_356 = x_425;
x_357 = x_400;
x_358 = x_413;
x_359 = x_401;
x_360 = x_412;
x_361 = x_402;
x_362 = x_417;
x_363 = x_414;
x_364 = x_404;
x_365 = x_407;
x_366 = x_466;
x_367 = x_467;
x_368 = x_468;
x_369 = x_465;
x_370 = lean_box(0);
goto block_399;
}
else
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; uint8_t x_476; 
lean_dec(x_425);
lean_dec_ref(x_414);
lean_dec_ref(x_412);
lean_dec(x_407);
lean_dec_ref(x_404);
lean_dec(x_355);
lean_dec(x_3);
lean_dec(x_2);
x_469 = lean_ctor_get(x_461, 0);
x_476 = !lean_is_exclusive(x_461);
if (x_476 == 0)
{
x_470 = x_461;
x_471 = x_476;
goto block_475;
}
else
{
lean_inc(x_469);
lean_dec(x_461);
x_470 = lean_box(0);
x_471 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_472; 
if (x_471 == 0)
{
x_472 = x_470;
goto block_473;
}
else
{
lean_object* x_474; 
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_469);
x_472 = x_474;
goto block_473;
}
block_473:
{
return x_472;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_486; lean_object* x_487; uint8_t x_488; uint8_t x_493; 
lean_dec_ref(x_435);
lean_dec(x_429);
lean_dec(x_425);
lean_dec_ref(x_414);
lean_dec_ref(x_412);
lean_dec(x_407);
lean_dec_ref(x_404);
lean_dec(x_355);
lean_dec(x_3);
lean_dec(x_2);
x_486 = lean_ctor_get(x_441, 0);
x_493 = !lean_is_exclusive(x_441);
if (x_493 == 0)
{
x_487 = x_441;
x_488 = x_493;
goto block_492;
}
else
{
lean_inc(x_486);
lean_dec(x_441);
x_487 = lean_box(0);
x_488 = x_493;
goto block_492;
}
block_492:
{
lean_object* x_489; 
if (x_488 == 0)
{
x_489 = x_487;
goto block_490;
}
else
{
lean_object* x_491; 
x_491 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_491, 0, x_486);
x_489 = x_491;
goto block_490;
}
block_490:
{
return x_489;
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
else
{
lean_object* x_508; lean_object* x_509; uint8_t x_510; uint8_t x_515; 
lean_dec_ref(x_414);
lean_dec_ref(x_412);
lean_dec(x_407);
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec(x_355);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_508 = lean_ctor_get(x_418, 0);
x_515 = !lean_is_exclusive(x_418);
if (x_515 == 0)
{
x_509 = x_418;
x_510 = x_515;
goto block_514;
}
else
{
lean_inc(x_508);
lean_dec(x_418);
x_509 = lean_box(0);
x_510 = x_515;
goto block_514;
}
block_514:
{
lean_object* x_511; 
if (x_510 == 0)
{
x_511 = x_509;
goto block_512;
}
else
{
lean_object* x_513; 
x_513 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_513, 0, x_508);
x_511 = x_513;
goto block_512;
}
block_512:
{
return x_511;
}
}
}
}
block_533:
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_529 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_529, 0, x_517);
lean_ctor_set_uint8(x_529, 1, x_527);
x_530 = lean_nat_shiftl(x_519, x_528);
lean_dec(x_528);
x_531 = lean_nat_lor(x_526, x_530);
lean_dec(x_530);
x_532 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_525, x_529, x_531);
lean_dec_ref(x_529);
x_400 = x_517;
x_401 = x_518;
x_402 = x_519;
x_403 = x_520;
x_404 = x_522;
x_405 = x_524;
x_406 = x_527;
x_407 = x_526;
x_408 = x_532;
x_409 = x_521;
x_410 = lean_box(0);
goto block_516;
}
block_552:
{
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_539, 0);
x_547 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9___closed__3));
x_548 = l_Lean_Environment_getModuleIdx_x3f(x_546, x_547);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_550 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__0(x_549);
x_517 = x_534;
x_518 = x_535;
x_519 = x_536;
x_520 = x_537;
x_521 = x_544;
x_522 = x_539;
x_523 = lean_box(0);
x_524 = x_540;
x_525 = x_543;
x_526 = x_542;
x_527 = x_541;
x_528 = x_550;
goto block_533;
}
else
{
lean_object* x_551; 
x_551 = lean_ctor_get(x_548, 0);
lean_inc(x_551);
lean_dec_ref(x_548);
x_517 = x_534;
x_518 = x_535;
x_519 = x_536;
x_520 = x_537;
x_521 = x_544;
x_522 = x_539;
x_523 = lean_box(0);
x_524 = x_540;
x_525 = x_543;
x_526 = x_542;
x_527 = x_541;
x_528 = x_551;
goto block_533;
}
}
else
{
lean_dec_ref(x_538);
x_400 = x_534;
x_401 = x_535;
x_402 = x_536;
x_403 = x_537;
x_404 = x_539;
x_405 = x_540;
x_406 = x_541;
x_407 = x_542;
x_408 = x_543;
x_409 = x_544;
x_410 = lean_box(0);
goto block_516;
}
}
block_605:
{
size_t x_562; lean_object* x_563; 
x_562 = lean_array_size(x_557);
lean_inc_ref(x_4);
lean_inc_ref(x_556);
x_563 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__9(x_6, x_561, x_355, x_556, x_557, x_562, x_554, x_4, x_556);
lean_dec_ref(x_557);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_556);
x_568 = lean_array_get_size(x_567);
x_569 = lean_unsigned_to_nat(1u);
lean_inc(x_558);
x_570 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_570, 0, x_558);
lean_ctor_set(x_570, 1, x_568);
lean_ctor_set(x_570, 2, x_569);
lean_inc(x_558);
x_571 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__26___redArg(x_6, x_556, x_3, x_570, x_565, x_558, x_566);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
if (x_561 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
lean_inc(x_558);
x_575 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__27___redArg(x_556, x_570, x_573, x_558, x_574);
lean_dec_ref(x_570);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_534 = x_553;
x_535 = x_554;
x_536 = x_569;
x_537 = x_568;
x_538 = x_555;
x_539 = x_556;
x_540 = x_567;
x_541 = x_559;
x_542 = x_558;
x_543 = x_577;
x_544 = x_578;
x_545 = lean_box(0);
goto block_552;
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec(x_355);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_579 = lean_ctor_get(x_575, 0);
x_586 = !lean_is_exclusive(x_575);
if (x_586 == 0)
{
x_580 = x_575;
x_581 = x_586;
goto block_585;
}
else
{
lean_inc(x_579);
lean_dec(x_575);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; 
lean_dec_ref(x_570);
x_587 = lean_ctor_get(x_572, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_572, 1);
lean_inc(x_588);
lean_dec(x_572);
x_534 = x_553;
x_535 = x_554;
x_536 = x_569;
x_537 = x_568;
x_538 = x_555;
x_539 = x_556;
x_540 = x_567;
x_541 = x_559;
x_542 = x_558;
x_543 = x_587;
x_544 = x_588;
x_545 = lean_box(0);
goto block_552;
}
}
else
{
lean_object* x_589; lean_object* x_590; uint8_t x_591; uint8_t x_596; 
lean_dec_ref(x_570);
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec(x_355);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_589 = lean_ctor_get(x_571, 0);
x_596 = !lean_is_exclusive(x_571);
if (x_596 == 0)
{
x_590 = x_571;
x_591 = x_596;
goto block_595;
}
else
{
lean_inc(x_589);
lean_dec(x_571);
x_590 = lean_box(0);
x_591 = x_596;
goto block_595;
}
block_595:
{
lean_object* x_592; 
if (x_591 == 0)
{
x_592 = x_590;
goto block_593;
}
else
{
lean_object* x_594; 
x_594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_594, 0, x_589);
x_592 = x_594;
goto block_593;
}
block_593:
{
return x_592;
}
}
}
}
else
{
lean_object* x_597; lean_object* x_598; uint8_t x_599; uint8_t x_604; 
lean_dec(x_558);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec(x_355);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_597 = lean_ctor_get(x_563, 0);
x_604 = !lean_is_exclusive(x_563);
if (x_604 == 0)
{
x_598 = x_563;
x_599 = x_604;
goto block_603;
}
else
{
lean_inc(x_597);
lean_dec(x_563);
x_598 = lean_box(0);
x_599 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_600; 
if (x_599 == 0)
{
x_600 = x_598;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_597);
x_600 = x_602;
goto block_601;
}
block_601:
{
return x_600;
}
}
}
}
block_632:
{
if (lean_obj_tag(x_608) == 0)
{
x_553 = x_606;
x_554 = x_607;
x_555 = x_609;
x_556 = x_611;
x_557 = x_610;
x_558 = x_614;
x_559 = x_613;
x_560 = lean_box(0);
x_561 = x_615;
goto block_605;
}
else
{
lean_object* x_616; lean_object* x_617; 
x_616 = lean_ctor_get(x_608, 0);
lean_inc(x_616);
lean_dec_ref(x_608);
x_617 = l_Lean_Syntax_getTrailing_x3f(x_616);
lean_dec(x_616);
if (lean_obj_tag(x_617) == 0)
{
x_553 = x_606;
x_554 = x_607;
x_555 = x_609;
x_556 = x_611;
x_557 = x_610;
x_558 = x_614;
x_559 = x_613;
x_560 = lean_box(0);
x_561 = x_615;
goto block_605;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_631; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
lean_dec_ref(x_617);
x_619 = lean_ctor_get(x_618, 0);
x_620 = lean_ctor_get(x_618, 1);
x_621 = lean_ctor_get(x_618, 2);
x_631 = !lean_is_exclusive(x_618);
if (x_631 == 0)
{
x_622 = x_618;
x_623 = x_631;
goto block_630;
}
else
{
lean_inc(x_621);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_618);
x_622 = lean_box(0);
x_623 = x_631;
goto block_630;
}
block_630:
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_string_utf8_extract(x_619, x_620, x_621);
lean_dec(x_621);
lean_dec(x_620);
lean_dec_ref(x_619);
x_625 = lean_string_utf8_byte_size(x_624);
lean_inc(x_614);
if (x_623 == 0)
{
lean_ctor_set(x_622, 2, x_625);
lean_ctor_set(x_622, 1, x_614);
lean_ctor_set(x_622, 0, x_624);
x_626 = x_622;
goto block_628;
}
else
{
lean_object* x_629; 
x_629 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_629, 0, x_624);
lean_ctor_set(x_629, 1, x_614);
lean_ctor_set(x_629, 2, x_625);
x_626 = x_629;
goto block_628;
}
block_628:
{
uint8_t x_627; 
x_627 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__28(x_626);
lean_dec_ref(x_626);
x_553 = x_606;
x_554 = x_607;
x_555 = x_609;
x_556 = x_611;
x_557 = x_610;
x_558 = x_614;
x_559 = x_613;
x_560 = lean_box(0);
x_561 = x_627;
goto block_605;
}
}
}
}
}
block_645:
{
if (x_7 == 0)
{
lean_object* x_642; uint8_t x_643; 
x_642 = lean_ctor_get(x_6, 1);
x_643 = l_Array_isEmpty___redArg(x_642);
if (x_643 == 0)
{
uint8_t x_644; 
x_644 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__29(x_642, x_355);
if (x_644 == 0)
{
if (x_633 == 0)
{
x_606 = x_633;
x_607 = x_634;
x_608 = x_635;
x_609 = x_636;
x_610 = x_637;
x_611 = x_640;
x_612 = lean_box(0);
x_613 = x_638;
x_614 = x_639;
x_615 = x_633;
goto block_632;
}
else
{
lean_dec(x_635);
x_553 = x_633;
x_554 = x_634;
x_555 = x_636;
x_556 = x_640;
x_557 = x_637;
x_558 = x_639;
x_559 = x_638;
x_560 = lean_box(0);
x_561 = x_633;
goto block_605;
}
}
else
{
x_606 = x_633;
x_607 = x_634;
x_608 = x_635;
x_609 = x_636;
x_610 = x_637;
x_611 = x_640;
x_612 = lean_box(0);
x_613 = x_638;
x_614 = x_639;
x_615 = x_7;
goto block_632;
}
}
else
{
x_606 = x_633;
x_607 = x_634;
x_608 = x_635;
x_609 = x_636;
x_610 = x_637;
x_611 = x_640;
x_612 = lean_box(0);
x_613 = x_638;
x_614 = x_639;
x_615 = x_7;
goto block_632;
}
}
else
{
lean_dec(x_635);
x_553 = x_633;
x_554 = x_634;
x_555 = x_636;
x_556 = x_640;
x_557 = x_637;
x_558 = x_639;
x_559 = x_638;
x_560 = lean_box(0);
x_561 = x_7;
goto block_605;
}
}
block_668:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_663 = lean_unsigned_to_nat(1u);
x_664 = lean_nat_shiftl(x_663, x_3);
x_665 = lean_nat_lor(x_650, x_664);
lean_dec(x_664);
x_666 = l___private_Lake_CLI_Shake_0__Lake_Shake_Needs_union(x_653, x_662, x_665);
lean_dec_ref(x_662);
x_667 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_667, 0, x_658);
lean_ctor_set(x_667, 1, x_656);
lean_ctor_set(x_667, 2, x_657);
lean_ctor_set(x_667, 3, x_666);
lean_ctor_set(x_667, 4, x_659);
lean_ctor_set(x_667, 5, x_648);
lean_ctor_set(x_667, 6, x_651);
lean_ctor_set(x_667, 7, x_655);
x_633 = x_646;
x_634 = x_647;
x_635 = x_652;
x_636 = x_654;
x_637 = x_649;
x_638 = x_661;
x_639 = x_650;
x_640 = x_667;
x_641 = lean_box(0);
goto block_645;
}
block_718:
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_671 = lean_unsigned_to_nat(0u);
x_672 = lean_array_get_size(x_1);
x_673 = lean_nat_dec_lt(x_671, x_672);
if (x_673 == 0)
{
lean_dec(x_355);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = x_669;
x_161 = lean_box(0);
goto block_165;
}
else
{
if (x_673 == 0)
{
lean_dec(x_355);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = x_669;
x_161 = lean_box(0);
goto block_165;
}
else
{
size_t x_674; size_t x_675; uint8_t x_676; 
x_674 = 0;
x_675 = lean_usize_of_nat(x_672);
x_676 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__0(x_355, x_1, x_674, x_675);
if (x_676 == 0)
{
lean_dec(x_355);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = x_669;
x_161 = lean_box(0);
goto block_165;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_677 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_5);
x_678 = lean_ctor_get(x_677, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 0);
lean_inc(x_679);
lean_dec_ref(x_677);
x_680 = lean_ctor_get(x_678, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_678, 1);
lean_inc(x_681);
lean_dec(x_678);
x_682 = 0;
if (lean_obj_tag(x_679) == 0)
{
x_633 = x_676;
x_634 = x_674;
x_635 = x_679;
x_636 = x_680;
x_637 = x_681;
x_638 = x_682;
x_639 = x_671;
x_640 = x_669;
x_641 = lean_box(0);
goto block_645;
}
else
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_ctor_get(x_679, 0);
x_684 = l_Lean_Syntax_getTrailing_x3f(x_683);
if (lean_obj_tag(x_684) == 0)
{
x_633 = x_676;
x_634 = x_674;
x_635 = x_679;
x_636 = x_680;
x_637 = x_681;
x_638 = x_682;
x_639 = x_671;
x_640 = x_669;
x_641 = lean_box(0);
goto block_645;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; uint8_t x_717; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
lean_dec_ref(x_684);
x_686 = lean_ctor_get(x_685, 0);
x_687 = lean_ctor_get(x_685, 1);
x_688 = lean_ctor_get(x_685, 2);
x_717 = !lean_is_exclusive(x_685);
if (x_717 == 0)
{
x_689 = x_685;
x_690 = x_717;
goto block_716;
}
else
{
lean_inc(x_688);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_685);
x_689 = lean_box(0);
x_690 = x_717;
goto block_716;
}
block_716:
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_string_utf8_extract(x_686, x_687, x_688);
lean_dec(x_688);
lean_dec(x_687);
lean_dec_ref(x_686);
x_692 = lean_string_utf8_byte_size(x_691);
if (x_690 == 0)
{
lean_ctor_set(x_689, 2, x_692);
lean_ctor_set(x_689, 1, x_671);
lean_ctor_set(x_689, 0, x_691);
x_693 = x_689;
goto block_714;
}
else
{
lean_object* x_715; 
x_715 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_715, 0, x_691);
lean_ctor_set(x_715, 1, x_671);
lean_ctor_set(x_715, 2, x_692);
x_693 = x_715;
goto block_714;
}
block_714:
{
uint8_t x_694; 
x_694 = l_String_Slice_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__30(x_693);
lean_dec_ref(x_693);
if (x_694 == 0)
{
x_633 = x_676;
x_634 = x_674;
x_635 = x_679;
x_636 = x_680;
x_637 = x_681;
x_638 = x_682;
x_639 = x_671;
x_640 = x_669;
x_641 = lean_box(0);
goto block_645;
}
else
{
uint8_t x_695; 
x_695 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 3);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_696 = lean_ctor_get(x_669, 0);
lean_inc_ref(x_696);
x_697 = lean_ctor_get(x_669, 1);
lean_inc_ref(x_697);
x_698 = lean_ctor_get(x_669, 2);
lean_inc_ref(x_698);
x_699 = lean_ctor_get(x_669, 3);
lean_inc_ref(x_699);
x_700 = lean_ctor_get(x_669, 4);
lean_inc_ref(x_700);
x_701 = lean_ctor_get(x_669, 5);
lean_inc_ref(x_701);
x_702 = lean_ctor_get(x_669, 6);
lean_inc_ref(x_702);
x_703 = lean_ctor_get(x_669, 7);
lean_inc_ref(x_703);
lean_dec_ref(x_669);
x_704 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedNeedsKind_default___closed__0));
x_646 = x_676;
x_647 = x_674;
x_648 = x_701;
x_649 = x_681;
x_650 = x_671;
x_651 = x_702;
x_652 = x_679;
x_653 = x_699;
x_654 = x_680;
x_655 = x_703;
x_656 = x_697;
x_657 = x_698;
x_658 = x_696;
x_659 = x_700;
x_660 = lean_box(0);
x_661 = x_682;
x_662 = x_704;
goto block_668;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_705 = lean_ctor_get(x_669, 0);
lean_inc_ref(x_705);
x_706 = lean_ctor_get(x_669, 1);
lean_inc_ref(x_706);
x_707 = lean_ctor_get(x_669, 2);
lean_inc_ref(x_707);
x_708 = lean_ctor_get(x_669, 3);
lean_inc_ref(x_708);
x_709 = lean_ctor_get(x_669, 4);
lean_inc_ref(x_709);
x_710 = lean_ctor_get(x_669, 5);
lean_inc_ref(x_710);
x_711 = lean_ctor_get(x_669, 6);
lean_inc_ref(x_711);
x_712 = lean_ctor_get(x_669, 7);
lean_inc_ref(x_712);
lean_dec_ref(x_669);
x_713 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_713, 0, x_694);
lean_ctor_set_uint8(x_713, 1, x_682);
x_646 = x_676;
x_647 = x_674;
x_648 = x_710;
x_649 = x_681;
x_650 = x_671;
x_651 = x_711;
x_652 = x_679;
x_653 = x_708;
x_654 = x_680;
x_655 = x_712;
x_656 = x_706;
x_657 = x_707;
x_658 = x_705;
x_659 = x_709;
x_660 = lean_box(0);
x_661 = x_682;
x_662 = x_713;
goto block_668;
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
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__2));
x_2 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__1));
x_3 = l_lexOrd___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__0));
x_2 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3, &l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__3);
x_3 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4, &l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake___closed__4);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_105; 
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 0);
x_105 = !lean_is_exclusive(x_5);
if (x_105 == 0)
{
x_28 = x_5;
x_29 = x_105;
goto block_104;
}
else
{
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
x_32 = lean_ctor_get(x_26, 2);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_2);
if (x_29 == 0)
{
x_34 = x_28;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_26);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_9 = x_34;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_37; uint8_t x_38; uint8_t x_100; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc_ref(x_30);
x_100 = !lean_is_exclusive(x_26);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_26, 2);
lean_dec(x_101);
x_102 = lean_ctor_get(x_26, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_26, 0);
lean_dec(x_103);
x_37 = x_26;
x_38 = x_100;
goto block_99;
}
else
{
lean_dec(x_26);
x_37 = lean_box(0);
x_38 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
x_41 = lean_ctor_get(x_27, 2);
x_42 = lean_array_fget(x_30, x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_31, x_43);
lean_dec(x_31);
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_44);
x_45 = x_37;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_30);
lean_ctor_set(x_98, 1, x_44);
lean_ctor_set(x_98, 2, x_32);
x_45 = x_98;
goto block_97;
}
block_97:
{
uint8_t x_46; 
x_46 = lean_nat_dec_lt(x_40, x_41);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_2);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_45);
x_47 = x_28;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_45);
x_47 = x_49;
goto block_48;
}
block_48:
{
x_9 = x_47;
x_10 = x_7;
x_11 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_50; uint8_t x_51; uint8_t x_93; 
lean_inc(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
x_93 = !lean_is_exclusive(x_27);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_27, 2);
lean_dec(x_94);
x_95 = lean_ctor_get(x_27, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_27, 0);
lean_dec(x_96);
x_50 = x_27;
x_51 = x_93;
goto block_92;
}
else
{
lean_dec(x_27);
x_50 = lean_box(0);
x_51 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_array_fget(x_39, x_40);
x_53 = lean_nat_add(x_40, x_43);
lean_dec(x_40);
if (x_51 == 0)
{
lean_ctor_set(x_50, 1, x_53);
x_54 = x_50;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_39);
lean_ctor_set(x_91, 1, x_53);
lean_ctor_set(x_91, 2, x_41);
x_54 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_55; 
x_55 = lean_task_get_own(x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_io_error_to_string(x_56);
x_58 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec_ref(x_58);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_45);
lean_ctor_set(x_28, 0, x_54);
x_59 = x_28;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_45);
x_59 = x_61;
goto block_60;
}
block_60:
{
x_17 = x_59;
x_18 = x_7;
x_19 = lean_box(0);
goto block_22;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_54);
lean_dec_ref(x_45);
lean_del_object(x_28);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_62 = lean_ctor_get(x_58, 0);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
x_63 = x_58;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_55, 0);
lean_inc(x_70);
lean_dec_ref(x_55);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = 0;
x_75 = lean_task_get_own(x_52);
lean_inc(x_6);
lean_inc(x_2);
x_76 = l___private_Lake_CLI_Shake_0__Lake_Shake_visitModule(x_1, x_2, x_6, x_75, x_73, x_3, x_74, x_7);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_45);
lean_ctor_set(x_28, 0, x_54);
x_79 = x_28;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_54);
lean_ctor_set(x_81, 1, x_45);
x_79 = x_81;
goto block_80;
}
block_80:
{
x_17 = x_79;
x_18 = x_78;
x_19 = lean_box(0);
goto block_22;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec_ref(x_54);
lean_dec_ref(x_45);
lean_del_object(x_28);
lean_dec(x_6);
lean_dec(x_2);
x_82 = lean_ctor_get(x_76, 0);
x_89 = !lean_is_exclusive(x_76);
if (x_89 == 0)
{
x_83 = x_76;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
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
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_2, x_17);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_instHashableImport_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
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
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6_spec__6___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_41; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_21 = x_1;
x_22 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_19);
x_26 = lean_array_uset(x_5, x_18, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7_spec__8___redArg(x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_24);
x_34 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_24);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_80; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 0);
x_80 = !lean_is_exclusive(x_6);
if (x_80 == 0)
{
x_14 = x_6;
x_15 = x_80;
goto block_79;
}
else
{
lean_inc(x_12);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_78; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
x_18 = x_12;
x_19 = x_78;
goto block_77;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = x_78;
goto block_77;
}
block_77:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_58; uint8_t x_75; 
x_20 = 0;
x_21 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_21);
x_22 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeImport(x_21);
x_75 = l_Array_contains___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__4(x_2, x_22);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_17, x_22);
if (x_76 == 0)
{
x_23 = x_13;
x_24 = x_16;
x_25 = x_7;
x_26 = lean_box(0);
goto block_38;
}
else
{
goto block_74;
}
}
else
{
goto block_74;
}
block_38:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(x_17, x_22, x_27);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_24);
x_29 = x_18;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_28);
x_29 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_30; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_29);
lean_ctor_set(x_14, 0, x_23);
x_30 = x_14;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_29);
x_30 = x_35;
goto block_34;
}
block_34:
{
size_t x_31; size_t x_32; 
x_31 = 1;
x_32 = lean_usize_add(x_5, x_31);
x_5 = x_32;
x_6 = x_30;
x_7 = x_25;
goto _start;
}
}
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_nat_add(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
x_44 = l_String_Slice_Pos_next_x21(x_39, x_43);
lean_dec(x_43);
lean_dec_ref(x_39);
x_23 = x_41;
x_24 = x_44;
x_25 = x_7;
x_26 = lean_box(0);
goto block_38;
}
block_57:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_String_Slice_pos_x21(x_46, x_50);
lean_dec(x_50);
lean_inc(x_48);
lean_inc(x_51);
lean_inc_ref(x_1);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
x_53 = lean_box(0);
x_54 = l_WellFounded_opaqueFix_u2083___at___00Lake_Shake_run_spec__8___redArg(x_52, x_51, x_1, x_49, x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_39 = x_46;
x_40 = x_51;
x_41 = x_47;
x_42 = x_55;
goto block_45;
}
else
{
lean_object* x_56; 
lean_dec(x_48);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
x_39 = x_46;
x_40 = x_51;
x_41 = x_47;
x_42 = x_56;
goto block_45;
}
}
block_69:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = l_String_Slice_pos_x21(x_61, x_58);
lean_dec(x_58);
x_63 = lean_string_utf8_extract(x_1, x_16, x_62);
lean_dec(x_62);
lean_dec(x_16);
x_64 = lean_string_append(x_13, x_63);
lean_dec_ref(x_63);
x_65 = l_Lean_Syntax_getTailPos_x3f(x_21, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_67 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_66);
x_46 = x_61;
x_47 = x_64;
x_48 = x_60;
x_49 = x_59;
x_50 = x_67;
goto block_57;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec_ref(x_65);
x_46 = x_61;
x_47 = x_64;
x_48 = x_60;
x_49 = x_59;
x_50 = x_68;
goto block_57;
}
}
block_74:
{
lean_object* x_70; 
x_70 = l_Lean_Syntax_getPos_x3f(x_21, x_20);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_spec__2___closed__3);
x_72 = l_panic___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__20(x_71);
x_58 = x_72;
goto block_69;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec_ref(x_70);
x_58 = x_73;
goto block_69;
}
}
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_60; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_60 = !lean_is_exclusive(x_5);
if (x_60 == 0)
{
x_20 = x_5;
x_21 = x_60;
goto block_59;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_uget_borrowed(x_2, x_4);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_Shake_run_spec__6___redArg(x_19, x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_40; lean_object* x_41; lean_object* x_49; 
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_25 = lean_box(0);
lean_inc(x_22);
x_26 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_Shake_run_spec__7___redArg(x_19, x_22, x_25);
if (x_24 == 0)
{
lean_object* x_54; 
x_54 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_49 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__5));
x_49 = x_55;
goto block_53;
}
block_39:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
lean_inc(x_29);
x_31 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_29, x_1);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11___closed__0));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_18, x_34);
lean_dec_ref(x_34);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_35);
x_36 = x_20;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_26);
x_36 = x_38;
goto block_37;
}
block_37:
{
x_8 = x_36;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
block_48:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_43 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_44 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__1));
x_45 = lean_string_append(x_43, x_44);
if (x_42 == 0)
{
lean_object* x_46; 
x_46 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_27 = x_45;
x_28 = x_46;
goto block_39;
}
else
{
lean_object* x_47; 
x_47 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__3));
x_27 = x_45;
x_28 = x_47;
goto block_39;
}
}
block_53:
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_40 = x_49;
x_41 = x_51;
goto block_48;
}
else
{
lean_object* x_52; 
x_52 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__4));
x_40 = x_49;
x_41 = x_52;
goto block_48;
}
}
}
else
{
lean_object* x_56; 
if (x_21 == 0)
{
x_56 = x_20;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_18);
lean_ctor_set(x_58, 1, x_19);
x_56 = x_58;
goto block_57;
}
block_57:
{
x_8 = x_56;
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__2);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_134; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_134 = !lean_is_exclusive(x_5);
if (x_134 == 0)
{
x_20 = x_5;
x_21 = x_134;
goto block_133;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_ctor_get(x_18, 2);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
if (x_21 == 0)
{
x_26 = x_20;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
x_26 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_129; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_129 = !lean_is_exclusive(x_18);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_18, 2);
lean_dec(x_130);
x_131 = lean_ctor_get(x_18, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_18, 0);
lean_dec(x_132);
x_31 = x_18;
x_32 = x_129;
goto block_128;
}
else
{
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_array_fget(x_22, x_23);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_array_uget_borrowed(x_2, x_4);
x_37 = lean_nat_add(x_23, x_35);
lean_dec(x_23);
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_37);
x_38 = x_31;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_22);
lean_ctor_set(x_127, 1, x_37);
lean_ctor_set(x_127, 2, x_24);
x_38 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_39; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Shake_0__Lake_Shake_calcNeeds_visitExpr_spec__1___redArg(x_33, x_36);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_task_get_own(x_34);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
lean_del_object(x_20);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = l___private_Lake_CLI_Shake_0__Lake_Shake_decodeHeader(x_49);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_48, 2);
lean_inc_ref(x_53);
lean_dec(x_48);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
lean_dec_ref(x_53);
x_56 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12___closed__3);
x_57 = lean_array_size(x_54);
x_58 = 0;
lean_inc_ref(x_55);
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__9(x_55, x_41, x_54, x_57, x_58, x_56, x_6);
lean_dec(x_54);
lean_dec(x_41);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_111; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 1);
x_111 = !lean_is_exclusive(x_62);
if (x_111 == 0)
{
x_67 = x_62;
x_68 = x_111;
goto block_110;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_62);
x_67 = lean_box(0);
x_68 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = l_Array_qsortOrd___at___00Lake_Shake_run_spec__10(x_42);
x_70 = lean_string_utf8_extract(x_55, x_65, x_50);
lean_dec(x_65);
x_71 = lean_string_append(x_64, x_70);
lean_dec_ref(x_70);
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_71);
x_72 = x_67;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_71);
lean_ctor_set(x_109, 1, x_66);
x_72 = x_109;
goto block_108;
}
block_108:
{
size_t x_73; lean_object* x_74; 
x_73 = lean_array_size(x_69);
x_74 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__11(x_1, x_69, x_73, x_58, x_72, x_63);
lean_dec_ref(x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_98; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
x_98 = !lean_is_exclusive(x_76);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_76, 1);
lean_dec(x_99);
x_79 = x_76;
x_80 = x_98;
goto block_97;
}
else
{
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
x_80 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_string_utf8_byte_size(x_55);
x_82 = lean_string_utf8_extract(x_55, x_50, x_81);
lean_dec(x_50);
lean_dec_ref(x_55);
x_83 = lean_string_append(x_78, x_82);
lean_dec_ref(x_82);
x_84 = l_IO_FS_writeFile(x_47, x_83);
lean_dec_ref(x_83);
lean_dec(x_47);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_84);
x_85 = lean_nat_add(x_19, x_35);
lean_dec(x_19);
if (x_80 == 0)
{
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_38);
x_86 = x_79;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_8 = x_86;
x_9 = x_77;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_del_object(x_79);
lean_dec(x_77);
lean_dec_ref(x_38);
lean_dec(x_19);
x_89 = lean_ctor_get(x_84, 0);
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
x_90 = x_84;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_dec_ref(x_55);
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_38);
lean_dec(x_19);
x_100 = lean_ctor_get(x_74, 0);
x_107 = !lean_is_exclusive(x_74);
if (x_107 == 0)
{
x_101 = x_74;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_74);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec_ref(x_55);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_42);
lean_dec_ref(x_38);
lean_dec(x_19);
x_112 = lean_ctor_get(x_59, 0);
x_119 = !lean_is_exclusive(x_59);
if (x_119 == 0)
{
x_113 = x_59;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_59);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_38);
x_120 = x_20;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_38);
lean_ctor_set(x_122, 1, x_19);
x_120 = x_122;
goto block_121;
}
block_121:
{
x_8 = x_120;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_39);
lean_dec(x_34);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_38);
x_123 = x_20;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_19);
x_123 = x_125;
goto block_124;
}
block_124:
{
x_8 = x_123;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
}
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_93; 
x_29 = lean_ctor_get(x_28, 0);
x_93 = !lean_is_exclusive(x_28);
if (x_93 == 0)
{
x_30 = x_28;
x_31 = x_93;
goto block_92;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_90; 
x_32 = lean_ctor_get(x_29, 1);
x_90 = !lean_is_exclusive(x_29);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_29, 0);
lean_dec(x_91);
x_33 = x_29;
x_34 = x_90;
goto block_89;
}
else
{
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = x_90;
goto block_89;
}
block_89:
{
uint32_t x_35; 
if (x_8 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec_ref(x_24);
x_44 = lean_ctor_get(x_32, 4);
x_45 = lean_ctor_get(x_44, 0);
x_46 = lean_nat_dec_eq(x_45, x_2);
lean_dec(x_2);
if (x_46 == 0)
{
uint32_t x_47; 
x_47 = 1;
x_35 = x_47;
goto block_43;
}
else
{
x_35 = x_9;
goto block_43;
}
}
else
{
lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; 
lean_del_object(x_33);
lean_del_object(x_30);
x_48 = lean_ctor_get(x_10, 7);
lean_inc(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_2);
x_50 = lean_array_size(x_48);
x_51 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Shake_run_spec__12(x_8, x_48, x_50, x_11, x_49, x_32);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_nat_dec_lt(x_2, x_55);
lean_dec(x_2);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
x_57 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__0));
x_58 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_15 = x_54;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_54);
x_59 = lean_ctor_get(x_58, 0);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
x_60 = x_58;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__1));
x_68 = l_Nat_reprFast(x_55);
x_69 = lean_string_append(x_67, x_68);
lean_dec_ref(x_68);
x_70 = ((lean_object*)(l_Lake_Shake_run___lam__0___closed__2));
x_71 = lean_string_append(x_69, x_70);
x_72 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_15 = x_54;
x_16 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_54);
x_73 = lean_ctor_get(x_72, 0);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
x_74 = x_72;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_2);
x_81 = lean_ctor_get(x_51, 0);
x_88 = !lean_is_exclusive(x_51);
if (x_88 == 0)
{
x_82 = x_51;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_51);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
block_43:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box_uint32(x_35);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_36);
x_37 = x_33;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_32);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_37);
x_38 = x_30;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec_ref(x_24);
lean_dec(x_2);
x_94 = lean_ctor_get(x_28, 0);
x_101 = !lean_is_exclusive(x_28);
if (x_101 == 0)
{
x_95 = x_28;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_28);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
x_14 = x_4;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
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
x_9 = lean_array_uget_borrowed(x_3, x_4);
x_10 = lean_array_get_borrowed(x_8, x_7, x_2);
x_11 = l_Lean_Name_isPrefixOf(x_9, x_10);
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
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Shake_0__Lake_Shake_visitModule_spec__17_spec__23___closed__2));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__0);
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
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__2));
x_2 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__3);
x_2 = l_System_instInhabitedFilePath_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__4);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__5);
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
x_25 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6, &l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg___closed__6);
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
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
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
static lean_object* _init_l_Lake_Shake_run___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2, &l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2_once, _init_l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv___closed__2);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Shake_run___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lake_Shake_run___closed__0, &l_Lake_Shake_run___closed__0_once, _init_l_Lake_Shake_run___closed__0);
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Shake_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_Lean_instInhabitedImportState_default;
x_26 = lean_st_mk_ref(x_25);
x_27 = lean_array_size(x_24);
x_28 = 0;
lean_inc_ref(x_24);
x_29 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__0(x_27, x_28, x_24);
x_30 = lean_box(1);
lean_inc_ref(x_24);
x_31 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Shake_run_spec__1(x_27, x_28, x_24);
x_32 = 2;
x_33 = 1;
lean_inc(x_26);
x_34 = l_Lean_importModulesCore(x_31, x_32, x_30, x_33, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; uint8_t x_39; lean_object* x_40; 
lean_dec_ref(x_34);
x_35 = lean_st_ref_get(x_26);
lean_dec(x_26);
x_36 = l_Lean_ImportState_markAllExported(x_35);
x_37 = l_Lean_Options_empty;
x_38 = 0;
x_39 = 0;
x_40 = l_Lean_finalizeImport(x_36, x_31, x_37, x_38, x_33, x_39, x_32, x_33);
lean_dec_ref(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_112; 
x_41 = lean_ctor_get(x_40, 0);
x_112 = !lean_is_exclusive(x_40);
if (x_112 == 0)
{
x_42 = x_40;
x_43 = x_112;
goto block_111;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_103; uint8_t x_104; 
x_44 = l_Lean_Environment_header(x_41);
x_45 = lean_ctor_get(x_44, 6);
lean_inc_ref(x_45);
lean_dec_ref(x_44);
x_46 = lean_obj_once(&l_Lake_Shake_run___closed__1, &l_Lake_Shake_run___closed__1_once, _init_l_Lake_Shake_run___closed__1);
x_47 = lean_unsigned_to_nat(0u);
x_103 = lean_array_get_size(x_45);
x_104 = lean_nat_dec_lt(x_47, x_103);
if (x_104 == 0)
{
lean_dec_ref(x_45);
lean_del_object(x_42);
x_48 = x_39;
goto block_102;
}
else
{
if (x_104 == 0)
{
lean_dec_ref(x_45);
lean_del_object(x_42);
x_48 = x_39;
goto block_102;
}
else
{
size_t x_105; uint8_t x_106; 
x_105 = lean_usize_of_nat(x_103);
x_106 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Shake_run_spec__13(x_45, x_28, x_105);
lean_dec_ref(x_45);
if (x_106 == 0)
{
lean_del_object(x_42);
x_48 = x_106;
goto block_102;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_41);
lean_dec_ref(x_29);
lean_dec(x_2);
lean_dec_ref(x_1);
x_107 = ((lean_object*)(l_Lake_Shake_run___closed__4));
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_107);
x_108 = x_42;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_107);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
}
block_102:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_100; 
x_49 = l_Lean_indirectModUseExt;
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_49, 2);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_50, 2);
x_53 = lean_box(0);
lean_inc(x_41);
x_54 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_46, x_50, x_41, x_52, x_53);
x_55 = lean_ctor_get(x_54, 0);
x_100 = !lean_is_exclusive(x_54);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_54, 1);
lean_dec(x_101);
x_56 = x_54;
x_57 = x_100;
goto block_99;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_58; lean_object* x_59; 
lean_inc(x_41);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_37);
lean_inc_ref(x_55);
x_59 = lean_apply_3(x_51, x_55, x_58, lean_box(0));
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_60);
x_61 = x_56;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_55);
lean_ctor_set(x_90, 1, x_60);
x_61 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_box(0);
x_63 = l_Lean_EnvExtension_setState___redArg(x_50, x_41, x_61, x_62);
x_64 = l___private_Lake_CLI_Shake_0__Lake_Shake_initStateFromEnv(x_63);
x_65 = l___private_Lake_CLI_Shake_0__Lake_Shake_State_mods(x_64);
x_66 = lean_array_get_size(x_65);
lean_dec_ref(x_65);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_inc_ref(x_67);
lean_inc_ref(x_64);
x_68 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__3___redArg(x_64, x_66, x_47, x_67);
lean_inc(x_2);
lean_inc_ref(x_64);
x_69 = l_Array_mapFinIdxM_map___at___00Lake_Shake_run_spec__4___redArg(x_64, x_2, x_29, x_48, x_66, x_47, x_67, x_64);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
if (x_23 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = l_Lake_Shake_run___lam__0(x_68, x_47, x_71, x_66, x_29, x_2, x_1, x_23, x_38, x_64, x_28, x_73, x_72);
lean_dec_ref(x_64);
lean_dec_ref(x_1);
lean_dec_ref(x_29);
x_4 = x_74;
goto block_22;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = ((lean_object*)(l_Lake_Shake_run___closed__2));
x_78 = l_IO_println___at___00__private_Lake_CLI_Shake_0__Lake_Shake_parseHeaderFromString_spec__1(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l_Lake_Shake_run___lam__0(x_68, x_47, x_75, x_66, x_29, x_2, x_1, x_23, x_38, x_64, x_28, x_79, x_76);
lean_dec_ref(x_64);
lean_dec_ref(x_1);
lean_dec_ref(x_29);
x_4 = x_80;
goto block_22;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_68);
lean_dec_ref(x_64);
lean_dec_ref(x_29);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_78, 0);
x_88 = !lean_is_exclusive(x_78);
if (x_88 == 0)
{
x_82 = x_78;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_del_object(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_50);
lean_dec(x_41);
lean_dec_ref(x_29);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_59, 0);
x_98 = !lean_is_exclusive(x_59);
if (x_98 == 0)
{
x_92 = x_59;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_59);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec_ref(x_29);
lean_dec(x_2);
lean_dec_ref(x_1);
x_113 = lean_ctor_get(x_40, 0);
x_120 = !lean_is_exclusive(x_40);
if (x_120 == 0)
{
x_114 = x_40;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_40);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_34, 0);
x_128 = !lean_is_exclusive(x_34);
if (x_128 == 0)
{
x_122 = x_34;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_34);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
block_22:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
x_6 = x_4;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_4, 0);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
x_15 = x_4;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
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
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Shake(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_Path(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset_default);
l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instInhabitedBitset);
l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_Bitset_instEmptyCollectionBitset);
l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake = _init_l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake();
lean_mark_persistent(l___private_Lake_CLI_Shake_0__Lake_Shake_instOrdImport__lake);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Shake(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lean_Util_Path(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Shake(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Shake(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Shake(builtin);
}
#ifdef __cplusplus
}
#endif
