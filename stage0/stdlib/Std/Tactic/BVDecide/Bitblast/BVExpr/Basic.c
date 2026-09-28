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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_reverse(lean_object*, lean_object*);
lean_object* l_BitVec_clz(lean_object*, lean_object*);
lean_object* l_BitVec_cpop(lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_BitVec_hash(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value;
static const lean_string_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16;
static lean_once_cell_t l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19 = (const lean_object*)&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instToStringBVBit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instToStringBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit = (const lean_object*)&l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVUnOp_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString = (const lean_object*)&l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value;
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
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg();
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object* v_x_1_){
_start:
{
lean_object* v_var_2_; lean_object* v_w_3_; lean_object* v_idx_4_; uint64_t v___x_5_; uint64_t v___x_6_; uint64_t v___x_7_; uint64_t v___x_8_; uint64_t v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; 
v_var_2_ = lean_ctor_get(v_x_1_, 0);
v_w_3_ = lean_ctor_get(v_x_1_, 1);
v_idx_4_ = lean_ctor_get(v_x_1_, 2);
v___x_5_ = 0ULL;
v___x_6_ = lean_uint64_of_nat(v_var_2_);
v___x_7_ = lean_uint64_mix_hash(v___x_5_, v___x_6_);
v___x_8_ = lean_uint64_of_nat(v_w_3_);
v___x_9_ = lean_uint64_mix_hash(v___x_7_, v___x_8_);
v___x_10_ = lean_uint64_of_nat(v_idx_4_);
v___x_11_ = lean_uint64_mix_hash(v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object* v_x_12_){
_start:
{
uint64_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_x_12_);
lean_dec_ref(v_x_12_);
v_r_14_ = lean_box_uint64(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_var_19_; lean_object* v_w_20_; lean_object* v_idx_21_; lean_object* v_var_22_; lean_object* v_w_23_; lean_object* v_idx_24_; uint8_t v___x_25_; 
v_var_19_ = lean_ctor_get(v_x_17_, 0);
v_w_20_ = lean_ctor_get(v_x_17_, 1);
v_idx_21_ = lean_ctor_get(v_x_17_, 2);
v_var_22_ = lean_ctor_get(v_x_18_, 0);
v_w_23_ = lean_ctor_get(v_x_18_, 1);
v_idx_24_ = lean_ctor_get(v_x_18_, 2);
v___x_25_ = lean_nat_dec_eq(v_var_19_, v_var_22_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = lean_nat_dec_eq(v_w_20_, v_w_23_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_idx_21_, v_idx_24_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_28_, v_x_29_);
lean_dec_ref(v_x_29_);
lean_dec_ref(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_32_, v_x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit(v_x_35_, v_x_36_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_x_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_instReprBVBit_repr_spec__0(lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_nat_to_int(v_a_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(7u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(5u);
v___x_63_ = lean_nat_to_int(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0));
v___x_69_ = lean_string_length(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(lean_object* v_x_76_){
_start:
{
lean_object* v_var_77_; lean_object* v_w_78_; lean_object* v_idx_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_var_77_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_var_77_);
v_w_78_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_w_78_);
v_idx_79_ = lean_ctor_get(v_x_76_, 2);
lean_inc(v_idx_79_);
lean_dec_ref(v_x_76_);
v___x_80_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5));
v___x_81_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6));
v___x_82_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7);
v___x_83_ = l_Nat_reprFast(v_var_77_);
v___x_84_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_81_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_box(1);
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11));
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_80_);
v___x_96_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12);
v___x_97_ = l_Nat_reprFast(v_w_78_);
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_86_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_95_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_89_);
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_91_);
v___x_104_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14));
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_80_);
v___x_107_ = l_Nat_reprFast(v_idx_79_);
v___x_108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_82_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_86_);
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_106_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17);
v___x_113_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18));
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_111_);
v___x_115_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19));
v___x_116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_112_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_86_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr(lean_object* v_x_119_, lean_object* v_prec_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(v_x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed(lean_object* v_x_122_, lean_object* v_prec_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Tactic_BVDecide_instReprBVBit_repr(v_x_122_, v_prec_123_);
lean_dec(v_prec_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object* v_b_130_){
_start:
{
lean_object* v_var_131_; lean_object* v_idx_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_var_131_ = lean_ctor_get(v_b_130_, 0);
lean_inc(v_var_131_);
v_idx_132_ = lean_ctor_get(v_b_130_, 2);
lean_inc(v_idx_132_);
lean_dec_ref(v_b_130_);
v___x_133_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0));
v___x_134_ = l_Nat_reprFast(v_var_131_);
v___x_135_ = lean_string_append(v___x_133_, v___x_134_);
lean_dec_ref(v___x_134_);
v___x_136_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_137_ = lean_string_append(v___x_135_, v___x_136_);
v___x_138_ = l_Nat_reprFast(v_idx_132_);
v___x_139_ = lean_string_append(v___x_137_, v___x_138_);
lean_dec_ref(v___x_138_);
v___x_140_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(uint8_t v_x_148_){
_start:
{
switch(v_x_148_)
{
case 0:
{
lean_object* v___x_149_; 
v___x_149_ = lean_unsigned_to_nat(0u);
return v___x_149_;
}
case 1:
{
lean_object* v___x_150_; 
v___x_150_ = lean_unsigned_to_nat(1u);
return v___x_150_;
}
case 2:
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(2u);
return v___x_151_;
}
case 3:
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(3u);
return v___x_152_;
}
case 4:
{
lean_object* v___x_153_; 
v___x_153_ = lean_unsigned_to_nat(4u);
return v___x_153_;
}
case 5:
{
lean_object* v___x_154_; 
v___x_154_ = lean_unsigned_to_nat(5u);
return v___x_154_;
}
default: 
{
lean_object* v___x_155_; 
v___x_155_ = lean_unsigned_to_nat(6u);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(lean_object* v_x_156_){
_start:
{
uint8_t v_x_boxed_157_; lean_object* v_res_158_; 
v_x_boxed_157_ = lean_unbox(v_x_156_);
v_res_158_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_boxed_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* v_k_159_){
_start:
{
lean_inc(v_k_159_);
return v_k_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* v_k_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_160_);
lean_dec(v_k_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* v_motive_162_, lean_object* v_ctorIdx_163_, uint8_t v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_inc(v_k_166_);
return v_k_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object* v_motive_167_, lean_object* v_ctorIdx_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_k_171_){
_start:
{
uint8_t v_t_boxed_172_; lean_object* v_res_173_; 
v_t_boxed_172_ = lean_unbox(v_t_169_);
v_res_173_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(v_motive_167_, v_ctorIdx_168_, v_t_boxed_172_, v_h_170_, v_k_171_);
lean_dec(v_k_171_);
lean_dec(v_ctorIdx_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object* v_and_174_){
_start:
{
lean_inc(v_and_174_);
return v_and_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object* v_and_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(v_and_175_);
lean_dec(v_and_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* v_motive_177_, uint8_t v_t_178_, lean_object* v_h_179_, lean_object* v_and_180_){
_start:
{
lean_inc(v_and_180_);
return v_and_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* v_motive_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_and_184_){
_start:
{
uint8_t v_t_boxed_185_; lean_object* v_res_186_; 
v_t_boxed_185_ = lean_unbox(v_t_182_);
v_res_186_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(v_motive_181_, v_t_boxed_185_, v_h_183_, v_and_184_);
lean_dec(v_and_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* v_or_187_){
_start:
{
lean_inc(v_or_187_);
return v_or_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* v_or_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_188_);
lean_dec(v_or_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* v_motive_190_, uint8_t v_t_191_, lean_object* v_h_192_, lean_object* v_or_193_){
_start:
{
lean_inc(v_or_193_);
return v_or_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* v_motive_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_or_197_){
_start:
{
uint8_t v_t_boxed_198_; lean_object* v_res_199_; 
v_t_boxed_198_ = lean_unbox(v_t_195_);
v_res_199_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(v_motive_194_, v_t_boxed_198_, v_h_196_, v_or_197_);
lean_dec(v_or_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* v_xor_200_){
_start:
{
lean_inc(v_xor_200_);
return v_xor_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* v_xor_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_201_);
lean_dec(v_xor_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* v_motive_203_, uint8_t v_t_204_, lean_object* v_h_205_, lean_object* v_xor_206_){
_start:
{
lean_inc(v_xor_206_);
return v_xor_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* v_motive_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_xor_210_){
_start:
{
uint8_t v_t_boxed_211_; lean_object* v_res_212_; 
v_t_boxed_211_ = lean_unbox(v_t_208_);
v_res_212_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(v_motive_207_, v_t_boxed_211_, v_h_209_, v_xor_210_);
lean_dec(v_xor_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* v_add_213_){
_start:
{
lean_inc(v_add_213_);
return v_add_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* v_add_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_214_);
lean_dec(v_add_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* v_motive_216_, uint8_t v_t_217_, lean_object* v_h_218_, lean_object* v_add_219_){
_start:
{
lean_inc(v_add_219_);
return v_add_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object* v_motive_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_add_223_){
_start:
{
uint8_t v_t_boxed_224_; lean_object* v_res_225_; 
v_t_boxed_224_ = lean_unbox(v_t_221_);
v_res_225_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(v_motive_220_, v_t_boxed_224_, v_h_222_, v_add_223_);
lean_dec(v_add_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object* v_mul_226_){
_start:
{
lean_inc(v_mul_226_);
return v_mul_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object* v_mul_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(v_mul_227_);
lean_dec(v_mul_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* v_motive_229_, uint8_t v_t_230_, lean_object* v_h_231_, lean_object* v_mul_232_){
_start:
{
lean_inc(v_mul_232_);
return v_mul_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_mul_236_){
_start:
{
uint8_t v_t_boxed_237_; lean_object* v_res_238_; 
v_t_boxed_237_ = lean_unbox(v_t_234_);
v_res_238_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(v_motive_233_, v_t_boxed_237_, v_h_235_, v_mul_236_);
lean_dec(v_mul_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* v_udiv_239_){
_start:
{
lean_inc(v_udiv_239_);
return v_udiv_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* v_udiv_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_240_);
lean_dec(v_udiv_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* v_motive_242_, uint8_t v_t_243_, lean_object* v_h_244_, lean_object* v_udiv_245_){
_start:
{
lean_inc(v_udiv_245_);
return v_udiv_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* v_motive_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_udiv_249_){
_start:
{
uint8_t v_t_boxed_250_; lean_object* v_res_251_; 
v_t_boxed_250_ = lean_unbox(v_t_247_);
v_res_251_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(v_motive_246_, v_t_boxed_250_, v_h_248_, v_udiv_249_);
lean_dec(v_udiv_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* v_umod_252_){
_start:
{
lean_inc(v_umod_252_);
return v_umod_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* v_umod_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_253_);
lean_dec(v_umod_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* v_motive_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_umod_258_){
_start:
{
lean_inc(v_umod_258_);
return v_umod_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_umod_262_){
_start:
{
uint8_t v_t_boxed_263_; lean_object* v_res_264_; 
v_t_boxed_263_ = lean_unbox(v_t_260_);
v_res_264_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(v_motive_259_, v_t_boxed_263_, v_h_261_, v_umod_262_);
lean_dec(v_umod_262_);
return v_res_264_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t v_x_265_){
_start:
{
switch(v_x_265_)
{
case 0:
{
uint64_t v___x_266_; 
v___x_266_ = 0ULL;
return v___x_266_;
}
case 1:
{
uint64_t v___x_267_; 
v___x_267_ = 1ULL;
return v___x_267_;
}
case 2:
{
uint64_t v___x_268_; 
v___x_268_ = 2ULL;
return v___x_268_;
}
case 3:
{
uint64_t v___x_269_; 
v___x_269_ = 3ULL;
return v___x_269_;
}
case 4:
{
uint64_t v___x_270_; 
v___x_270_ = 4ULL;
return v___x_270_;
}
case 5:
{
uint64_t v___x_271_; 
v___x_271_ = 5ULL;
return v___x_271_;
}
default: 
{
uint64_t v___x_272_; 
v___x_272_ = 6ULL;
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* v_x_273_){
_start:
{
uint8_t v_x_88__boxed_274_; uint64_t v_res_275_; lean_object* v_r_276_; 
v_x_88__boxed_274_ = lean_unbox(v_x_273_);
v_res_275_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_274_);
v_r_276_ = lean_box_uint64(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* v_n_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(2u);
v___x_281_ = lean_nat_dec_le(v_n_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = lean_nat_dec_le(v_n_279_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(5u);
v___x_285_ = lean_nat_dec_le(v_n_279_, v___x_284_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 6;
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = 5;
return v___x_287_;
}
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(3u);
v___x_289_ = lean_nat_dec_le(v_n_279_, v___x_288_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 4;
return v___x_290_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = 3;
return v___x_291_;
}
}
}
else
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_nat_dec_le(v_n_279_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_dec_le(v_n_279_, v___x_294_);
if (v___x_295_ == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 2;
return v___x_296_;
}
else
{
uint8_t v___x_297_; 
v___x_297_ = 1;
return v___x_297_;
}
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* v_n_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_299_);
lean_dec(v_n_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t v_x_302_, uint8_t v_y_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_302_);
v___x_305_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_y_303_);
v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v___x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* v_x_307_, lean_object* v_y_308_){
_start:
{
uint8_t v_x_20__boxed_309_; uint8_t v_y_21__boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_x_20__boxed_309_ = lean_unbox(v_x_307_);
v_y_21__boxed_310_ = lean_unbox(v_y_308_);
v_res_311_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_20__boxed_309_, v_y_21__boxed_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t v_x_320_){
_start:
{
switch(v_x_320_)
{
case 0:
{
lean_object* v___x_321_; 
v___x_321_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return v___x_321_;
}
case 1:
{
lean_object* v___x_322_; 
v___x_322_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return v___x_322_;
}
case 2:
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return v___x_323_;
}
case 3:
{
lean_object* v___x_324_; 
v___x_324_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return v___x_324_;
}
case 4:
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return v___x_325_;
}
case 5:
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return v___x_326_;
}
default: 
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* v_x_328_){
_start:
{
uint8_t v_x_67__boxed_329_; lean_object* v_res_330_; 
v_x_67__boxed_329_ = lean_unbox(v_x_328_);
v_res_330_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* v_w_333_, uint8_t v_x_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
switch(v_x_334_)
{
case 0:
{
lean_object* v___x_337_; 
v___x_337_ = lean_nat_land(v_a_335_, v_a_336_);
return v___x_337_;
}
case 1:
{
lean_object* v___x_338_; 
v___x_338_ = lean_nat_lor(v_a_335_, v_a_336_);
return v___x_338_;
}
case 2:
{
lean_object* v___x_339_; 
v___x_339_ = lean_nat_lxor(v_a_335_, v_a_336_);
return v___x_339_;
}
case 3:
{
lean_object* v___x_340_; 
v___x_340_ = l_BitVec_add(v_w_333_, v_a_335_, v_a_336_);
return v___x_340_;
}
case 4:
{
lean_object* v___x_341_; 
v___x_341_ = l_BitVec_mul(v_w_333_, v_a_335_, v_a_336_);
return v___x_341_;
}
case 5:
{
lean_object* v___x_342_; 
v___x_342_ = lean_nat_div(v_a_335_, v_a_336_);
return v___x_342_;
}
default: 
{
lean_object* v___x_343_; 
v___x_343_ = lean_nat_mod(v_a_335_, v_a_336_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* v_w_344_, lean_object* v_x_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_x_340__boxed_348_; lean_object* v_res_349_; 
v_x_340__boxed_348_ = lean_unbox(v_x_345_);
v_res_349_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_344_, v_x_340__boxed_348_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec(v_a_346_);
lean_dec(v_w_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(lean_object* v_x_350_){
_start:
{
switch(lean_obj_tag(v_x_350_))
{
case 0:
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(0u);
return v___x_351_;
}
case 1:
{
lean_object* v___x_352_; 
v___x_352_ = lean_unsigned_to_nat(1u);
return v___x_352_;
}
case 2:
{
lean_object* v___x_353_; 
v___x_353_ = lean_unsigned_to_nat(2u);
return v___x_353_;
}
case 3:
{
lean_object* v___x_354_; 
v___x_354_ = lean_unsigned_to_nat(3u);
return v___x_354_;
}
case 4:
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(4u);
return v___x_355_;
}
case 5:
{
lean_object* v___x_356_; 
v___x_356_ = lean_unsigned_to_nat(5u);
return v___x_356_;
}
default: 
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(6u);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(v_x_358_);
lean_dec(v_x_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* v_t_360_, lean_object* v_k_361_){
_start:
{
switch(lean_obj_tag(v_t_360_))
{
case 1:
{
lean_object* v_n_362_; lean_object* v___x_363_; 
v_n_362_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_n_362_);
lean_dec_ref_known(v_t_360_, 1);
v___x_363_ = lean_apply_1(v_k_361_, v_n_362_);
return v___x_363_;
}
case 2:
{
lean_object* v_n_364_; lean_object* v___x_365_; 
v_n_364_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_n_364_);
lean_dec_ref_known(v_t_360_, 1);
v___x_365_ = lean_apply_1(v_k_361_, v_n_364_);
return v___x_365_;
}
case 3:
{
lean_object* v_n_366_; lean_object* v___x_367_; 
v_n_366_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_n_366_);
lean_dec_ref_known(v_t_360_, 1);
v___x_367_ = lean_apply_1(v_k_361_, v_n_366_);
return v___x_367_;
}
default: 
{
lean_dec(v_t_360_);
return v_k_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* v_motive_368_, lean_object* v_ctorIdx_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_k_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_370_, v_k_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* v_motive_374_, lean_object* v_ctorIdx_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_k_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(v_motive_374_, v_ctorIdx_375_, v_t_376_, v_h_377_, v_k_378_);
lean_dec(v_ctorIdx_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* v_t_380_, lean_object* v_not_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_380_, v_not_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_not_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_384_, v_not_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* v_t_388_, lean_object* v_rotateLeft_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_388_, v_rotateLeft_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_rotateLeft_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_392_, v_rotateLeft_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* v_t_396_, lean_object* v_rotateRight_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_396_, v_rotateRight_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_rotateRight_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_400_, v_rotateRight_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* v_t_404_, lean_object* v_arithShiftRightConst_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_404_, v_arithShiftRightConst_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_arithShiftRightConst_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_408_, v_arithShiftRightConst_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* v_t_412_, lean_object* v_reverse_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_412_, v_reverse_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_reverse_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_416_, v_reverse_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* v_t_420_, lean_object* v_clz_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_420_, v_clz_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_clz_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_424_, v_clz_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object* v_t_428_, lean_object* v_cpop_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_428_, v_cpop_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_cpop_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_432_, v_cpop_434_);
return v___x_435_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* v_x_436_){
_start:
{
switch(lean_obj_tag(v_x_436_))
{
case 0:
{
uint64_t v___x_437_; 
v___x_437_ = 0ULL;
return v___x_437_;
}
case 1:
{
lean_object* v_n_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; 
v_n_438_ = lean_ctor_get(v_x_436_, 0);
v___x_439_ = 1ULL;
v___x_440_ = lean_uint64_of_nat(v_n_438_);
v___x_441_ = lean_uint64_mix_hash(v___x_439_, v___x_440_);
return v___x_441_;
}
case 2:
{
lean_object* v_n_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; 
v_n_442_ = lean_ctor_get(v_x_436_, 0);
v___x_443_ = 2ULL;
v___x_444_ = lean_uint64_of_nat(v_n_442_);
v___x_445_ = lean_uint64_mix_hash(v___x_443_, v___x_444_);
return v___x_445_;
}
case 3:
{
lean_object* v_n_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; 
v_n_446_ = lean_ctor_get(v_x_436_, 0);
v___x_447_ = 3ULL;
v___x_448_ = lean_uint64_of_nat(v_n_446_);
v___x_449_ = lean_uint64_mix_hash(v___x_447_, v___x_448_);
return v___x_449_;
}
case 4:
{
uint64_t v___x_450_; 
v___x_450_ = 4ULL;
return v___x_450_;
}
case 5:
{
uint64_t v___x_451_; 
v___x_451_ = 5ULL;
return v___x_451_;
}
default: 
{
uint64_t v___x_452_; 
v___x_452_ = 6ULL;
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object* v_x_453_){
_start:
{
uint64_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_453_);
lean_dec(v_x_453_);
v_r_455_ = lean_box_uint64(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
switch(lean_obj_tag(v_x_458_))
{
case 0:
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
case 1:
{
if (lean_obj_tag(v_x_459_) == 1)
{
lean_object* v_n_462_; lean_object* v_n_463_; uint8_t v___x_464_; 
v_n_462_ = lean_ctor_get(v_x_458_, 0);
v_n_463_ = lean_ctor_get(v_x_459_, 0);
v___x_464_ = lean_nat_dec_eq(v_n_462_, v_n_463_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
}
case 2:
{
if (lean_obj_tag(v_x_459_) == 2)
{
lean_object* v_n_466_; lean_object* v_n_467_; uint8_t v___x_468_; 
v_n_466_ = lean_ctor_get(v_x_458_, 0);
v_n_467_ = lean_ctor_get(v_x_459_, 0);
v___x_468_ = lean_nat_dec_eq(v_n_466_, v_n_467_);
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
case 3:
{
if (lean_obj_tag(v_x_459_) == 3)
{
lean_object* v_n_470_; lean_object* v_n_471_; uint8_t v___x_472_; 
v_n_470_ = lean_ctor_get(v_x_458_, 0);
v_n_471_ = lean_ctor_get(v_x_459_, 0);
v___x_472_ = lean_nat_dec_eq(v_n_470_, v_n_471_);
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
}
case 4:
{
if (lean_obj_tag(v_x_459_) == 4)
{
uint8_t v___x_474_; 
v___x_474_ = 1;
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
}
case 5:
{
if (lean_obj_tag(v_x_459_) == 5)
{
uint8_t v___x_476_; 
v___x_476_ = 1;
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = 0;
return v___x_477_;
}
}
default: 
{
if (lean_obj_tag(v_x_459_) == 6)
{
uint8_t v___x_478_; 
v___x_478_ = 1;
return v___x_478_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = 0;
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_x_480_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec(v_x_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_498_){
_start:
{
switch(lean_obj_tag(v_x_498_))
{
case 0:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_499_;
}
case 1:
{
lean_object* v_n_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_n_500_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_n_500_);
lean_dec_ref_known(v_x_498_, 1);
v___x_501_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_502_ = l_Nat_reprFast(v_n_500_);
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
lean_dec_ref(v___x_502_);
return v___x_503_;
}
case 2:
{
lean_object* v_n_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_n_504_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_n_504_);
lean_dec_ref_known(v_x_498_, 1);
v___x_505_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_506_ = l_Nat_reprFast(v_n_504_);
v___x_507_ = lean_string_append(v___x_505_, v___x_506_);
lean_dec_ref(v___x_506_);
return v___x_507_;
}
case 3:
{
lean_object* v_n_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_n_508_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_n_508_);
lean_dec_ref_known(v_x_498_, 1);
v___x_509_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_510_ = l_Nat_reprFast(v_n_508_);
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
return v___x_511_;
}
case 4:
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_512_;
}
case 5:
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_513_;
}
default: 
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_517_, lean_object* v_x_518_, lean_object* v_a_519_){
_start:
{
switch(lean_obj_tag(v_x_518_))
{
case 0:
{
lean_object* v___x_520_; 
v___x_520_ = l_BitVec_not(v_w_517_, v_a_519_);
lean_dec(v_a_519_);
lean_dec(v_w_517_);
return v___x_520_;
}
case 1:
{
lean_object* v_n_521_; lean_object* v___x_522_; 
v_n_521_ = lean_ctor_get(v_x_518_, 0);
v___x_522_ = l_BitVec_rotateLeft(v_w_517_, v_a_519_, v_n_521_);
lean_dec(v_a_519_);
lean_dec(v_w_517_);
return v___x_522_;
}
case 2:
{
lean_object* v_n_523_; lean_object* v___x_524_; 
v_n_523_ = lean_ctor_get(v_x_518_, 0);
v___x_524_ = l_BitVec_rotateRight(v_w_517_, v_a_519_, v_n_523_);
lean_dec(v_a_519_);
lean_dec(v_w_517_);
return v___x_524_;
}
case 3:
{
lean_object* v_n_525_; lean_object* v___x_526_; 
v_n_525_ = lean_ctor_get(v_x_518_, 0);
v___x_526_ = l_BitVec_sshiftRight(v_w_517_, v_a_519_, v_n_525_);
lean_dec(v_w_517_);
return v___x_526_;
}
case 4:
{
lean_object* v___x_527_; 
v___x_527_ = l_BitVec_reverse(v_w_517_, v_a_519_);
lean_dec(v_a_519_);
lean_dec(v_w_517_);
return v___x_527_;
}
case 5:
{
lean_object* v___x_528_; 
v___x_528_ = l_BitVec_clz(v_w_517_, v_a_519_);
lean_dec(v_a_519_);
lean_dec(v_w_517_);
return v___x_528_;
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = l_BitVec_cpop(v_w_517_, v_a_519_);
lean_dec(v_a_519_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_530_, lean_object* v_x_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_530_, v_x_531_, v_a_532_);
lean_dec(v_x_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object* v_x_534_){
_start:
{
switch(lean_obj_tag(v_x_534_))
{
case 0:
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(0u);
return v___x_535_;
}
case 1:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(1u);
return v___x_536_;
}
case 2:
{
lean_object* v___x_537_; 
v___x_537_ = lean_unsigned_to_nat(2u);
return v___x_537_;
}
case 3:
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(3u);
return v___x_538_;
}
case 4:
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(4u);
return v___x_539_;
}
case 5:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(5u);
return v___x_540_;
}
case 6:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(6u);
return v___x_541_;
}
case 7:
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(7u);
return v___x_542_;
}
case 8:
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(8u);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(9u);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_545_);
lean_dec_ref(v_x_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object* v_a_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(v_a_550_, v_x_551_);
lean_dec_ref(v_x_551_);
lean_dec(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
switch(lean_obj_tag(v_t_553_))
{
case 0:
{
lean_object* v_w_555_; lean_object* v_idx_556_; lean_object* v___x_557_; 
v_w_555_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_555_);
v_idx_556_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_idx_556_);
lean_dec_ref_known(v_t_553_, 2);
v___x_557_ = lean_apply_2(v_k_554_, v_w_555_, v_idx_556_);
return v___x_557_;
}
case 1:
{
lean_object* v_w_558_; lean_object* v_val_559_; lean_object* v___x_560_; 
v_w_558_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_558_);
v_val_559_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_val_559_);
lean_dec_ref_known(v_t_553_, 2);
v___x_560_ = lean_apply_2(v_k_554_, v_w_558_, v_val_559_);
return v___x_560_;
}
case 2:
{
lean_object* v_w_561_; lean_object* v_start_562_; lean_object* v_len_563_; lean_object* v_expr_564_; lean_object* v___x_565_; 
v_w_561_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_561_);
v_start_562_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_start_562_);
v_len_563_ = lean_ctor_get(v_t_553_, 2);
lean_inc(v_len_563_);
v_expr_564_ = lean_ctor_get(v_t_553_, 3);
lean_inc_ref(v_expr_564_);
lean_dec_ref_known(v_t_553_, 4);
v___x_565_ = lean_apply_4(v_k_554_, v_w_561_, v_start_562_, v_len_563_, v_expr_564_);
return v___x_565_;
}
case 3:
{
lean_object* v_w_566_; lean_object* v_lhs_567_; uint8_t v_op_568_; lean_object* v_rhs_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_w_566_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_566_);
v_lhs_567_ = lean_ctor_get(v_t_553_, 1);
lean_inc_ref(v_lhs_567_);
v_op_568_ = lean_ctor_get_uint8(v_t_553_, sizeof(void*)*3);
v_rhs_569_ = lean_ctor_get(v_t_553_, 2);
lean_inc_ref(v_rhs_569_);
lean_dec_ref_known(v_t_553_, 3);
v___x_570_ = lean_box(v_op_568_);
v___x_571_ = lean_apply_4(v_k_554_, v_w_566_, v_lhs_567_, v___x_570_, v_rhs_569_);
return v___x_571_;
}
case 4:
{
lean_object* v_w_572_; lean_object* v_op_573_; lean_object* v_operand_574_; lean_object* v___x_575_; 
v_w_572_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_572_);
v_op_573_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_op_573_);
v_operand_574_ = lean_ctor_get(v_t_553_, 2);
lean_inc_ref(v_operand_574_);
lean_dec_ref_known(v_t_553_, 3);
v___x_575_ = lean_apply_3(v_k_554_, v_w_572_, v_op_573_, v_operand_574_);
return v___x_575_;
}
case 5:
{
lean_object* v_l_576_; lean_object* v_r_577_; lean_object* v_w_578_; lean_object* v_lhs_579_; lean_object* v_rhs_580_; lean_object* v___x_581_; 
v_l_576_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_l_576_);
v_r_577_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_r_577_);
v_w_578_ = lean_ctor_get(v_t_553_, 2);
lean_inc(v_w_578_);
v_lhs_579_ = lean_ctor_get(v_t_553_, 3);
lean_inc_ref(v_lhs_579_);
v_rhs_580_ = lean_ctor_get(v_t_553_, 4);
lean_inc_ref(v_rhs_580_);
lean_dec_ref_known(v_t_553_, 5);
v___x_581_ = lean_apply_6(v_k_554_, v_l_576_, v_r_577_, v_w_578_, v_lhs_579_, v_rhs_580_, lean_box(0));
return v___x_581_;
}
case 6:
{
lean_object* v_w_582_; lean_object* v_w_x27_583_; lean_object* v_n_584_; lean_object* v_expr_585_; lean_object* v___x_586_; 
v_w_582_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_w_582_);
v_w_x27_583_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_w_x27_583_);
v_n_584_ = lean_ctor_get(v_t_553_, 2);
lean_inc(v_n_584_);
v_expr_585_ = lean_ctor_get(v_t_553_, 3);
lean_inc_ref(v_expr_585_);
lean_dec_ref_known(v_t_553_, 4);
v___x_586_ = lean_apply_5(v_k_554_, v_w_582_, v_w_x27_583_, v_n_584_, v_expr_585_, lean_box(0));
return v___x_586_;
}
default: 
{
lean_object* v_m_587_; lean_object* v_n_588_; lean_object* v_lhs_589_; lean_object* v_rhs_590_; lean_object* v___x_591_; 
v_m_587_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_m_587_);
v_n_588_ = lean_ctor_get(v_t_553_, 1);
lean_inc(v_n_588_);
v_lhs_589_ = lean_ctor_get(v_t_553_, 2);
lean_inc_ref(v_lhs_589_);
v_rhs_590_ = lean_ctor_get(v_t_553_, 3);
lean_inc_ref(v_rhs_590_);
lean_dec_ref(v_t_553_);
v___x_591_ = lean_apply_4(v_k_554_, v_m_587_, v_n_588_, v_lhs_589_, v_rhs_590_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_592_, lean_object* v_ctorIdx_593_, lean_object* v_a_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_k_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_595_, v_k_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_599_, lean_object* v_ctorIdx_600_, lean_object* v_a_601_, lean_object* v_t_602_, lean_object* v_h_603_, lean_object* v_k_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_599_, v_ctorIdx_600_, v_a_601_, v_t_602_, v_h_603_, v_k_604_);
lean_dec(v_a_601_);
lean_dec(v_ctorIdx_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_606_, lean_object* v_var_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_606_, v_var_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_609_, lean_object* v_a_610_, lean_object* v_t_611_, lean_object* v_h_612_, lean_object* v_var_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_611_, v_var_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_615_, lean_object* v_a_616_, lean_object* v_t_617_, lean_object* v_h_618_, lean_object* v_var_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_615_, v_a_616_, v_t_617_, v_h_618_, v_var_619_);
lean_dec(v_a_616_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_621_, lean_object* v_const_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_621_, v_const_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_624_, lean_object* v_a_625_, lean_object* v_t_626_, lean_object* v_h_627_, lean_object* v_const_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_626_, v_const_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_630_, lean_object* v_a_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_const_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_630_, v_a_631_, v_t_632_, v_h_633_, v_const_634_);
lean_dec(v_a_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_636_, lean_object* v_extract_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_636_, v_extract_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_639_, lean_object* v_a_640_, lean_object* v_t_641_, lean_object* v_h_642_, lean_object* v_extract_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_641_, v_extract_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_645_, lean_object* v_a_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_extract_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_645_, v_a_646_, v_t_647_, v_h_648_, v_extract_649_);
lean_dec(v_a_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_651_, lean_object* v_bin_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_651_, v_bin_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_654_, lean_object* v_a_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_bin_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_656_, v_bin_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_660_, lean_object* v_a_661_, lean_object* v_t_662_, lean_object* v_h_663_, lean_object* v_bin_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_660_, v_a_661_, v_t_662_, v_h_663_, v_bin_664_);
lean_dec(v_a_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_666_, lean_object* v_un_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_666_, v_un_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_669_, lean_object* v_a_670_, lean_object* v_t_671_, lean_object* v_h_672_, lean_object* v_un_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_671_, v_un_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_675_, lean_object* v_a_676_, lean_object* v_t_677_, lean_object* v_h_678_, lean_object* v_un_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_675_, v_a_676_, v_t_677_, v_h_678_, v_un_679_);
lean_dec(v_a_676_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_681_, lean_object* v_append_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_681_, v_append_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_684_, lean_object* v_a_685_, lean_object* v_t_686_, lean_object* v_h_687_, lean_object* v_append_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_686_, v_append_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_690_, lean_object* v_a_691_, lean_object* v_t_692_, lean_object* v_h_693_, lean_object* v_append_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_690_, v_a_691_, v_t_692_, v_h_693_, v_append_694_);
lean_dec(v_a_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_696_, lean_object* v_replicate_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_696_, v_replicate_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_699_, lean_object* v_a_700_, lean_object* v_t_701_, lean_object* v_h_702_, lean_object* v_replicate_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_701_, v_replicate_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_705_, lean_object* v_a_706_, lean_object* v_t_707_, lean_object* v_h_708_, lean_object* v_replicate_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_705_, v_a_706_, v_t_707_, v_h_708_, v_replicate_709_);
lean_dec(v_a_706_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_711_, lean_object* v_shiftLeft_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_711_, v_shiftLeft_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_714_, lean_object* v_a_715_, lean_object* v_t_716_, lean_object* v_h_717_, lean_object* v_shiftLeft_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_716_, v_shiftLeft_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_720_, lean_object* v_a_721_, lean_object* v_t_722_, lean_object* v_h_723_, lean_object* v_shiftLeft_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_720_, v_a_721_, v_t_722_, v_h_723_, v_shiftLeft_724_);
lean_dec(v_a_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_726_, lean_object* v_shiftRight_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_726_, v_shiftRight_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_729_, lean_object* v_a_730_, lean_object* v_t_731_, lean_object* v_h_732_, lean_object* v_shiftRight_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_731_, v_shiftRight_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_735_, lean_object* v_a_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_shiftRight_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_735_, v_a_736_, v_t_737_, v_h_738_, v_shiftRight_739_);
lean_dec(v_a_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_741_, lean_object* v_arithShiftRight_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_741_, v_arithShiftRight_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_744_, lean_object* v_a_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_arithShiftRight_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_746_, v_arithShiftRight_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_750_, lean_object* v_a_751_, lean_object* v_t_752_, lean_object* v_h_753_, lean_object* v_arithShiftRight_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_750_, v_a_751_, v_t_752_, v_h_753_, v_arithShiftRight_754_);
lean_dec(v_a_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_756_, lean_object* v_var_757_, lean_object* v_const_758_, lean_object* v_extract_759_, lean_object* v_bin_760_, lean_object* v_un_761_, lean_object* v_append_762_, lean_object* v_replicate_763_, lean_object* v_shiftLeft_764_, lean_object* v_shiftRight_765_, lean_object* v_arithShiftRight_766_){
_start:
{
switch(lean_obj_tag(v_t_756_))
{
case 0:
{
lean_object* v_w_767_; lean_object* v_idx_768_; lean_object* v___x_769_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
v_w_767_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_767_);
v_idx_768_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_idx_768_);
lean_dec_ref_known(v_t_756_, 2);
v___x_769_ = lean_apply_2(v_var_757_, v_w_767_, v_idx_768_);
return v___x_769_;
}
case 1:
{
lean_object* v_w_770_; lean_object* v_val_771_; lean_object* v___x_772_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_var_757_);
v_w_770_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_770_);
v_val_771_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_val_771_);
lean_dec_ref_known(v_t_756_, 2);
v___x_772_ = lean_apply_2(v_const_758_, v_w_770_, v_val_771_);
return v___x_772_;
}
case 2:
{
lean_object* v_w_773_; lean_object* v_start_774_; lean_object* v_len_775_; lean_object* v_expr_776_; lean_object* v___x_777_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_w_773_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_773_);
v_start_774_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_start_774_);
v_len_775_ = lean_ctor_get(v_t_756_, 2);
lean_inc(v_len_775_);
v_expr_776_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_expr_776_);
lean_dec_ref_known(v_t_756_, 4);
v___x_777_ = lean_apply_4(v_extract_759_, v_w_773_, v_start_774_, v_len_775_, v_expr_776_);
return v___x_777_;
}
case 3:
{
lean_object* v_w_778_; lean_object* v_lhs_779_; uint8_t v_op_780_; lean_object* v_rhs_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_w_778_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_778_);
v_lhs_779_ = lean_ctor_get(v_t_756_, 1);
lean_inc_ref(v_lhs_779_);
v_op_780_ = lean_ctor_get_uint8(v_t_756_, sizeof(void*)*3 + 8);
v_rhs_781_ = lean_ctor_get(v_t_756_, 2);
lean_inc_ref(v_rhs_781_);
lean_dec_ref_known(v_t_756_, 3);
v___x_782_ = lean_box(v_op_780_);
v___x_783_ = lean_apply_4(v_bin_760_, v_w_778_, v_lhs_779_, v___x_782_, v_rhs_781_);
return v___x_783_;
}
case 4:
{
lean_object* v_w_784_; lean_object* v_op_785_; lean_object* v_operand_786_; lean_object* v___x_787_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_w_784_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_784_);
v_op_785_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_op_785_);
v_operand_786_ = lean_ctor_get(v_t_756_, 2);
lean_inc_ref(v_operand_786_);
lean_dec_ref_known(v_t_756_, 3);
v___x_787_ = lean_apply_3(v_un_761_, v_w_784_, v_op_785_, v_operand_786_);
return v___x_787_;
}
case 5:
{
lean_object* v_l_788_; lean_object* v_r_789_; lean_object* v_w_790_; lean_object* v_lhs_791_; lean_object* v_rhs_792_; lean_object* v___x_793_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_l_788_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_l_788_);
v_r_789_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_r_789_);
v_w_790_ = lean_ctor_get(v_t_756_, 2);
lean_inc(v_w_790_);
v_lhs_791_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_lhs_791_);
v_rhs_792_ = lean_ctor_get(v_t_756_, 4);
lean_inc_ref(v_rhs_792_);
lean_dec_ref_known(v_t_756_, 5);
v___x_793_ = lean_apply_6(v_append_762_, v_l_788_, v_r_789_, v_w_790_, v_lhs_791_, v_rhs_792_, lean_box(0));
return v___x_793_;
}
case 6:
{
lean_object* v_w_794_; lean_object* v_w_x27_795_; lean_object* v_n_796_; lean_object* v_expr_797_; lean_object* v___x_798_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_w_794_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_w_794_);
v_w_x27_795_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_w_x27_795_);
v_n_796_ = lean_ctor_get(v_t_756_, 2);
lean_inc(v_n_796_);
v_expr_797_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_expr_797_);
lean_dec_ref_known(v_t_756_, 4);
v___x_798_ = lean_apply_5(v_replicate_763_, v_w_794_, v_w_x27_795_, v_n_796_, v_expr_797_, lean_box(0));
return v___x_798_;
}
case 7:
{
lean_object* v_m_799_; lean_object* v_n_800_; lean_object* v_lhs_801_; lean_object* v_rhs_802_; lean_object* v___x_803_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftRight_765_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_m_799_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_m_799_);
v_n_800_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_n_800_);
v_lhs_801_ = lean_ctor_get(v_t_756_, 2);
lean_inc_ref(v_lhs_801_);
v_rhs_802_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_rhs_802_);
lean_dec_ref_known(v_t_756_, 4);
v___x_803_ = lean_apply_4(v_shiftLeft_764_, v_m_799_, v_n_800_, v_lhs_801_, v_rhs_802_);
return v___x_803_;
}
case 8:
{
lean_object* v_m_804_; lean_object* v_n_805_; lean_object* v_lhs_806_; lean_object* v_rhs_807_; lean_object* v___x_808_; 
lean_dec(v_arithShiftRight_766_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_m_804_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_m_804_);
v_n_805_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_n_805_);
v_lhs_806_ = lean_ctor_get(v_t_756_, 2);
lean_inc_ref(v_lhs_806_);
v_rhs_807_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_rhs_807_);
lean_dec_ref_known(v_t_756_, 4);
v___x_808_ = lean_apply_4(v_shiftRight_765_, v_m_804_, v_n_805_, v_lhs_806_, v_rhs_807_);
return v___x_808_;
}
default: 
{
lean_object* v_m_809_; lean_object* v_n_810_; lean_object* v_lhs_811_; lean_object* v_rhs_812_; lean_object* v___x_813_; 
lean_dec(v_shiftRight_765_);
lean_dec(v_shiftLeft_764_);
lean_dec(v_replicate_763_);
lean_dec(v_append_762_);
lean_dec(v_un_761_);
lean_dec(v_bin_760_);
lean_dec(v_extract_759_);
lean_dec(v_const_758_);
lean_dec(v_var_757_);
v_m_809_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_m_809_);
v_n_810_ = lean_ctor_get(v_t_756_, 1);
lean_inc(v_n_810_);
v_lhs_811_ = lean_ctor_get(v_t_756_, 2);
lean_inc_ref(v_lhs_811_);
v_rhs_812_ = lean_ctor_get(v_t_756_, 3);
lean_inc_ref(v_rhs_812_);
lean_dec_ref_known(v_t_756_, 4);
v___x_813_ = lean_apply_4(v_arithShiftRight_766_, v_m_809_, v_n_810_, v_lhs_811_, v_rhs_812_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_814_, lean_object* v_a_815_, lean_object* v_t_816_, lean_object* v_var_817_, lean_object* v_const_818_, lean_object* v_extract_819_, lean_object* v_bin_820_, lean_object* v_un_821_, lean_object* v_append_822_, lean_object* v_replicate_823_, lean_object* v_shiftLeft_824_, lean_object* v_shiftRight_825_, lean_object* v_arithShiftRight_826_){
_start:
{
switch(lean_obj_tag(v_t_816_))
{
case 0:
{
lean_object* v_w_827_; lean_object* v_idx_828_; lean_object* v___x_829_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
v_w_827_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_827_);
v_idx_828_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_idx_828_);
lean_dec_ref_known(v_t_816_, 2);
v___x_829_ = lean_apply_2(v_var_817_, v_w_827_, v_idx_828_);
return v___x_829_;
}
case 1:
{
lean_object* v_w_830_; lean_object* v_val_831_; lean_object* v___x_832_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_var_817_);
v_w_830_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_830_);
v_val_831_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_val_831_);
lean_dec_ref_known(v_t_816_, 2);
v___x_832_ = lean_apply_2(v_const_818_, v_w_830_, v_val_831_);
return v___x_832_;
}
case 2:
{
lean_object* v_w_833_; lean_object* v_start_834_; lean_object* v_len_835_; lean_object* v_expr_836_; lean_object* v___x_837_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_w_833_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_833_);
v_start_834_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_start_834_);
v_len_835_ = lean_ctor_get(v_t_816_, 2);
lean_inc(v_len_835_);
v_expr_836_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_expr_836_);
lean_dec_ref_known(v_t_816_, 4);
v___x_837_ = lean_apply_4(v_extract_819_, v_w_833_, v_start_834_, v_len_835_, v_expr_836_);
return v___x_837_;
}
case 3:
{
lean_object* v_w_838_; lean_object* v_lhs_839_; uint8_t v_op_840_; lean_object* v_rhs_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_w_838_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_838_);
v_lhs_839_ = lean_ctor_get(v_t_816_, 1);
lean_inc_ref(v_lhs_839_);
v_op_840_ = lean_ctor_get_uint8(v_t_816_, sizeof(void*)*3 + 8);
v_rhs_841_ = lean_ctor_get(v_t_816_, 2);
lean_inc_ref(v_rhs_841_);
lean_dec_ref_known(v_t_816_, 3);
v___x_842_ = lean_box(v_op_840_);
v___x_843_ = lean_apply_4(v_bin_820_, v_w_838_, v_lhs_839_, v___x_842_, v_rhs_841_);
return v___x_843_;
}
case 4:
{
lean_object* v_w_844_; lean_object* v_op_845_; lean_object* v_operand_846_; lean_object* v___x_847_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_w_844_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_844_);
v_op_845_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_op_845_);
v_operand_846_ = lean_ctor_get(v_t_816_, 2);
lean_inc_ref(v_operand_846_);
lean_dec_ref_known(v_t_816_, 3);
v___x_847_ = lean_apply_3(v_un_821_, v_w_844_, v_op_845_, v_operand_846_);
return v___x_847_;
}
case 5:
{
lean_object* v_l_848_; lean_object* v_r_849_; lean_object* v_w_850_; lean_object* v_lhs_851_; lean_object* v_rhs_852_; lean_object* v___x_853_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_l_848_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_l_848_);
v_r_849_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_r_849_);
v_w_850_ = lean_ctor_get(v_t_816_, 2);
lean_inc(v_w_850_);
v_lhs_851_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_lhs_851_);
v_rhs_852_ = lean_ctor_get(v_t_816_, 4);
lean_inc_ref(v_rhs_852_);
lean_dec_ref_known(v_t_816_, 5);
v___x_853_ = lean_apply_6(v_append_822_, v_l_848_, v_r_849_, v_w_850_, v_lhs_851_, v_rhs_852_, lean_box(0));
return v___x_853_;
}
case 6:
{
lean_object* v_w_854_; lean_object* v_w_x27_855_; lean_object* v_n_856_; lean_object* v_expr_857_; lean_object* v___x_858_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_w_854_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_w_854_);
v_w_x27_855_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_w_x27_855_);
v_n_856_ = lean_ctor_get(v_t_816_, 2);
lean_inc(v_n_856_);
v_expr_857_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_expr_857_);
lean_dec_ref_known(v_t_816_, 4);
v___x_858_ = lean_apply_5(v_replicate_823_, v_w_854_, v_w_x27_855_, v_n_856_, v_expr_857_, lean_box(0));
return v___x_858_;
}
case 7:
{
lean_object* v_m_859_; lean_object* v_n_860_; lean_object* v_lhs_861_; lean_object* v_rhs_862_; lean_object* v___x_863_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftRight_825_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_m_859_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_m_859_);
v_n_860_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_n_860_);
v_lhs_861_ = lean_ctor_get(v_t_816_, 2);
lean_inc_ref(v_lhs_861_);
v_rhs_862_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_rhs_862_);
lean_dec_ref_known(v_t_816_, 4);
v___x_863_ = lean_apply_4(v_shiftLeft_824_, v_m_859_, v_n_860_, v_lhs_861_, v_rhs_862_);
return v___x_863_;
}
case 8:
{
lean_object* v_m_864_; lean_object* v_n_865_; lean_object* v_lhs_866_; lean_object* v_rhs_867_; lean_object* v___x_868_; 
lean_dec(v_arithShiftRight_826_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_m_864_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_m_864_);
v_n_865_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_n_865_);
v_lhs_866_ = lean_ctor_get(v_t_816_, 2);
lean_inc_ref(v_lhs_866_);
v_rhs_867_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_rhs_867_);
lean_dec_ref_known(v_t_816_, 4);
v___x_868_ = lean_apply_4(v_shiftRight_825_, v_m_864_, v_n_865_, v_lhs_866_, v_rhs_867_);
return v___x_868_;
}
default: 
{
lean_object* v_m_869_; lean_object* v_n_870_; lean_object* v_lhs_871_; lean_object* v_rhs_872_; lean_object* v___x_873_; 
lean_dec(v_shiftRight_825_);
lean_dec(v_shiftLeft_824_);
lean_dec(v_replicate_823_);
lean_dec(v_append_822_);
lean_dec(v_un_821_);
lean_dec(v_bin_820_);
lean_dec(v_extract_819_);
lean_dec(v_const_818_);
lean_dec(v_var_817_);
v_m_869_ = lean_ctor_get(v_t_816_, 0);
lean_inc(v_m_869_);
v_n_870_ = lean_ctor_get(v_t_816_, 1);
lean_inc(v_n_870_);
v_lhs_871_ = lean_ctor_get(v_t_816_, 2);
lean_inc_ref(v_lhs_871_);
v_rhs_872_ = lean_ctor_get(v_t_816_, 3);
lean_inc_ref(v_rhs_872_);
lean_dec_ref_known(v_t_816_, 4);
v___x_873_ = lean_apply_4(v_arithShiftRight_826_, v_m_869_, v_n_870_, v_lhs_871_, v_rhs_872_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_874_, lean_object* v_a_875_, lean_object* v_t_876_, lean_object* v_var_877_, lean_object* v_const_878_, lean_object* v_extract_879_, lean_object* v_bin_880_, lean_object* v_un_881_, lean_object* v_append_882_, lean_object* v_replicate_883_, lean_object* v_shiftLeft_884_, lean_object* v_shiftRight_885_, lean_object* v_arithShiftRight_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_874_, v_a_875_, v_t_876_, v_var_877_, v_const_878_, v_extract_879_, v_bin_880_, v_un_881_, v_append_882_, v_replicate_883_, v_shiftLeft_884_, v_shiftRight_885_, v_arithShiftRight_886_);
lean_dec(v_a_875_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_888_, lean_object* v_idx_889_){
_start:
{
uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; lean_object* v___x_895_; 
v___x_890_ = 5ULL;
v___x_891_ = lean_uint64_of_nat(v_w_888_);
v___x_892_ = lean_uint64_of_nat(v_idx_889_);
v___x_893_ = lean_uint64_mix_hash(v___x_891_, v___x_892_);
v___x_894_ = lean_uint64_mix_hash(v___x_890_, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_895_, 0, v_w_888_);
lean_ctor_set(v___x_895_, 1, v_idx_889_);
lean_ctor_set_uint64(v___x_895_, sizeof(void*)*2, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_896_, lean_object* v_val_897_){
_start:
{
uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; lean_object* v___x_903_; 
v___x_898_ = 7ULL;
v___x_899_ = lean_uint64_of_nat(v_w_896_);
v___x_900_ = l_BitVec_hash(v_w_896_, v_val_897_);
v___x_901_ = lean_uint64_mix_hash(v___x_899_, v___x_900_);
v___x_902_ = lean_uint64_mix_hash(v___x_898_, v___x_901_);
v___x_903_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_903_, 0, v_w_896_);
lean_ctor_set(v___x_903_, 1, v_val_897_);
lean_ctor_set_uint64(v___x_903_, sizeof(void*)*2, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_904_, lean_object* v_start_905_, lean_object* v_len_906_, lean_object* v_expr_907_){
_start:
{
uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___y_912_; 
v___x_908_ = 11ULL;
v___x_909_ = lean_uint64_of_nat(v_start_905_);
v___x_910_ = lean_uint64_of_nat(v_len_906_);
switch(lean_obj_tag(v_expr_907_))
{
case 0:
{
uint64_t v_hashCode_917_; 
v_hashCode_917_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*2);
v___y_912_ = v_hashCode_917_;
goto v___jp_911_;
}
case 1:
{
uint64_t v_hashCode_918_; 
v_hashCode_918_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*2);
v___y_912_ = v_hashCode_918_;
goto v___jp_911_;
}
case 3:
{
uint64_t v_hashCode_919_; 
v_hashCode_919_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*3);
v___y_912_ = v_hashCode_919_;
goto v___jp_911_;
}
case 4:
{
uint64_t v_hashCode_920_; 
v_hashCode_920_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*3);
v___y_912_ = v_hashCode_920_;
goto v___jp_911_;
}
case 5:
{
uint64_t v_hashCode_921_; 
v_hashCode_921_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*5);
v___y_912_ = v_hashCode_921_;
goto v___jp_911_;
}
default: 
{
uint64_t v_hashCode_922_; 
v_hashCode_922_ = lean_ctor_get_uint64(v_expr_907_, sizeof(void*)*4);
v___y_912_ = v_hashCode_922_;
goto v___jp_911_;
}
}
v___jp_911_:
{
uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; lean_object* v___x_916_; 
v___x_913_ = lean_uint64_mix_hash(v___x_910_, v___y_912_);
v___x_914_ = lean_uint64_mix_hash(v___x_909_, v___x_913_);
v___x_915_ = lean_uint64_mix_hash(v___x_908_, v___x_914_);
v___x_916_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_916_, 0, v_w_904_);
lean_ctor_set(v___x_916_, 1, v_start_905_);
lean_ctor_set(v___x_916_, 2, v_len_906_);
lean_ctor_set(v___x_916_, 3, v_expr_907_);
lean_ctor_set_uint64(v___x_916_, sizeof(void*)*4, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_923_, lean_object* v_lhs_924_, uint8_t v_op_925_, lean_object* v_rhs_926_){
_start:
{
uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v___y_930_; uint64_t v___y_931_; uint64_t v___y_932_; uint64_t v___y_939_; 
v___x_927_ = 13ULL;
v___x_928_ = lean_uint64_of_nat(v_w_923_);
switch(lean_obj_tag(v_lhs_924_))
{
case 0:
{
uint64_t v_hashCode_947_; 
v_hashCode_947_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*2);
v___y_939_ = v_hashCode_947_;
goto v___jp_938_;
}
case 1:
{
uint64_t v_hashCode_948_; 
v_hashCode_948_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*2);
v___y_939_ = v_hashCode_948_;
goto v___jp_938_;
}
case 3:
{
uint64_t v_hashCode_949_; 
v_hashCode_949_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*3);
v___y_939_ = v_hashCode_949_;
goto v___jp_938_;
}
case 4:
{
uint64_t v_hashCode_950_; 
v_hashCode_950_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*3);
v___y_939_ = v_hashCode_950_;
goto v___jp_938_;
}
case 5:
{
uint64_t v_hashCode_951_; 
v_hashCode_951_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*5);
v___y_939_ = v_hashCode_951_;
goto v___jp_938_;
}
default: 
{
uint64_t v_hashCode_952_; 
v_hashCode_952_ = lean_ctor_get_uint64(v_lhs_924_, sizeof(void*)*4);
v___y_939_ = v_hashCode_952_;
goto v___jp_938_;
}
}
v___jp_929_:
{
uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; lean_object* v___x_937_; 
v___x_933_ = lean_uint64_mix_hash(v___y_931_, v___y_932_);
v___x_934_ = lean_uint64_mix_hash(v___y_930_, v___x_933_);
v___x_935_ = lean_uint64_mix_hash(v___x_928_, v___x_934_);
v___x_936_ = lean_uint64_mix_hash(v___x_927_, v___x_935_);
v___x_937_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_937_, 0, v_w_923_);
lean_ctor_set(v___x_937_, 1, v_lhs_924_);
lean_ctor_set(v___x_937_, 2, v_rhs_926_);
lean_ctor_set_uint64(v___x_937_, sizeof(void*)*3, v___x_936_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*3 + 8, v_op_925_);
return v___x_937_;
}
v___jp_938_:
{
uint64_t v___x_940_; 
v___x_940_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_925_);
switch(lean_obj_tag(v_rhs_926_))
{
case 0:
{
uint64_t v_hashCode_941_; 
v_hashCode_941_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*2);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_941_;
goto v___jp_929_;
}
case 1:
{
uint64_t v_hashCode_942_; 
v_hashCode_942_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*2);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_942_;
goto v___jp_929_;
}
case 3:
{
uint64_t v_hashCode_943_; 
v_hashCode_943_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*3);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_943_;
goto v___jp_929_;
}
case 4:
{
uint64_t v_hashCode_944_; 
v_hashCode_944_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*3);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_944_;
goto v___jp_929_;
}
case 5:
{
uint64_t v_hashCode_945_; 
v_hashCode_945_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*5);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_945_;
goto v___jp_929_;
}
default: 
{
uint64_t v_hashCode_946_; 
v_hashCode_946_ = lean_ctor_get_uint64(v_rhs_926_, sizeof(void*)*4);
v___y_930_ = v___y_939_;
v___y_931_ = v___x_940_;
v___y_932_ = v_hashCode_946_;
goto v___jp_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_953_, lean_object* v_lhs_954_, lean_object* v_op_955_, lean_object* v_rhs_956_){
_start:
{
uint8_t v_op_boxed_957_; lean_object* v_res_958_; 
v_op_boxed_957_ = lean_unbox(v_op_955_);
v_res_958_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_953_, v_lhs_954_, v_op_boxed_957_, v_rhs_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_959_, lean_object* v_op_960_, lean_object* v_operand_961_){
_start:
{
uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v___y_966_; 
v___x_962_ = 17ULL;
v___x_963_ = lean_uint64_of_nat(v_w_959_);
v___x_964_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_960_);
switch(lean_obj_tag(v_operand_961_))
{
case 0:
{
uint64_t v_hashCode_971_; 
v_hashCode_971_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*2);
v___y_966_ = v_hashCode_971_;
goto v___jp_965_;
}
case 1:
{
uint64_t v_hashCode_972_; 
v_hashCode_972_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*2);
v___y_966_ = v_hashCode_972_;
goto v___jp_965_;
}
case 3:
{
uint64_t v_hashCode_973_; 
v_hashCode_973_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*3);
v___y_966_ = v_hashCode_973_;
goto v___jp_965_;
}
case 4:
{
uint64_t v_hashCode_974_; 
v_hashCode_974_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*3);
v___y_966_ = v_hashCode_974_;
goto v___jp_965_;
}
case 5:
{
uint64_t v_hashCode_975_; 
v_hashCode_975_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*5);
v___y_966_ = v_hashCode_975_;
goto v___jp_965_;
}
default: 
{
uint64_t v_hashCode_976_; 
v_hashCode_976_ = lean_ctor_get_uint64(v_operand_961_, sizeof(void*)*4);
v___y_966_ = v_hashCode_976_;
goto v___jp_965_;
}
}
v___jp_965_:
{
uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; lean_object* v___x_970_; 
v___x_967_ = lean_uint64_mix_hash(v___x_964_, v___y_966_);
v___x_968_ = lean_uint64_mix_hash(v___x_963_, v___x_967_);
v___x_969_ = lean_uint64_mix_hash(v___x_962_, v___x_968_);
v___x_970_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_970_, 0, v_w_959_);
lean_ctor_set(v___x_970_, 1, v_op_960_);
lean_ctor_set(v___x_970_, 2, v_operand_961_);
lean_ctor_set_uint64(v___x_970_, sizeof(void*)*3, v___x_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_977_, lean_object* v_r_978_, lean_object* v_w_979_, lean_object* v_lhs_980_, lean_object* v_rhs_981_){
_start:
{
uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___y_985_; uint64_t v___y_986_; uint64_t v___y_992_; 
v___x_982_ = 19ULL;
v___x_983_ = lean_uint64_of_nat(v_w_979_);
switch(lean_obj_tag(v_lhs_980_))
{
case 0:
{
uint64_t v_hashCode_999_; 
v_hashCode_999_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*2);
v___y_992_ = v_hashCode_999_;
goto v___jp_991_;
}
case 1:
{
uint64_t v_hashCode_1000_; 
v_hashCode_1000_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*2);
v___y_992_ = v_hashCode_1000_;
goto v___jp_991_;
}
case 3:
{
uint64_t v_hashCode_1001_; 
v_hashCode_1001_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*3);
v___y_992_ = v_hashCode_1001_;
goto v___jp_991_;
}
case 4:
{
uint64_t v_hashCode_1002_; 
v_hashCode_1002_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*3);
v___y_992_ = v_hashCode_1002_;
goto v___jp_991_;
}
case 5:
{
uint64_t v_hashCode_1003_; 
v_hashCode_1003_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*5);
v___y_992_ = v_hashCode_1003_;
goto v___jp_991_;
}
default: 
{
uint64_t v_hashCode_1004_; 
v_hashCode_1004_ = lean_ctor_get_uint64(v_lhs_980_, sizeof(void*)*4);
v___y_992_ = v_hashCode_1004_;
goto v___jp_991_;
}
}
v___jp_984_:
{
uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_uint64_mix_hash(v___y_985_, v___y_986_);
v___x_988_ = lean_uint64_mix_hash(v___x_983_, v___x_987_);
v___x_989_ = lean_uint64_mix_hash(v___x_982_, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_990_, 0, v_l_977_);
lean_ctor_set(v___x_990_, 1, v_r_978_);
lean_ctor_set(v___x_990_, 2, v_w_979_);
lean_ctor_set(v___x_990_, 3, v_lhs_980_);
lean_ctor_set(v___x_990_, 4, v_rhs_981_);
lean_ctor_set_uint64(v___x_990_, sizeof(void*)*5, v___x_989_);
return v___x_990_;
}
v___jp_991_:
{
switch(lean_obj_tag(v_rhs_981_))
{
case 0:
{
uint64_t v_hashCode_993_; 
v_hashCode_993_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*2);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_993_;
goto v___jp_984_;
}
case 1:
{
uint64_t v_hashCode_994_; 
v_hashCode_994_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*2);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_994_;
goto v___jp_984_;
}
case 3:
{
uint64_t v_hashCode_995_; 
v_hashCode_995_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*3);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_995_;
goto v___jp_984_;
}
case 4:
{
uint64_t v_hashCode_996_; 
v_hashCode_996_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*3);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_996_;
goto v___jp_984_;
}
case 5:
{
uint64_t v_hashCode_997_; 
v_hashCode_997_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*5);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_997_;
goto v___jp_984_;
}
default: 
{
uint64_t v_hashCode_998_; 
v_hashCode_998_ = lean_ctor_get_uint64(v_rhs_981_, sizeof(void*)*4);
v___y_985_ = v___y_992_;
v___y_986_ = v_hashCode_998_;
goto v___jp_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_1005_, lean_object* v_r_1006_, lean_object* v_w_1007_, lean_object* v_lhs_1008_, lean_object* v_rhs_1009_, lean_object* v_h_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_1005_, v_r_1006_, v_w_1007_, v_lhs_1008_, v_rhs_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_1012_, lean_object* v_w_x27_1013_, lean_object* v_n_1014_, lean_object* v_expr_1015_){
_start:
{
uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___y_1020_; 
v___x_1016_ = 23ULL;
v___x_1017_ = lean_uint64_of_nat(v_w_x27_1013_);
v___x_1018_ = lean_uint64_of_nat(v_n_1014_);
switch(lean_obj_tag(v_expr_1015_))
{
case 0:
{
uint64_t v_hashCode_1025_; 
v_hashCode_1025_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*2);
v___y_1020_ = v_hashCode_1025_;
goto v___jp_1019_;
}
case 1:
{
uint64_t v_hashCode_1026_; 
v_hashCode_1026_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*2);
v___y_1020_ = v_hashCode_1026_;
goto v___jp_1019_;
}
case 3:
{
uint64_t v_hashCode_1027_; 
v_hashCode_1027_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*3);
v___y_1020_ = v_hashCode_1027_;
goto v___jp_1019_;
}
case 4:
{
uint64_t v_hashCode_1028_; 
v_hashCode_1028_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*3);
v___y_1020_ = v_hashCode_1028_;
goto v___jp_1019_;
}
case 5:
{
uint64_t v_hashCode_1029_; 
v_hashCode_1029_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*5);
v___y_1020_ = v_hashCode_1029_;
goto v___jp_1019_;
}
default: 
{
uint64_t v_hashCode_1030_; 
v_hashCode_1030_ = lean_ctor_get_uint64(v_expr_1015_, sizeof(void*)*4);
v___y_1020_ = v_hashCode_1030_;
goto v___jp_1019_;
}
}
v___jp_1019_:
{
uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_uint64_mix_hash(v___x_1018_, v___y_1020_);
v___x_1022_ = lean_uint64_mix_hash(v___x_1017_, v___x_1021_);
v___x_1023_ = lean_uint64_mix_hash(v___x_1016_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1024_, 0, v_w_1012_);
lean_ctor_set(v___x_1024_, 1, v_w_x27_1013_);
lean_ctor_set(v___x_1024_, 2, v_n_1014_);
lean_ctor_set(v___x_1024_, 3, v_expr_1015_);
lean_ctor_set_uint64(v___x_1024_, sizeof(void*)*4, v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1031_, lean_object* v_w_x27_1032_, lean_object* v_n_1033_, lean_object* v_expr_1034_, lean_object* v_h_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1031_, v_w_x27_1032_, v_n_1033_, v_expr_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1037_, lean_object* v_n_1038_, lean_object* v_lhs_1039_, lean_object* v_rhs_1040_){
_start:
{
uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v___y_1044_; uint64_t v___y_1045_; uint64_t v___y_1051_; 
v___x_1041_ = 29ULL;
v___x_1042_ = lean_uint64_of_nat(v_m_1037_);
switch(lean_obj_tag(v_lhs_1039_))
{
case 0:
{
uint64_t v_hashCode_1058_; 
v_hashCode_1058_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*2);
v___y_1051_ = v_hashCode_1058_;
goto v___jp_1050_;
}
case 1:
{
uint64_t v_hashCode_1059_; 
v_hashCode_1059_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*2);
v___y_1051_ = v_hashCode_1059_;
goto v___jp_1050_;
}
case 3:
{
uint64_t v_hashCode_1060_; 
v_hashCode_1060_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*3);
v___y_1051_ = v_hashCode_1060_;
goto v___jp_1050_;
}
case 4:
{
uint64_t v_hashCode_1061_; 
v_hashCode_1061_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*3);
v___y_1051_ = v_hashCode_1061_;
goto v___jp_1050_;
}
case 5:
{
uint64_t v_hashCode_1062_; 
v_hashCode_1062_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*5);
v___y_1051_ = v_hashCode_1062_;
goto v___jp_1050_;
}
default: 
{
uint64_t v_hashCode_1063_; 
v_hashCode_1063_ = lean_ctor_get_uint64(v_lhs_1039_, sizeof(void*)*4);
v___y_1051_ = v_hashCode_1063_;
goto v___jp_1050_;
}
}
v___jp_1043_:
{
uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_uint64_mix_hash(v___y_1044_, v___y_1045_);
v___x_1047_ = lean_uint64_mix_hash(v___x_1042_, v___x_1046_);
v___x_1048_ = lean_uint64_mix_hash(v___x_1041_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1049_, 0, v_m_1037_);
lean_ctor_set(v___x_1049_, 1, v_n_1038_);
lean_ctor_set(v___x_1049_, 2, v_lhs_1039_);
lean_ctor_set(v___x_1049_, 3, v_rhs_1040_);
lean_ctor_set_uint64(v___x_1049_, sizeof(void*)*4, v___x_1048_);
return v___x_1049_;
}
v___jp_1050_:
{
switch(lean_obj_tag(v_rhs_1040_))
{
case 0:
{
uint64_t v_hashCode_1052_; 
v_hashCode_1052_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*2);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1052_;
goto v___jp_1043_;
}
case 1:
{
uint64_t v_hashCode_1053_; 
v_hashCode_1053_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*2);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1053_;
goto v___jp_1043_;
}
case 3:
{
uint64_t v_hashCode_1054_; 
v_hashCode_1054_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*3);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1054_;
goto v___jp_1043_;
}
case 4:
{
uint64_t v_hashCode_1055_; 
v_hashCode_1055_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*3);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1055_;
goto v___jp_1043_;
}
case 5:
{
uint64_t v_hashCode_1056_; 
v_hashCode_1056_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*5);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1056_;
goto v___jp_1043_;
}
default: 
{
uint64_t v_hashCode_1057_; 
v_hashCode_1057_ = lean_ctor_get_uint64(v_rhs_1040_, sizeof(void*)*4);
v___y_1044_ = v___y_1051_;
v___y_1045_ = v_hashCode_1057_;
goto v___jp_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1064_, lean_object* v_n_1065_, lean_object* v_lhs_1066_, lean_object* v_rhs_1067_){
_start:
{
uint64_t v___x_1068_; uint64_t v___x_1069_; uint64_t v___y_1071_; uint64_t v___y_1072_; uint64_t v___y_1078_; 
v___x_1068_ = 31ULL;
v___x_1069_ = lean_uint64_of_nat(v_m_1064_);
switch(lean_obj_tag(v_lhs_1066_))
{
case 0:
{
uint64_t v_hashCode_1085_; 
v_hashCode_1085_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*2);
v___y_1078_ = v_hashCode_1085_;
goto v___jp_1077_;
}
case 1:
{
uint64_t v_hashCode_1086_; 
v_hashCode_1086_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*2);
v___y_1078_ = v_hashCode_1086_;
goto v___jp_1077_;
}
case 3:
{
uint64_t v_hashCode_1087_; 
v_hashCode_1087_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*3);
v___y_1078_ = v_hashCode_1087_;
goto v___jp_1077_;
}
case 4:
{
uint64_t v_hashCode_1088_; 
v_hashCode_1088_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*3);
v___y_1078_ = v_hashCode_1088_;
goto v___jp_1077_;
}
case 5:
{
uint64_t v_hashCode_1089_; 
v_hashCode_1089_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*5);
v___y_1078_ = v_hashCode_1089_;
goto v___jp_1077_;
}
default: 
{
uint64_t v_hashCode_1090_; 
v_hashCode_1090_ = lean_ctor_get_uint64(v_lhs_1066_, sizeof(void*)*4);
v___y_1078_ = v_hashCode_1090_;
goto v___jp_1077_;
}
}
v___jp_1070_:
{
uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_uint64_mix_hash(v___y_1071_, v___y_1072_);
v___x_1074_ = lean_uint64_mix_hash(v___x_1069_, v___x_1073_);
v___x_1075_ = lean_uint64_mix_hash(v___x_1068_, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1076_, 0, v_m_1064_);
lean_ctor_set(v___x_1076_, 1, v_n_1065_);
lean_ctor_set(v___x_1076_, 2, v_lhs_1066_);
lean_ctor_set(v___x_1076_, 3, v_rhs_1067_);
lean_ctor_set_uint64(v___x_1076_, sizeof(void*)*4, v___x_1075_);
return v___x_1076_;
}
v___jp_1077_:
{
switch(lean_obj_tag(v_rhs_1067_))
{
case 0:
{
uint64_t v_hashCode_1079_; 
v_hashCode_1079_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*2);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1079_;
goto v___jp_1070_;
}
case 1:
{
uint64_t v_hashCode_1080_; 
v_hashCode_1080_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*2);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1080_;
goto v___jp_1070_;
}
case 3:
{
uint64_t v_hashCode_1081_; 
v_hashCode_1081_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*3);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1081_;
goto v___jp_1070_;
}
case 4:
{
uint64_t v_hashCode_1082_; 
v_hashCode_1082_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*3);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1082_;
goto v___jp_1070_;
}
case 5:
{
uint64_t v_hashCode_1083_; 
v_hashCode_1083_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*5);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1083_;
goto v___jp_1070_;
}
default: 
{
uint64_t v_hashCode_1084_; 
v_hashCode_1084_ = lean_ctor_get_uint64(v_rhs_1067_, sizeof(void*)*4);
v___y_1071_ = v___y_1078_;
v___y_1072_ = v_hashCode_1084_;
goto v___jp_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1091_, lean_object* v_n_1092_, lean_object* v_lhs_1093_, lean_object* v_rhs_1094_){
_start:
{
uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___y_1098_; uint64_t v___y_1099_; uint64_t v___y_1105_; 
v___x_1095_ = 37ULL;
v___x_1096_ = lean_uint64_of_nat(v_m_1091_);
switch(lean_obj_tag(v_lhs_1093_))
{
case 0:
{
uint64_t v_hashCode_1112_; 
v_hashCode_1112_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*2);
v___y_1105_ = v_hashCode_1112_;
goto v___jp_1104_;
}
case 1:
{
uint64_t v_hashCode_1113_; 
v_hashCode_1113_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*2);
v___y_1105_ = v_hashCode_1113_;
goto v___jp_1104_;
}
case 3:
{
uint64_t v_hashCode_1114_; 
v_hashCode_1114_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*3);
v___y_1105_ = v_hashCode_1114_;
goto v___jp_1104_;
}
case 4:
{
uint64_t v_hashCode_1115_; 
v_hashCode_1115_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*3);
v___y_1105_ = v_hashCode_1115_;
goto v___jp_1104_;
}
case 5:
{
uint64_t v_hashCode_1116_; 
v_hashCode_1116_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*5);
v___y_1105_ = v_hashCode_1116_;
goto v___jp_1104_;
}
default: 
{
uint64_t v_hashCode_1117_; 
v_hashCode_1117_ = lean_ctor_get_uint64(v_lhs_1093_, sizeof(void*)*4);
v___y_1105_ = v_hashCode_1117_;
goto v___jp_1104_;
}
}
v___jp_1097_:
{
uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_uint64_mix_hash(v___y_1098_, v___y_1099_);
v___x_1101_ = lean_uint64_mix_hash(v___x_1096_, v___x_1100_);
v___x_1102_ = lean_uint64_mix_hash(v___x_1095_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1103_, 0, v_m_1091_);
lean_ctor_set(v___x_1103_, 1, v_n_1092_);
lean_ctor_set(v___x_1103_, 2, v_lhs_1093_);
lean_ctor_set(v___x_1103_, 3, v_rhs_1094_);
lean_ctor_set_uint64(v___x_1103_, sizeof(void*)*4, v___x_1102_);
return v___x_1103_;
}
v___jp_1104_:
{
switch(lean_obj_tag(v_rhs_1094_))
{
case 0:
{
uint64_t v_hashCode_1106_; 
v_hashCode_1106_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*2);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1106_;
goto v___jp_1097_;
}
case 1:
{
uint64_t v_hashCode_1107_; 
v_hashCode_1107_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*2);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1107_;
goto v___jp_1097_;
}
case 3:
{
uint64_t v_hashCode_1108_; 
v_hashCode_1108_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*3);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1108_;
goto v___jp_1097_;
}
case 4:
{
uint64_t v_hashCode_1109_; 
v_hashCode_1109_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*3);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1109_;
goto v___jp_1097_;
}
case 5:
{
uint64_t v_hashCode_1110_; 
v_hashCode_1110_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*5);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1110_;
goto v___jp_1097_;
}
default: 
{
uint64_t v_hashCode_1111_; 
v_hashCode_1111_ = lean_ctor_get_uint64(v_rhs_1094_, sizeof(void*)*4);
v___y_1098_ = v___y_1105_;
v___y_1099_ = v_hashCode_1111_;
goto v___jp_1097_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1118_){
_start:
{
switch(lean_obj_tag(v_x_1118_))
{
case 0:
{
uint64_t v_hashCode_1119_; 
v_hashCode_1119_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*2);
return v_hashCode_1119_;
}
case 1:
{
uint64_t v_hashCode_1120_; 
v_hashCode_1120_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*2);
return v_hashCode_1120_;
}
case 3:
{
uint64_t v_hashCode_1121_; 
v_hashCode_1121_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*3);
return v_hashCode_1121_;
}
case 4:
{
uint64_t v_hashCode_1122_; 
v_hashCode_1122_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*3);
return v_hashCode_1122_;
}
case 5:
{
uint64_t v_hashCode_1123_; 
v_hashCode_1123_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*5);
return v_hashCode_1123_;
}
default: 
{
uint64_t v_hashCode_1124_; 
v_hashCode_1124_ = lean_ctor_get_uint64(v_x_1118_, sizeof(void*)*4);
return v_hashCode_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* v_x_1125_){
_start:
{
uint64_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1125_);
lean_dec_ref(v_x_1125_);
v_r_1127_ = lean_box_uint64(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1128_, lean_object* v_x_1129_){
_start:
{
switch(lean_obj_tag(v_x_1129_))
{
case 0:
{
uint64_t v_hashCode_1130_; 
v_hashCode_1130_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*2);
return v_hashCode_1130_;
}
case 1:
{
uint64_t v_hashCode_1131_; 
v_hashCode_1131_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*2);
return v_hashCode_1131_;
}
case 3:
{
uint64_t v_hashCode_1132_; 
v_hashCode_1132_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*3);
return v_hashCode_1132_;
}
case 4:
{
uint64_t v_hashCode_1133_; 
v_hashCode_1133_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*3);
return v_hashCode_1133_;
}
case 5:
{
uint64_t v_hashCode_1134_; 
v_hashCode_1134_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*5);
return v_hashCode_1134_;
}
default: 
{
uint64_t v_hashCode_1135_; 
v_hashCode_1135_ = lean_ctor_get_uint64(v_x_1129_, sizeof(void*)*4);
return v_hashCode_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
uint64_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1136_, v_x_1137_);
lean_dec_ref(v_x_1137_);
lean_dec(v_a_1136_);
v_r_1139_ = lean_box_uint64(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(lean_object* v_expr_1140_){
_start:
{
switch(lean_obj_tag(v_expr_1140_))
{
case 0:
{
uint64_t v_hashCode_1141_; 
v_hashCode_1141_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*2);
return v_hashCode_1141_;
}
case 1:
{
uint64_t v_hashCode_1142_; 
v_hashCode_1142_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*2);
return v_hashCode_1142_;
}
case 3:
{
uint64_t v_hashCode_1143_; 
v_hashCode_1143_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*3);
return v_hashCode_1143_;
}
case 4:
{
uint64_t v_hashCode_1144_; 
v_hashCode_1144_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*3);
return v_hashCode_1144_;
}
case 5:
{
uint64_t v_hashCode_1145_; 
v_hashCode_1145_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*5);
return v_hashCode_1145_;
}
default: 
{
uint64_t v_hashCode_1146_; 
v_hashCode_1146_ = lean_ctor_get_uint64(v_expr_1140_, sizeof(void*)*4);
return v_hashCode_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0___boxed(lean_object* v_expr_1147_){
_start:
{
uint64_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(v_expr_1147_);
lean_dec_ref(v_expr_1147_);
v_r_1149_ = lean_box_uint64(v_res_1148_);
return v_r_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg(){
_start:
{
lean_object* v___f_1152_; 
v___f_1152_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___boxed(lean_object* v___dummy_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg();
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1155_){
_start:
{
lean_object* v___f_1156_; 
v___f_1156_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* v_w_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_1157_);
lean_dec(v_w_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(lean_object* v_a_1159_, lean_object* v_b_1160_, lean_object* v_k_1161_){
_start:
{
size_t v___x_1162_; size_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_ptr_addr(v_a_1159_);
v___x_1163_ = lean_ptr_addr(v_b_1160_);
v___x_1164_ = lean_usize_dec_eq(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_apply_1(v_k_1161_, v___x_1165_);
v___x_1167_ = lean_unbox(v___x_1166_);
return v___x_1167_;
}
else
{
lean_dec_ref(v_k_1161_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg___boxed(lean_object* v_a_1168_, lean_object* v_b_1169_, lean_object* v_k_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(v_a_1168_, v_b_1169_, v_k_1170_);
lean_dec_ref(v_b_1169_);
lean_dec_ref(v_a_1168_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(lean_object* v_w_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v_k_1176_, lean_object* v_h_1177_){
_start:
{
size_t v___x_1178_; size_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = lean_ptr_addr(v_a_1174_);
v___x_1179_ = lean_ptr_addr(v_b_1175_);
v___x_1180_ = lean_usize_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_apply_1(v_k_1176_, v___x_1181_);
v___x_1183_ = lean_unbox(v___x_1182_);
return v___x_1183_;
}
else
{
lean_dec_ref(v_k_1176_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___boxed(lean_object* v_w_1184_, lean_object* v_a_1185_, lean_object* v_b_1186_, lean_object* v_k_1187_, lean_object* v_h_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(v_w_1184_, v_a_1185_, v_b_1186_, v_k_1187_, v_h_1188_);
lean_dec_ref(v_b_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_w_1184_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1191_, lean_object* v_r_1192_){
_start:
{
size_t v___x_1193_; size_t v___x_1194_; uint8_t v___x_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; uint8_t v___y_1216_; uint64_t v___y_1219_; uint64_t v___y_1220_; uint64_t v___y_1299_; 
v___x_1193_ = lean_ptr_addr(v_l_1191_);
v___x_1194_ = lean_ptr_addr(v_r_1192_);
v___x_1195_ = lean_usize_dec_eq(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
switch(lean_obj_tag(v_l_1191_))
{
case 0:
{
uint64_t v_hashCode_1306_; 
v_hashCode_1306_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*2);
v___y_1299_ = v_hashCode_1306_;
goto v___jp_1298_;
}
case 1:
{
uint64_t v_hashCode_1307_; 
v_hashCode_1307_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*2);
v___y_1299_ = v_hashCode_1307_;
goto v___jp_1298_;
}
case 3:
{
uint64_t v_hashCode_1308_; 
v_hashCode_1308_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*3);
v___y_1299_ = v_hashCode_1308_;
goto v___jp_1298_;
}
case 4:
{
uint64_t v_hashCode_1309_; 
v_hashCode_1309_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*3);
v___y_1299_ = v_hashCode_1309_;
goto v___jp_1298_;
}
case 5:
{
uint64_t v_hashCode_1310_; 
v_hashCode_1310_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*5);
v___y_1299_ = v_hashCode_1310_;
goto v___jp_1298_;
}
default: 
{
uint64_t v_hashCode_1311_; 
v_hashCode_1311_ = lean_ctor_get_uint64(v_l_1191_, sizeof(void*)*4);
v___y_1299_ = v_hashCode_1311_;
goto v___jp_1298_;
}
}
}
else
{
return v___x_1195_;
}
v___jp_1196_:
{
if (v___y_1200_ == 0)
{
return v___y_1200_;
}
else
{
uint8_t v_decide_1201_; 
v_decide_1201_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1197_, v___y_1199_);
if (v_decide_1201_ == 0)
{
return v___x_1195_;
}
else
{
return v___y_1200_;
}
}
}
v___jp_1202_:
{
if (v___y_1209_ == 0)
{
return v___y_1209_;
}
else
{
uint8_t v_decide_1210_; 
v_decide_1210_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1208_, v___y_1203_);
if (v_decide_1210_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1211_; 
v_decide_1211_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1206_, v___y_1207_);
if (v_decide_1211_ == 0)
{
return v___x_1195_;
}
else
{
return v___y_1209_;
}
}
}
}
v___jp_1212_:
{
if (v___y_1216_ == 0)
{
return v___y_1216_;
}
else
{
uint8_t v_decide_1217_; 
v_decide_1217_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1214_, v___y_1215_);
if (v_decide_1217_ == 0)
{
return v___x_1195_;
}
else
{
return v___y_1216_;
}
}
}
v___jp_1218_:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_uint64_dec_eq(v___y_1219_, v___y_1220_);
if (v___x_1221_ == 0)
{
return v___x_1195_;
}
else
{
if (v___x_1195_ == 0)
{
switch(lean_obj_tag(v_l_1191_))
{
case 0:
{
if (lean_obj_tag(v_r_1192_) == 0)
{
lean_object* v_idx_1222_; lean_object* v_idx_1223_; uint8_t v___x_1224_; 
v_idx_1222_ = lean_ctor_get(v_l_1191_, 1);
v_idx_1223_ = lean_ctor_get(v_r_1192_, 1);
v___x_1224_ = lean_nat_dec_eq(v_idx_1222_, v_idx_1223_);
return v___x_1224_;
}
else
{
return v___x_1195_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1192_) == 1)
{
lean_object* v_val_1225_; lean_object* v_val_1226_; uint8_t v___x_1227_; 
v_val_1225_ = lean_ctor_get(v_l_1191_, 1);
v_val_1226_ = lean_ctor_get(v_r_1192_, 1);
v___x_1227_ = lean_nat_dec_eq(v_val_1225_, v_val_1226_);
return v___x_1227_;
}
else
{
return v___x_1195_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1192_) == 2)
{
lean_object* v_w_1228_; lean_object* v_start_1229_; lean_object* v_expr_1230_; lean_object* v_w_1231_; lean_object* v_start_1232_; lean_object* v_expr_1233_; uint8_t v___x_1234_; 
v_w_1228_ = lean_ctor_get(v_l_1191_, 0);
v_start_1229_ = lean_ctor_get(v_l_1191_, 1);
v_expr_1230_ = lean_ctor_get(v_l_1191_, 3);
v_w_1231_ = lean_ctor_get(v_r_1192_, 0);
v_start_1232_ = lean_ctor_get(v_r_1192_, 1);
v_expr_1233_ = lean_ctor_get(v_r_1192_, 3);
v___x_1234_ = lean_nat_dec_eq(v_w_1228_, v_w_1231_);
if (v___x_1234_ == 0)
{
v___y_1197_ = v_expr_1230_;
v___y_1198_ = v_w_1231_;
v___y_1199_ = v_expr_1233_;
v___y_1200_ = v___x_1234_;
goto v___jp_1196_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_eq(v_start_1229_, v_start_1232_);
v___y_1197_ = v_expr_1230_;
v___y_1198_ = v_w_1231_;
v___y_1199_ = v_expr_1233_;
v___y_1200_ = v___x_1235_;
goto v___jp_1196_;
}
}
else
{
return v___x_1195_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1192_) == 3)
{
lean_object* v_lhs_1236_; uint8_t v_op_1237_; lean_object* v_rhs_1238_; lean_object* v_lhs_1239_; uint8_t v_op_1240_; lean_object* v_rhs_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_lhs_1236_ = lean_ctor_get(v_l_1191_, 1);
v_op_1237_ = lean_ctor_get_uint8(v_l_1191_, sizeof(void*)*3 + 8);
v_rhs_1238_ = lean_ctor_get(v_l_1191_, 2);
v_lhs_1239_ = lean_ctor_get(v_r_1192_, 1);
v_op_1240_ = lean_ctor_get_uint8(v_r_1192_, sizeof(void*)*3 + 8);
v_rhs_1241_ = lean_ctor_get(v_r_1192_, 2);
v___x_1242_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_op_1237_);
v___x_1243_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_op_1240_);
v___x_1244_ = lean_nat_dec_eq(v___x_1242_, v___x_1243_);
lean_dec(v___x_1243_);
lean_dec(v___x_1242_);
if (v___x_1244_ == 0)
{
return v___x_1244_;
}
else
{
uint8_t v_decide_1245_; 
v_decide_1245_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1236_, v_lhs_1239_);
if (v_decide_1245_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1246_; 
v_decide_1246_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1238_, v_rhs_1241_);
if (v_decide_1246_ == 0)
{
return v___x_1195_;
}
else
{
return v___x_1244_;
}
}
}
}
else
{
return v___x_1195_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1192_) == 4)
{
lean_object* v_op_1247_; lean_object* v_operand_1248_; lean_object* v_op_1249_; lean_object* v_operand_1250_; uint8_t v___x_1251_; 
v_op_1247_ = lean_ctor_get(v_l_1191_, 1);
v_operand_1248_ = lean_ctor_get(v_l_1191_, 2);
v_op_1249_ = lean_ctor_get(v_r_1192_, 1);
v_operand_1250_ = lean_ctor_get(v_r_1192_, 2);
v___x_1251_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1247_, v_op_1249_);
if (v___x_1251_ == 0)
{
return v___x_1251_;
}
else
{
uint8_t v_decide_1252_; 
v_decide_1252_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_operand_1248_, v_operand_1250_);
if (v_decide_1252_ == 0)
{
return v___x_1195_;
}
else
{
return v___x_1251_;
}
}
}
else
{
return v___x_1195_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1192_) == 5)
{
lean_object* v_l_1253_; lean_object* v_r_1254_; lean_object* v_lhs_1255_; lean_object* v_rhs_1256_; lean_object* v_l_1257_; lean_object* v_r_1258_; lean_object* v_lhs_1259_; lean_object* v_rhs_1260_; uint8_t v___x_1261_; 
v_l_1253_ = lean_ctor_get(v_l_1191_, 0);
v_r_1254_ = lean_ctor_get(v_l_1191_, 1);
v_lhs_1255_ = lean_ctor_get(v_l_1191_, 3);
v_rhs_1256_ = lean_ctor_get(v_l_1191_, 4);
v_l_1257_ = lean_ctor_get(v_r_1192_, 0);
v_r_1258_ = lean_ctor_get(v_r_1192_, 1);
v_lhs_1259_ = lean_ctor_get(v_r_1192_, 3);
v_rhs_1260_ = lean_ctor_get(v_r_1192_, 4);
v___x_1261_ = lean_nat_dec_eq(v_l_1253_, v_l_1257_);
if (v___x_1261_ == 0)
{
v___y_1203_ = v_lhs_1259_;
v___y_1204_ = v_r_1258_;
v___y_1205_ = v_l_1257_;
v___y_1206_ = v_rhs_1256_;
v___y_1207_ = v_rhs_1260_;
v___y_1208_ = v_lhs_1255_;
v___y_1209_ = v___x_1261_;
goto v___jp_1202_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_r_1254_, v_r_1258_);
v___y_1203_ = v_lhs_1259_;
v___y_1204_ = v_r_1258_;
v___y_1205_ = v_l_1257_;
v___y_1206_ = v_rhs_1256_;
v___y_1207_ = v_rhs_1260_;
v___y_1208_ = v_lhs_1255_;
v___y_1209_ = v___x_1262_;
goto v___jp_1202_;
}
}
else
{
return v___x_1195_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1192_) == 6)
{
lean_object* v_w_1263_; lean_object* v_n_1264_; lean_object* v_expr_1265_; lean_object* v_w_1266_; lean_object* v_n_1267_; lean_object* v_expr_1268_; uint8_t v___x_1269_; 
v_w_1263_ = lean_ctor_get(v_l_1191_, 0);
v_n_1264_ = lean_ctor_get(v_l_1191_, 2);
v_expr_1265_ = lean_ctor_get(v_l_1191_, 3);
v_w_1266_ = lean_ctor_get(v_r_1192_, 0);
v_n_1267_ = lean_ctor_get(v_r_1192_, 2);
v_expr_1268_ = lean_ctor_get(v_r_1192_, 3);
v___x_1269_ = lean_nat_dec_eq(v_n_1264_, v_n_1267_);
if (v___x_1269_ == 0)
{
v___y_1213_ = v_w_1266_;
v___y_1214_ = v_expr_1265_;
v___y_1215_ = v_expr_1268_;
v___y_1216_ = v___x_1269_;
goto v___jp_1212_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_eq(v_w_1263_, v_w_1266_);
v___y_1213_ = v_w_1266_;
v___y_1214_ = v_expr_1265_;
v___y_1215_ = v_expr_1268_;
v___y_1216_ = v___x_1270_;
goto v___jp_1212_;
}
}
else
{
return v___x_1195_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1192_) == 7)
{
lean_object* v_n_1271_; lean_object* v_lhs_1272_; lean_object* v_rhs_1273_; lean_object* v_n_1274_; lean_object* v_lhs_1275_; lean_object* v_rhs_1276_; uint8_t v___x_1277_; 
v_n_1271_ = lean_ctor_get(v_l_1191_, 1);
v_lhs_1272_ = lean_ctor_get(v_l_1191_, 2);
v_rhs_1273_ = lean_ctor_get(v_l_1191_, 3);
v_n_1274_ = lean_ctor_get(v_r_1192_, 1);
v_lhs_1275_ = lean_ctor_get(v_r_1192_, 2);
v_rhs_1276_ = lean_ctor_get(v_r_1192_, 3);
v___x_1277_ = lean_nat_dec_eq(v_n_1271_, v_n_1274_);
if (v___x_1277_ == 0)
{
return v___x_1277_;
}
else
{
uint8_t v_decide_1278_; 
v_decide_1278_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1272_, v_lhs_1275_);
if (v_decide_1278_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1279_; 
v_decide_1279_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1273_, v_rhs_1276_);
if (v_decide_1279_ == 0)
{
return v___x_1195_;
}
else
{
return v___x_1277_;
}
}
}
}
else
{
return v___x_1195_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1192_) == 8)
{
lean_object* v_n_1280_; lean_object* v_lhs_1281_; lean_object* v_rhs_1282_; lean_object* v_n_1283_; lean_object* v_lhs_1284_; lean_object* v_rhs_1285_; uint8_t v___x_1286_; 
v_n_1280_ = lean_ctor_get(v_l_1191_, 1);
v_lhs_1281_ = lean_ctor_get(v_l_1191_, 2);
v_rhs_1282_ = lean_ctor_get(v_l_1191_, 3);
v_n_1283_ = lean_ctor_get(v_r_1192_, 1);
v_lhs_1284_ = lean_ctor_get(v_r_1192_, 2);
v_rhs_1285_ = lean_ctor_get(v_r_1192_, 3);
v___x_1286_ = lean_nat_dec_eq(v_n_1280_, v_n_1283_);
if (v___x_1286_ == 0)
{
return v___x_1286_;
}
else
{
uint8_t v_decide_1287_; 
v_decide_1287_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1281_, v_lhs_1284_);
if (v_decide_1287_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1288_; 
v_decide_1288_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1282_, v_rhs_1285_);
if (v_decide_1288_ == 0)
{
return v___x_1195_;
}
else
{
return v___x_1286_;
}
}
}
}
else
{
return v___x_1195_;
}
}
default: 
{
if (lean_obj_tag(v_r_1192_) == 9)
{
lean_object* v_n_1289_; lean_object* v_lhs_1290_; lean_object* v_rhs_1291_; lean_object* v_n_1292_; lean_object* v_lhs_1293_; lean_object* v_rhs_1294_; uint8_t v___x_1295_; 
v_n_1289_ = lean_ctor_get(v_l_1191_, 1);
v_lhs_1290_ = lean_ctor_get(v_l_1191_, 2);
v_rhs_1291_ = lean_ctor_get(v_l_1191_, 3);
v_n_1292_ = lean_ctor_get(v_r_1192_, 1);
v_lhs_1293_ = lean_ctor_get(v_r_1192_, 2);
v_rhs_1294_ = lean_ctor_get(v_r_1192_, 3);
v___x_1295_ = lean_nat_dec_eq(v_n_1289_, v_n_1292_);
if (v___x_1295_ == 0)
{
return v___x_1295_;
}
else
{
uint8_t v_decide_1296_; 
v_decide_1296_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1290_, v_lhs_1293_);
if (v_decide_1296_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1297_; 
v_decide_1297_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1291_, v_rhs_1294_);
if (v_decide_1297_ == 0)
{
return v___x_1195_;
}
else
{
return v___x_1295_;
}
}
}
}
else
{
return v___x_1195_;
}
}
}
}
else
{
return v___x_1195_;
}
}
}
v___jp_1298_:
{
switch(lean_obj_tag(v_r_1192_))
{
case 0:
{
uint64_t v_hashCode_1300_; 
v_hashCode_1300_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*2);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1300_;
goto v___jp_1218_;
}
case 1:
{
uint64_t v_hashCode_1301_; 
v_hashCode_1301_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*2);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1301_;
goto v___jp_1218_;
}
case 3:
{
uint64_t v_hashCode_1302_; 
v_hashCode_1302_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*3);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1302_;
goto v___jp_1218_;
}
case 4:
{
uint64_t v_hashCode_1303_; 
v_hashCode_1303_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*3);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1303_;
goto v___jp_1218_;
}
case 5:
{
uint64_t v_hashCode_1304_; 
v_hashCode_1304_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*5);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1304_;
goto v___jp_1218_;
}
default: 
{
uint64_t v_hashCode_1305_; 
v_hashCode_1305_ = lean_ctor_get_uint64(v_r_1192_, sizeof(void*)*4);
v___y_1219_ = v___y_1299_;
v___y_1220_ = v_hashCode_1305_;
goto v___jp_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1312_, lean_object* v_r_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1312_, v_r_1313_);
lean_dec_ref(v_r_1313_);
lean_dec_ref(v_l_1312_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1316_, lean_object* v_l_1317_, lean_object* v_r_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1317_, v_r_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1320_, lean_object* v_l_1321_, lean_object* v_r_1322_){
_start:
{
uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1320_, v_l_1321_, v_r_1322_);
lean_dec_ref(v_r_1322_);
lean_dec_ref(v_l_1321_);
lean_dec(v_w_1320_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1334_, lean_object* v_x_1335_){
_start:
{
switch(lean_obj_tag(v_x_1335_))
{
case 0:
{
lean_object* v_idx_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_w_1334_);
v_idx_1336_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_idx_1336_);
lean_dec_ref_known(v_x_1335_, 2);
v___x_1337_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1338_ = l_Nat_reprFast(v_idx_1336_);
v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
lean_dec_ref(v___x_1338_);
return v___x_1339_;
}
case 1:
{
lean_object* v_val_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_val_1340_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_x_1335_, 2);
v___x_1341_ = l_BitVec_repr(v_w_1334_, v_val_1340_);
v___x_1342_ = l_Std_Format_defWidth;
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = l_Std_Format_pretty(v___x_1341_, v___x_1342_, v___x_1343_, v___x_1343_);
return v___x_1344_;
}
case 2:
{
lean_object* v_w_1345_; lean_object* v_start_1346_; lean_object* v_expr_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_w_1345_ = lean_ctor_get(v_x_1335_, 0);
lean_inc(v_w_1345_);
v_start_1346_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_start_1346_);
v_expr_1347_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_expr_1347_);
lean_dec_ref_known(v_x_1335_, 4);
v___x_1348_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1345_, v_expr_1347_);
v___x_1349_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
v___x_1351_ = l_Nat_reprFast(v_start_1346_);
v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
lean_dec_ref(v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
v___x_1355_ = l_Nat_reprFast(v_w_1334_);
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
return v___x_1358_;
}
case 3:
{
lean_object* v_lhs_1359_; uint8_t v_op_1360_; lean_object* v_rhs_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_lhs_1359_ = lean_ctor_get(v_x_1335_, 1);
lean_inc_ref(v_lhs_1359_);
v_op_1360_ = lean_ctor_get_uint8(v_x_1335_, sizeof(void*)*3 + 8);
v_rhs_1361_ = lean_ctor_get(v_x_1335_, 2);
lean_inc_ref(v_rhs_1361_);
lean_dec_ref_known(v_x_1335_, 3);
v___x_1362_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1334_);
v___x_1363_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_lhs_1359_);
v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
v___x_1367_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1360_);
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1368_, v___x_1365_);
v___x_1370_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_rhs_1361_);
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
return v___x_1373_;
}
case 4:
{
lean_object* v_op_1374_; lean_object* v_operand_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_op_1374_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_op_1374_);
v_operand_1375_ = lean_ctor_get(v_x_1335_, 2);
lean_inc_ref(v_operand_1375_);
lean_dec_ref_known(v_x_1335_, 3);
v___x_1376_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1377_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1374_);
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1380_ = lean_string_append(v___x_1378_, v___x_1379_);
v___x_1381_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_operand_1375_);
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
return v___x_1384_;
}
case 5:
{
lean_object* v_l_1385_; lean_object* v_r_1386_; lean_object* v_lhs_1387_; lean_object* v_rhs_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_w_1334_);
v_l_1385_ = lean_ctor_get(v_x_1335_, 0);
lean_inc(v_l_1385_);
v_r_1386_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_r_1386_);
v_lhs_1387_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_lhs_1387_);
v_rhs_1388_ = lean_ctor_get(v_x_1335_, 4);
lean_inc_ref(v_rhs_1388_);
lean_dec_ref_known(v_x_1335_, 5);
v___x_1389_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1390_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1385_, v_lhs_1387_);
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
v___x_1394_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1386_, v_rhs_1388_);
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
return v___x_1397_;
}
case 6:
{
lean_object* v_w_1398_; lean_object* v_n_1399_; lean_object* v_expr_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v_w_1334_);
v_w_1398_ = lean_ctor_get(v_x_1335_, 0);
lean_inc(v_w_1398_);
v_n_1399_ = lean_ctor_get(v_x_1335_, 2);
lean_inc(v_n_1399_);
v_expr_1400_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_expr_1400_);
lean_dec_ref_known(v_x_1335_, 4);
v___x_1401_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1402_ = l_Nat_reprFast(v_n_1399_);
v___x_1403_ = lean_string_append(v___x_1401_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1398_, v_expr_1400_);
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
return v___x_1409_;
}
case 7:
{
lean_object* v_n_1410_; lean_object* v_lhs_1411_; lean_object* v_rhs_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_n_1410_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_n_1410_);
v_lhs_1411_ = lean_ctor_get(v_x_1335_, 2);
lean_inc_ref(v_lhs_1411_);
v_rhs_1412_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_rhs_1412_);
lean_dec_ref_known(v_x_1335_, 4);
v___x_1413_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1414_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_lhs_1411_);
v___x_1415_ = lean_string_append(v___x_1413_, v___x_1414_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
v___x_1418_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1410_, v_rhs_1412_);
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
return v___x_1421_;
}
case 8:
{
lean_object* v_n_1422_; lean_object* v_lhs_1423_; lean_object* v_rhs_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_n_1422_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_n_1422_);
v_lhs_1423_ = lean_ctor_get(v_x_1335_, 2);
lean_inc_ref(v_lhs_1423_);
v_rhs_1424_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_rhs_1424_);
lean_dec_ref_known(v_x_1335_, 4);
v___x_1425_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1426_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_lhs_1423_);
v___x_1427_ = lean_string_append(v___x_1425_, v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1429_ = lean_string_append(v___x_1427_, v___x_1428_);
v___x_1430_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1422_, v_rhs_1424_);
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1433_ = lean_string_append(v___x_1431_, v___x_1432_);
return v___x_1433_;
}
default: 
{
lean_object* v_n_1434_; lean_object* v_lhs_1435_; lean_object* v_rhs_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_n_1434_ = lean_ctor_get(v_x_1335_, 1);
lean_inc(v_n_1434_);
v_lhs_1435_ = lean_ctor_get(v_x_1335_, 2);
lean_inc_ref(v_lhs_1435_);
v_rhs_1436_ = lean_ctor_get(v_x_1335_, 3);
lean_inc_ref(v_rhs_1436_);
lean_dec_ref_known(v_x_1335_, 4);
v___x_1437_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1438_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1334_, v_lhs_1435_);
v___x_1439_ = lean_string_append(v___x_1437_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1441_ = lean_string_append(v___x_1439_, v___x_1440_);
v___x_1442_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1434_, v_rhs_1436_);
v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1447_, 0, v_w_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1448_, lean_object* v_idx_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_RArray_getImpl___redArg(v_assign_1448_, v_idx_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1451_, lean_object* v_idx_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1451_, v_idx_1452_);
lean_dec(v_idx_1452_);
lean_dec_ref(v_assign_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1454_, lean_object* v_assign_1455_, lean_object* v_x_1456_){
_start:
{
switch(lean_obj_tag(v_x_1456_))
{
case 0:
{
lean_object* v_idx_1457_; lean_object* v_packedBv_1458_; lean_object* v_w_1459_; lean_object* v_bv_1460_; uint8_t v___x_1461_; 
v_idx_1457_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_idx_1457_);
lean_dec_ref_known(v_x_1456_, 2);
v_packedBv_1458_ = l_Lean_RArray_getImpl___redArg(v_assign_1455_, v_idx_1457_);
lean_dec(v_idx_1457_);
v_w_1459_ = lean_ctor_get(v_packedBv_1458_, 0);
lean_inc(v_w_1459_);
v_bv_1460_ = lean_ctor_get(v_packedBv_1458_, 1);
lean_inc(v_bv_1460_);
lean_dec(v_packedBv_1458_);
v___x_1461_ = lean_nat_dec_eq(v_w_1459_, v_w_1454_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = l_BitVec_setWidth(v_w_1459_, v_w_1454_, v_bv_1460_);
lean_dec(v_bv_1460_);
lean_dec(v_w_1454_);
lean_dec(v_w_1459_);
return v___x_1462_;
}
else
{
lean_dec(v_w_1459_);
lean_dec(v_w_1454_);
return v_bv_1460_;
}
}
case 1:
{
lean_object* v_val_1463_; 
lean_dec(v_w_1454_);
v_val_1463_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_x_1456_, 2);
return v_val_1463_;
}
case 2:
{
lean_object* v_w_1464_; lean_object* v_start_1465_; lean_object* v_expr_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_w_1464_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_w_1464_);
v_start_1465_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_start_1465_);
v_expr_1466_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_expr_1466_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1467_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1464_, v_assign_1455_, v_expr_1466_);
v___x_1468_ = l_BitVec_extractLsb_x27___redArg(v_start_1465_, v_w_1454_, v___x_1467_);
lean_dec(v___x_1467_);
lean_dec(v_w_1454_);
lean_dec(v_start_1465_);
return v___x_1468_;
}
case 3:
{
lean_object* v_lhs_1469_; uint8_t v_op_1470_; lean_object* v_rhs_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_lhs_1469_ = lean_ctor_get(v_x_1456_, 1);
lean_inc_ref(v_lhs_1469_);
v_op_1470_ = lean_ctor_get_uint8(v_x_1456_, sizeof(void*)*3 + 8);
v_rhs_1471_ = lean_ctor_get(v_x_1456_, 2);
lean_inc_ref(v_rhs_1471_);
lean_dec_ref_known(v_x_1456_, 3);
lean_inc_n(v_w_1454_, 2);
v___x_1472_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_lhs_1469_);
v___x_1473_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_rhs_1471_);
v___x_1474_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1454_, v_op_1470_, v___x_1472_, v___x_1473_);
lean_dec(v___x_1473_);
lean_dec(v___x_1472_);
lean_dec(v_w_1454_);
return v___x_1474_;
}
case 4:
{
lean_object* v_op_1475_; lean_object* v_operand_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_op_1475_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_op_1475_);
v_operand_1476_ = lean_ctor_get(v_x_1456_, 2);
lean_inc_ref(v_operand_1476_);
lean_dec_ref_known(v_x_1456_, 3);
lean_inc(v_w_1454_);
v___x_1477_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_operand_1476_);
v___x_1478_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1454_, v_op_1475_, v___x_1477_);
lean_dec(v_op_1475_);
return v___x_1478_;
}
case 5:
{
lean_object* v_l_1479_; lean_object* v_r_1480_; lean_object* v_lhs_1481_; lean_object* v_rhs_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v_w_1454_);
v_l_1479_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_l_1479_);
v_r_1480_ = lean_ctor_get(v_x_1456_, 1);
lean_inc_n(v_r_1480_, 2);
v_lhs_1481_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_lhs_1481_);
v_rhs_1482_ = lean_ctor_get(v_x_1456_, 4);
lean_inc_ref(v_rhs_1482_);
lean_dec_ref_known(v_x_1456_, 5);
v___x_1483_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1479_, v_assign_1455_, v_lhs_1481_);
v___x_1484_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1480_, v_assign_1455_, v_rhs_1482_);
v___x_1485_ = l_BitVec_append___redArg(v_r_1480_, v___x_1483_, v___x_1484_);
lean_dec(v___x_1484_);
lean_dec(v___x_1483_);
lean_dec(v_r_1480_);
return v___x_1485_;
}
case 6:
{
lean_object* v_w_1486_; lean_object* v_n_1487_; lean_object* v_expr_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec(v_w_1454_);
v_w_1486_ = lean_ctor_get(v_x_1456_, 0);
lean_inc_n(v_w_1486_, 2);
v_n_1487_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_n_1487_);
v_expr_1488_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_expr_1488_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1489_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1486_, v_assign_1455_, v_expr_1488_);
v___x_1490_ = l_BitVec_replicate(v_w_1486_, v_n_1487_, v___x_1489_);
lean_dec(v___x_1489_);
lean_dec(v_n_1487_);
lean_dec(v_w_1486_);
return v___x_1490_;
}
case 7:
{
lean_object* v_n_1491_; lean_object* v_lhs_1492_; lean_object* v_rhs_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_n_1491_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_n_1491_);
v_lhs_1492_ = lean_ctor_get(v_x_1456_, 2);
lean_inc_ref(v_lhs_1492_);
v_rhs_1493_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_rhs_1493_);
lean_dec_ref_known(v_x_1456_, 4);
lean_inc(v_w_1454_);
v___x_1494_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_lhs_1492_);
v___x_1495_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1491_, v_assign_1455_, v_rhs_1493_);
v___x_1496_ = l_BitVec_shiftLeft(v_w_1454_, v___x_1494_, v___x_1495_);
lean_dec(v___x_1495_);
lean_dec(v___x_1494_);
lean_dec(v_w_1454_);
return v___x_1496_;
}
case 8:
{
lean_object* v_n_1497_; lean_object* v_lhs_1498_; lean_object* v_rhs_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_n_1497_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_n_1497_);
v_lhs_1498_ = lean_ctor_get(v_x_1456_, 2);
lean_inc_ref(v_lhs_1498_);
v_rhs_1499_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_rhs_1499_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1500_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_lhs_1498_);
v___x_1501_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1497_, v_assign_1455_, v_rhs_1499_);
v___x_1502_ = lean_nat_shiftr(v___x_1500_, v___x_1501_);
lean_dec(v___x_1501_);
lean_dec(v___x_1500_);
return v___x_1502_;
}
default: 
{
lean_object* v_n_1503_; lean_object* v_lhs_1504_; lean_object* v_rhs_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_n_1503_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_n_1503_);
v_lhs_1504_ = lean_ctor_get(v_x_1456_, 2);
lean_inc_ref(v_lhs_1504_);
v_rhs_1505_ = lean_ctor_get(v_x_1456_, 3);
lean_inc_ref(v_rhs_1505_);
lean_dec_ref_known(v_x_1456_, 4);
lean_inc(v_w_1454_);
v___x_1506_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1455_, v_lhs_1504_);
v___x_1507_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1503_, v_assign_1455_, v_rhs_1505_);
v___x_1508_ = l_BitVec_sshiftRight(v_w_1454_, v___x_1506_, v___x_1507_);
lean_dec(v___x_1507_);
lean_dec(v_w_1454_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1509_, lean_object* v_assign_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1509_, v_assign_1510_, v_x_1511_);
lean_dec_ref(v_assign_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* v_w_1513_, lean_object* v_x_1514_, lean_object* v_h__1_1515_, lean_object* v_h__2_1516_, lean_object* v_h__3_1517_, lean_object* v_h__4_1518_, lean_object* v_h__5_1519_, lean_object* v_h__6_1520_, lean_object* v_h__7_1521_, lean_object* v_h__8_1522_, lean_object* v_h__9_1523_, lean_object* v_h__10_1524_){
_start:
{
switch(lean_obj_tag(v_x_1514_))
{
case 0:
{
lean_object* v_idx_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
v_idx_1525_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_idx_1525_);
lean_dec_ref_known(v_x_1514_, 2);
v___x_1526_ = lean_apply_2(v_h__1_1515_, v_w_1513_, v_idx_1525_);
return v___x_1526_;
}
case 1:
{
lean_object* v_val_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__1_1515_);
v_val_1527_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_val_1527_);
lean_dec_ref_known(v_x_1514_, 2);
v___x_1528_ = lean_apply_2(v_h__2_1516_, v_w_1513_, v_val_1527_);
return v___x_1528_;
}
case 2:
{
lean_object* v_w_1529_; lean_object* v_start_1530_; lean_object* v_expr_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_w_1529_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_w_1529_);
v_start_1530_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_start_1530_);
v_expr_1531_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_expr_1531_);
lean_dec_ref_known(v_x_1514_, 4);
v___x_1532_ = lean_apply_4(v_h__3_1517_, v_w_1513_, v_w_1529_, v_start_1530_, v_expr_1531_);
return v___x_1532_;
}
case 3:
{
lean_object* v_lhs_1533_; uint8_t v_op_1534_; lean_object* v_rhs_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_lhs_1533_ = lean_ctor_get(v_x_1514_, 1);
lean_inc_ref(v_lhs_1533_);
v_op_1534_ = lean_ctor_get_uint8(v_x_1514_, sizeof(void*)*3 + 8);
v_rhs_1535_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_rhs_1535_);
lean_dec_ref_known(v_x_1514_, 3);
v___x_1536_ = lean_box(v_op_1534_);
v___x_1537_ = lean_apply_4(v_h__4_1518_, v_w_1513_, v_lhs_1533_, v___x_1536_, v_rhs_1535_);
return v___x_1537_;
}
case 4:
{
lean_object* v_op_1538_; lean_object* v_operand_1539_; lean_object* v___x_1540_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_op_1538_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_op_1538_);
v_operand_1539_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_operand_1539_);
lean_dec_ref_known(v_x_1514_, 3);
v___x_1540_ = lean_apply_3(v_h__5_1519_, v_w_1513_, v_op_1538_, v_operand_1539_);
return v___x_1540_;
}
case 5:
{
lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v_lhs_1543_; lean_object* v_rhs_1544_; lean_object* v___x_1545_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_l_1541_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_l_1541_);
v_r_1542_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_r_1542_);
v_lhs_1543_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_lhs_1543_);
v_rhs_1544_ = lean_ctor_get(v_x_1514_, 4);
lean_inc_ref(v_rhs_1544_);
lean_dec_ref_known(v_x_1514_, 5);
v___x_1545_ = lean_apply_6(v_h__6_1520_, v_w_1513_, v_l_1541_, v_r_1542_, v_lhs_1543_, v_rhs_1544_, lean_box(0));
return v___x_1545_;
}
case 6:
{
lean_object* v_w_1546_; lean_object* v_n_1547_; lean_object* v_expr_1548_; lean_object* v___x_1549_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_w_1546_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_w_1546_);
v_n_1547_ = lean_ctor_get(v_x_1514_, 2);
lean_inc(v_n_1547_);
v_expr_1548_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_expr_1548_);
lean_dec_ref_known(v_x_1514_, 4);
v___x_1549_ = lean_apply_5(v_h__7_1521_, v_w_1513_, v_w_1546_, v_n_1547_, v_expr_1548_, lean_box(0));
return v___x_1549_;
}
case 7:
{
lean_object* v_n_1550_; lean_object* v_lhs_1551_; lean_object* v_rhs_1552_; lean_object* v___x_1553_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__9_1523_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_n_1550_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_n_1550_);
v_lhs_1551_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_lhs_1551_);
v_rhs_1552_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_rhs_1552_);
lean_dec_ref_known(v_x_1514_, 4);
v___x_1553_ = lean_apply_4(v_h__8_1522_, v_w_1513_, v_n_1550_, v_lhs_1551_, v_rhs_1552_);
return v___x_1553_;
}
case 8:
{
lean_object* v_n_1554_; lean_object* v_lhs_1555_; lean_object* v_rhs_1556_; lean_object* v___x_1557_; 
lean_dec(v_h__10_1524_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_n_1554_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_n_1554_);
v_lhs_1555_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_lhs_1555_);
v_rhs_1556_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_rhs_1556_);
lean_dec_ref_known(v_x_1514_, 4);
v___x_1557_ = lean_apply_4(v_h__9_1523_, v_w_1513_, v_n_1554_, v_lhs_1555_, v_rhs_1556_);
return v___x_1557_;
}
default: 
{
lean_object* v_n_1558_; lean_object* v_lhs_1559_; lean_object* v_rhs_1560_; lean_object* v___x_1561_; 
lean_dec(v_h__9_1523_);
lean_dec(v_h__8_1522_);
lean_dec(v_h__7_1521_);
lean_dec(v_h__6_1520_);
lean_dec(v_h__5_1519_);
lean_dec(v_h__4_1518_);
lean_dec(v_h__3_1517_);
lean_dec(v_h__2_1516_);
lean_dec(v_h__1_1515_);
v_n_1558_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_n_1558_);
v_lhs_1559_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_lhs_1559_);
v_rhs_1560_ = lean_ctor_get(v_x_1514_, 3);
lean_inc_ref(v_rhs_1560_);
lean_dec_ref_known(v_x_1514_, 4);
v___x_1561_ = lean_apply_4(v_h__10_1524_, v_w_1513_, v_n_1558_, v_lhs_1559_, v_rhs_1560_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* v_motive_1562_, lean_object* v_w_1563_, lean_object* v_x_1564_, lean_object* v_h__1_1565_, lean_object* v_h__2_1566_, lean_object* v_h__3_1567_, lean_object* v_h__4_1568_, lean_object* v_h__5_1569_, lean_object* v_h__6_1570_, lean_object* v_h__7_1571_, lean_object* v_h__8_1572_, lean_object* v_h__9_1573_, lean_object* v_h__10_1574_){
_start:
{
switch(lean_obj_tag(v_x_1564_))
{
case 0:
{
lean_object* v_idx_1575_; lean_object* v___x_1576_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
v_idx_1575_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_idx_1575_);
lean_dec_ref_known(v_x_1564_, 2);
v___x_1576_ = lean_apply_2(v_h__1_1565_, v_w_1563_, v_idx_1575_);
return v___x_1576_;
}
case 1:
{
lean_object* v_val_1577_; lean_object* v___x_1578_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__1_1565_);
v_val_1577_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_val_1577_);
lean_dec_ref_known(v_x_1564_, 2);
v___x_1578_ = lean_apply_2(v_h__2_1566_, v_w_1563_, v_val_1577_);
return v___x_1578_;
}
case 2:
{
lean_object* v_w_1579_; lean_object* v_start_1580_; lean_object* v_expr_1581_; lean_object* v___x_1582_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_w_1579_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_w_1579_);
v_start_1580_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_start_1580_);
v_expr_1581_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_expr_1581_);
lean_dec_ref_known(v_x_1564_, 4);
v___x_1582_ = lean_apply_4(v_h__3_1567_, v_w_1563_, v_w_1579_, v_start_1580_, v_expr_1581_);
return v___x_1582_;
}
case 3:
{
lean_object* v_lhs_1583_; uint8_t v_op_1584_; lean_object* v_rhs_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_lhs_1583_ = lean_ctor_get(v_x_1564_, 1);
lean_inc_ref(v_lhs_1583_);
v_op_1584_ = lean_ctor_get_uint8(v_x_1564_, sizeof(void*)*3 + 8);
v_rhs_1585_ = lean_ctor_get(v_x_1564_, 2);
lean_inc_ref(v_rhs_1585_);
lean_dec_ref_known(v_x_1564_, 3);
v___x_1586_ = lean_box(v_op_1584_);
v___x_1587_ = lean_apply_4(v_h__4_1568_, v_w_1563_, v_lhs_1583_, v___x_1586_, v_rhs_1585_);
return v___x_1587_;
}
case 4:
{
lean_object* v_op_1588_; lean_object* v_operand_1589_; lean_object* v___x_1590_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_op_1588_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_op_1588_);
v_operand_1589_ = lean_ctor_get(v_x_1564_, 2);
lean_inc_ref(v_operand_1589_);
lean_dec_ref_known(v_x_1564_, 3);
v___x_1590_ = lean_apply_3(v_h__5_1569_, v_w_1563_, v_op_1588_, v_operand_1589_);
return v___x_1590_;
}
case 5:
{
lean_object* v_l_1591_; lean_object* v_r_1592_; lean_object* v_lhs_1593_; lean_object* v_rhs_1594_; lean_object* v___x_1595_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_l_1591_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_l_1591_);
v_r_1592_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_r_1592_);
v_lhs_1593_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_lhs_1593_);
v_rhs_1594_ = lean_ctor_get(v_x_1564_, 4);
lean_inc_ref(v_rhs_1594_);
lean_dec_ref_known(v_x_1564_, 5);
v___x_1595_ = lean_apply_6(v_h__6_1570_, v_w_1563_, v_l_1591_, v_r_1592_, v_lhs_1593_, v_rhs_1594_, lean_box(0));
return v___x_1595_;
}
case 6:
{
lean_object* v_w_1596_; lean_object* v_n_1597_; lean_object* v_expr_1598_; lean_object* v___x_1599_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_w_1596_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_w_1596_);
v_n_1597_ = lean_ctor_get(v_x_1564_, 2);
lean_inc(v_n_1597_);
v_expr_1598_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_expr_1598_);
lean_dec_ref_known(v_x_1564_, 4);
v___x_1599_ = lean_apply_5(v_h__7_1571_, v_w_1563_, v_w_1596_, v_n_1597_, v_expr_1598_, lean_box(0));
return v___x_1599_;
}
case 7:
{
lean_object* v_n_1600_; lean_object* v_lhs_1601_; lean_object* v_rhs_1602_; lean_object* v___x_1603_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__9_1573_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_n_1600_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_n_1600_);
v_lhs_1601_ = lean_ctor_get(v_x_1564_, 2);
lean_inc_ref(v_lhs_1601_);
v_rhs_1602_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_rhs_1602_);
lean_dec_ref_known(v_x_1564_, 4);
v___x_1603_ = lean_apply_4(v_h__8_1572_, v_w_1563_, v_n_1600_, v_lhs_1601_, v_rhs_1602_);
return v___x_1603_;
}
case 8:
{
lean_object* v_n_1604_; lean_object* v_lhs_1605_; lean_object* v_rhs_1606_; lean_object* v___x_1607_; 
lean_dec(v_h__10_1574_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_n_1604_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_n_1604_);
v_lhs_1605_ = lean_ctor_get(v_x_1564_, 2);
lean_inc_ref(v_lhs_1605_);
v_rhs_1606_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_rhs_1606_);
lean_dec_ref_known(v_x_1564_, 4);
v___x_1607_ = lean_apply_4(v_h__9_1573_, v_w_1563_, v_n_1604_, v_lhs_1605_, v_rhs_1606_);
return v___x_1607_;
}
default: 
{
lean_object* v_n_1608_; lean_object* v_lhs_1609_; lean_object* v_rhs_1610_; lean_object* v___x_1611_; 
lean_dec(v_h__9_1573_);
lean_dec(v_h__8_1572_);
lean_dec(v_h__7_1571_);
lean_dec(v_h__6_1570_);
lean_dec(v_h__5_1569_);
lean_dec(v_h__4_1568_);
lean_dec(v_h__3_1567_);
lean_dec(v_h__2_1566_);
lean_dec(v_h__1_1565_);
v_n_1608_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_n_1608_);
v_lhs_1609_ = lean_ctor_get(v_x_1564_, 2);
lean_inc_ref(v_lhs_1609_);
v_rhs_1610_ = lean_ctor_get(v_x_1564_, 3);
lean_inc_ref(v_rhs_1610_);
lean_dec_ref_known(v_x_1564_, 4);
v___x_1611_ = lean_apply_4(v_h__10_1574_, v_w_1563_, v_n_1608_, v_lhs_1609_, v_rhs_1610_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t v_x_1612_){
_start:
{
if (v_x_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_unsigned_to_nat(1u);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object* v_x_1615_){
_start:
{
uint8_t v_x_boxed_1616_; lean_object* v_res_1617_; 
v_x_boxed_1616_ = lean_unbox(v_x_1615_);
v_res_1617_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_boxed_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1618_){
_start:
{
lean_inc(v_k_1618_);
return v_k_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1619_);
lean_dec(v_k_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1621_, lean_object* v_ctorIdx_1622_, uint8_t v_t_1623_, lean_object* v_h_1624_, lean_object* v_k_1625_){
_start:
{
lean_inc(v_k_1625_);
return v_k_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1626_, lean_object* v_ctorIdx_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_k_1630_){
_start:
{
uint8_t v_t_boxed_1631_; lean_object* v_res_1632_; 
v_t_boxed_1631_ = lean_unbox(v_t_1628_);
v_res_1632_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1626_, v_ctorIdx_1627_, v_t_boxed_1631_, v_h_1629_, v_k_1630_);
lean_dec(v_k_1630_);
lean_dec(v_ctorIdx_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1633_){
_start:
{
lean_inc(v_eq_1633_);
return v_eq_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1634_);
lean_dec(v_eq_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1636_, uint8_t v_t_1637_, lean_object* v_h_1638_, lean_object* v_eq_1639_){
_start:
{
lean_inc(v_eq_1639_);
return v_eq_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1640_, lean_object* v_t_1641_, lean_object* v_h_1642_, lean_object* v_eq_1643_){
_start:
{
uint8_t v_t_boxed_1644_; lean_object* v_res_1645_; 
v_t_boxed_1644_ = lean_unbox(v_t_1641_);
v_res_1645_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1640_, v_t_boxed_1644_, v_h_1642_, v_eq_1643_);
lean_dec(v_eq_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1646_){
_start:
{
lean_inc(v_ult_1646_);
return v_ult_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1647_);
lean_dec(v_ult_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1649_, uint8_t v_t_1650_, lean_object* v_h_1651_, lean_object* v_ult_1652_){
_start:
{
lean_inc(v_ult_1652_);
return v_ult_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1653_, lean_object* v_t_1654_, lean_object* v_h_1655_, lean_object* v_ult_1656_){
_start:
{
uint8_t v_t_boxed_1657_; lean_object* v_res_1658_; 
v_t_boxed_1657_ = lean_unbox(v_t_1654_);
v_res_1658_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1653_, v_t_boxed_1657_, v_h_1655_, v_ult_1656_);
lean_dec(v_ult_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1661_){
_start:
{
if (v_x_1661_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1664_){
_start:
{
uint8_t v_x_22__boxed_1665_; lean_object* v_res_1666_; 
v_x_22__boxed_1665_ = lean_unbox(v_x_1664_);
v_res_1666_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
if (v_x_1669_ == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_eq(v_a_1670_, v_a_1671_);
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_lt(v_a_1670_, v_a_1671_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
uint8_t v_x_101__boxed_1677_; uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_x_101__boxed_1677_ = lean_unbox(v_x_1674_);
v_res_1678_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_101__boxed_1677_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec(v_a_1675_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1680_, uint8_t v_x_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1681_, v_a_1682_, v_a_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1685_, lean_object* v_x_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
uint8_t v_x_114__boxed_1689_; uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_x_114__boxed_1689_ = lean_unbox(v_x_1686_);
v_res_1690_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1685_, v_x_114__boxed_1689_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec(v_w_1685_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx(v_x_1695_);
lean_dec_ref(v_x_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1697_, lean_object* v_k_1698_){
_start:
{
if (lean_obj_tag(v_t_1697_) == 0)
{
lean_object* v_w_1699_; lean_object* v_lhs_1700_; uint8_t v_op_1701_; lean_object* v_rhs_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_w_1699_ = lean_ctor_get(v_t_1697_, 0);
lean_inc(v_w_1699_);
v_lhs_1700_ = lean_ctor_get(v_t_1697_, 1);
lean_inc_ref(v_lhs_1700_);
v_op_1701_ = lean_ctor_get_uint8(v_t_1697_, sizeof(void*)*3);
v_rhs_1702_ = lean_ctor_get(v_t_1697_, 2);
lean_inc_ref(v_rhs_1702_);
lean_dec_ref_known(v_t_1697_, 3);
v___x_1703_ = lean_box(v_op_1701_);
v___x_1704_ = lean_apply_4(v_k_1698_, v_w_1699_, v_lhs_1700_, v___x_1703_, v_rhs_1702_);
return v___x_1704_;
}
else
{
lean_object* v_w_1705_; lean_object* v_expr_1706_; lean_object* v_idx_1707_; lean_object* v___x_1708_; 
v_w_1705_ = lean_ctor_get(v_t_1697_, 0);
lean_inc(v_w_1705_);
v_expr_1706_ = lean_ctor_get(v_t_1697_, 1);
lean_inc_ref(v_expr_1706_);
v_idx_1707_ = lean_ctor_get(v_t_1697_, 2);
lean_inc(v_idx_1707_);
lean_dec_ref_known(v_t_1697_, 3);
v___x_1708_ = lean_apply_3(v_k_1698_, v_w_1705_, v_expr_1706_, v_idx_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1709_, lean_object* v_ctorIdx_1710_, lean_object* v_t_1711_, lean_object* v_h_1712_, lean_object* v_k_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1711_, v_k_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1715_, lean_object* v_ctorIdx_1716_, lean_object* v_t_1717_, lean_object* v_h_1718_, lean_object* v_k_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1715_, v_ctorIdx_1716_, v_t_1717_, v_h_1718_, v_k_1719_);
lean_dec(v_ctorIdx_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1721_, lean_object* v_bin_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1721_, v_bin_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1724_, lean_object* v_t_1725_, lean_object* v_h_1726_, lean_object* v_bin_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1725_, v_bin_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1729_, lean_object* v_getLsbD_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1729_, v_getLsbD_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1732_, lean_object* v_t_1733_, lean_object* v_h_1734_, lean_object* v_getLsbD_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1733_, v_getLsbD_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
lean_object* v_w_1738_; lean_object* v_lhs_1739_; uint8_t v_op_1740_; lean_object* v_rhs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_w_1738_ = lean_ctor_get(v_x_1737_, 0);
lean_inc_n(v_w_1738_, 2);
v_lhs_1739_ = lean_ctor_get(v_x_1737_, 1);
lean_inc_ref(v_lhs_1739_);
v_op_1740_ = lean_ctor_get_uint8(v_x_1737_, sizeof(void*)*3);
v_rhs_1741_ = lean_ctor_get(v_x_1737_, 2);
lean_inc_ref(v_rhs_1741_);
lean_dec_ref_known(v_x_1737_, 3);
v___x_1742_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1743_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1738_, v_lhs_1739_);
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
v___x_1747_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1740_);
v___x_1748_ = lean_string_append(v___x_1746_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = lean_string_append(v___x_1748_, v___x_1745_);
v___x_1750_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1738_, v_rhs_1741_);
v___x_1751_ = lean_string_append(v___x_1749_, v___x_1750_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1753_ = lean_string_append(v___x_1751_, v___x_1752_);
return v___x_1753_;
}
else
{
lean_object* v_w_1754_; lean_object* v_expr_1755_; lean_object* v_idx_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_w_1754_ = lean_ctor_get(v_x_1737_, 0);
lean_inc(v_w_1754_);
v_expr_1755_ = lean_ctor_get(v_x_1737_, 1);
lean_inc_ref(v_expr_1755_);
v_idx_1756_ = lean_ctor_get(v_x_1737_, 2);
lean_inc(v_idx_1756_);
lean_dec_ref_known(v_x_1737_, 3);
v___x_1757_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1754_, v_expr_1755_);
v___x_1758_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1759_ = lean_string_append(v___x_1757_, v___x_1758_);
v___x_1760_ = l_Nat_reprFast(v_idx_1756_);
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
return v___x_1763_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
lean_object* v_w_1768_; lean_object* v_lhs_1769_; uint8_t v_op_1770_; lean_object* v_rhs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_w_1768_ = lean_ctor_get(v_x_1767_, 0);
lean_inc_n(v_w_1768_, 2);
v_lhs_1769_ = lean_ctor_get(v_x_1767_, 1);
lean_inc_ref(v_lhs_1769_);
v_op_1770_ = lean_ctor_get_uint8(v_x_1767_, sizeof(void*)*3);
v_rhs_1771_ = lean_ctor_get(v_x_1767_, 2);
lean_inc_ref(v_rhs_1771_);
lean_dec_ref_known(v_x_1767_, 3);
v___x_1772_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1768_, v_assign_1766_, v_lhs_1769_);
v___x_1773_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1768_, v_assign_1766_, v_rhs_1771_);
v___x_1774_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1770_, v___x_1772_, v___x_1773_);
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
return v___x_1774_;
}
else
{
lean_object* v_w_1775_; lean_object* v_expr_1776_; lean_object* v_idx_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_w_1775_ = lean_ctor_get(v_x_1767_, 0);
lean_inc(v_w_1775_);
v_expr_1776_ = lean_ctor_get(v_x_1767_, 1);
lean_inc_ref(v_expr_1776_);
v_idx_1777_ = lean_ctor_get(v_x_1767_, 2);
lean_inc(v_idx_1777_);
lean_dec_ref_known(v_x_1767_, 3);
v___x_1778_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1775_, v_assign_1766_, v_expr_1776_);
v___x_1779_ = l_Nat_testBit(v___x_1778_, v_idx_1777_);
lean_dec(v_idx_1777_);
lean_dec(v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1780_, lean_object* v_x_1781_){
_start:
{
uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_res_1782_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1780_, v_x_1781_);
lean_dec_ref(v_assign_1780_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1784_, lean_object* v_x_1785_){
_start:
{
uint8_t v___x_1786_; 
v___x_1786_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1787_, lean_object* v_x_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1787_, v_x_1788_);
lean_dec_ref(v_assign_1787_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1791_, lean_object* v_expr_1792_){
_start:
{
lean_object* v___f_1793_; uint8_t v___x_1794_; 
v___f_1793_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1793_, 0, v_assign_1791_);
v___x_1794_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1793_, v_expr_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1795_, lean_object* v_expr_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1795_, v_expr_1796_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
