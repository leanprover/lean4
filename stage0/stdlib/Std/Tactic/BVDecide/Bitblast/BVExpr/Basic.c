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
static lean_once_cell_t l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object*);
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
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_nat_mod(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0, &l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_once, _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1, &l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1_once, _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(uint8_t v_x_152_){
_start:
{
switch(v_x_152_)
{
case 0:
{
lean_object* v___x_153_; 
v___x_153_ = lean_unsigned_to_nat(0u);
return v___x_153_;
}
case 1:
{
lean_object* v___x_154_; 
v___x_154_ = lean_unsigned_to_nat(1u);
return v___x_154_;
}
case 2:
{
lean_object* v___x_155_; 
v___x_155_ = lean_unsigned_to_nat(2u);
return v___x_155_;
}
case 3:
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(3u);
return v___x_156_;
}
case 4:
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(4u);
return v___x_157_;
}
case 5:
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(5u);
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; 
v___x_159_ = lean_unsigned_to_nat(6u);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_boxed_161_; lean_object* v_res_162_; 
v_x_boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t v_x_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object* v_x_165_){
_start:
{
uint8_t v_x_4__boxed_166_; lean_object* v_res_167_; 
v_x_4__boxed_166_ = lean_unbox(v_x_165_);
v_res_167_ = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(v_x_4__boxed_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* v_k_168_){
_start:
{
lean_inc(v_k_168_);
return v_k_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* v_k_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_169_);
lean_dec(v_k_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* v_motive_171_, lean_object* v_ctorIdx_172_, uint8_t v_t_173_, lean_object* v_h_174_, lean_object* v_k_175_){
_start:
{
lean_inc(v_k_175_);
return v_k_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
uint8_t v_t_boxed_181_; lean_object* v_res_182_; 
v_t_boxed_181_ = lean_unbox(v_t_178_);
v_res_182_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(v_motive_176_, v_ctorIdx_177_, v_t_boxed_181_, v_h_179_, v_k_180_);
lean_dec(v_k_180_);
lean_dec(v_ctorIdx_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object* v_and_183_){
_start:
{
lean_inc(v_and_183_);
return v_and_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object* v_and_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(v_and_184_);
lean_dec(v_and_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* v_motive_186_, uint8_t v_t_187_, lean_object* v_h_188_, lean_object* v_and_189_){
_start:
{
lean_inc(v_and_189_);
return v_and_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_and_193_){
_start:
{
uint8_t v_t_boxed_194_; lean_object* v_res_195_; 
v_t_boxed_194_ = lean_unbox(v_t_191_);
v_res_195_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(v_motive_190_, v_t_boxed_194_, v_h_192_, v_and_193_);
lean_dec(v_and_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* v_or_196_){
_start:
{
lean_inc(v_or_196_);
return v_or_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* v_or_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_197_);
lean_dec(v_or_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* v_motive_199_, uint8_t v_t_200_, lean_object* v_h_201_, lean_object* v_or_202_){
_start:
{
lean_inc(v_or_202_);
return v_or_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_or_206_){
_start:
{
uint8_t v_t_boxed_207_; lean_object* v_res_208_; 
v_t_boxed_207_ = lean_unbox(v_t_204_);
v_res_208_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(v_motive_203_, v_t_boxed_207_, v_h_205_, v_or_206_);
lean_dec(v_or_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* v_xor_209_){
_start:
{
lean_inc(v_xor_209_);
return v_xor_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* v_xor_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_210_);
lean_dec(v_xor_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* v_motive_212_, uint8_t v_t_213_, lean_object* v_h_214_, lean_object* v_xor_215_){
_start:
{
lean_inc(v_xor_215_);
return v_xor_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* v_motive_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_xor_219_){
_start:
{
uint8_t v_t_boxed_220_; lean_object* v_res_221_; 
v_t_boxed_220_ = lean_unbox(v_t_217_);
v_res_221_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(v_motive_216_, v_t_boxed_220_, v_h_218_, v_xor_219_);
lean_dec(v_xor_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* v_add_222_){
_start:
{
lean_inc(v_add_222_);
return v_add_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* v_add_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_223_);
lean_dec(v_add_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* v_motive_225_, uint8_t v_t_226_, lean_object* v_h_227_, lean_object* v_add_228_){
_start:
{
lean_inc(v_add_228_);
return v_add_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object* v_motive_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_add_232_){
_start:
{
uint8_t v_t_boxed_233_; lean_object* v_res_234_; 
v_t_boxed_233_ = lean_unbox(v_t_230_);
v_res_234_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(v_motive_229_, v_t_boxed_233_, v_h_231_, v_add_232_);
lean_dec(v_add_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object* v_mul_235_){
_start:
{
lean_inc(v_mul_235_);
return v_mul_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object* v_mul_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(v_mul_236_);
lean_dec(v_mul_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* v_motive_238_, uint8_t v_t_239_, lean_object* v_h_240_, lean_object* v_mul_241_){
_start:
{
lean_inc(v_mul_241_);
return v_mul_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_mul_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(v_motive_242_, v_t_boxed_246_, v_h_244_, v_mul_245_);
lean_dec(v_mul_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* v_udiv_248_){
_start:
{
lean_inc(v_udiv_248_);
return v_udiv_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* v_udiv_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_249_);
lean_dec(v_udiv_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_udiv_254_){
_start:
{
lean_inc(v_udiv_254_);
return v_udiv_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_udiv_258_){
_start:
{
uint8_t v_t_boxed_259_; lean_object* v_res_260_; 
v_t_boxed_259_ = lean_unbox(v_t_256_);
v_res_260_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(v_motive_255_, v_t_boxed_259_, v_h_257_, v_udiv_258_);
lean_dec(v_udiv_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* v_umod_261_){
_start:
{
lean_inc(v_umod_261_);
return v_umod_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* v_umod_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_262_);
lean_dec(v_umod_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* v_motive_264_, uint8_t v_t_265_, lean_object* v_h_266_, lean_object* v_umod_267_){
_start:
{
lean_inc(v_umod_267_);
return v_umod_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* v_motive_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_umod_271_){
_start:
{
uint8_t v_t_boxed_272_; lean_object* v_res_273_; 
v_t_boxed_272_ = lean_unbox(v_t_269_);
v_res_273_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(v_motive_268_, v_t_boxed_272_, v_h_270_, v_umod_271_);
lean_dec(v_umod_271_);
return v_res_273_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t v_x_274_){
_start:
{
switch(v_x_274_)
{
case 0:
{
uint64_t v___x_275_; 
v___x_275_ = 0ULL;
return v___x_275_;
}
case 1:
{
uint64_t v___x_276_; 
v___x_276_ = 1ULL;
return v___x_276_;
}
case 2:
{
uint64_t v___x_277_; 
v___x_277_ = 2ULL;
return v___x_277_;
}
case 3:
{
uint64_t v___x_278_; 
v___x_278_ = 3ULL;
return v___x_278_;
}
case 4:
{
uint64_t v___x_279_; 
v___x_279_ = 4ULL;
return v___x_279_;
}
case 5:
{
uint64_t v___x_280_; 
v___x_280_ = 5ULL;
return v___x_280_;
}
default: 
{
uint64_t v___x_281_; 
v___x_281_ = 6ULL;
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* v_x_282_){
_start:
{
uint8_t v_x_88__boxed_283_; uint64_t v_res_284_; lean_object* v_r_285_; 
v_x_88__boxed_283_ = lean_unbox(v_x_282_);
v_res_284_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_283_);
v_r_285_ = lean_box_uint64(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* v_n_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(2u);
v___x_290_ = lean_nat_dec_le(v_n_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(4u);
v___x_292_ = lean_nat_dec_le(v_n_288_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(5u);
v___x_294_ = lean_nat_dec_le(v_n_288_, v___x_293_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 6;
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = 5;
return v___x_296_;
}
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(3u);
v___x_298_ = lean_nat_dec_le(v_n_288_, v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 4;
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = 3;
return v___x_300_;
}
}
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_dec_le(v_n_288_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_dec_le(v_n_288_, v___x_303_);
if (v___x_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 2;
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 1;
return v___x_306_;
}
}
else
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* v_n_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_308_);
lean_dec(v_n_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t v_x_311_, uint8_t v_y_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_311_);
v___x_314_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_y_312_);
v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
lean_dec(v___x_314_);
lean_dec(v___x_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* v_x_316_, lean_object* v_y_317_){
_start:
{
uint8_t v_x_13__boxed_318_; uint8_t v_y_14__boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_x_13__boxed_318_ = lean_unbox(v_x_316_);
v_y_14__boxed_319_ = lean_unbox(v_y_317_);
v_res_320_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_13__boxed_318_, v_y_14__boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t v_x_329_){
_start:
{
switch(v_x_329_)
{
case 0:
{
lean_object* v___x_330_; 
v___x_330_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return v___x_330_;
}
case 1:
{
lean_object* v___x_331_; 
v___x_331_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return v___x_331_;
}
case 2:
{
lean_object* v___x_332_; 
v___x_332_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return v___x_332_;
}
case 3:
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return v___x_333_;
}
case 4:
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return v___x_334_;
}
case 5:
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return v___x_335_;
}
default: 
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* v_x_337_){
_start:
{
uint8_t v_x_67__boxed_338_; lean_object* v_res_339_; 
v_x_67__boxed_338_ = lean_unbox(v_x_337_);
v_res_339_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* v_w_342_, uint8_t v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
switch(v_x_343_)
{
case 0:
{
lean_object* v___x_346_; 
v___x_346_ = lean_nat_land(v_a_344_, v_a_345_);
return v___x_346_;
}
case 1:
{
lean_object* v___x_347_; 
v___x_347_ = lean_nat_lor(v_a_344_, v_a_345_);
return v___x_347_;
}
case 2:
{
lean_object* v___x_348_; 
v___x_348_ = lean_nat_lxor(v_a_344_, v_a_345_);
return v___x_348_;
}
case 3:
{
lean_object* v___x_349_; 
v___x_349_ = l_BitVec_add(v_w_342_, v_a_344_, v_a_345_);
return v___x_349_;
}
case 4:
{
lean_object* v___x_350_; 
v___x_350_ = l_BitVec_mul(v_w_342_, v_a_344_, v_a_345_);
return v___x_350_;
}
case 5:
{
lean_object* v___x_351_; 
v___x_351_ = lean_nat_div(v_a_344_, v_a_345_);
return v___x_351_;
}
default: 
{
lean_object* v___x_352_; 
v___x_352_ = lean_nat_mod(v_a_344_, v_a_345_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* v_w_353_, lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint8_t v_x_354__boxed_357_; lean_object* v_res_358_; 
v_x_354__boxed_357_ = lean_unbox(v_x_354_);
v_res_358_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_353_, v_x_354__boxed_357_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec(v_a_355_);
lean_dec(v_w_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(lean_object* v_x_359_){
_start:
{
switch(lean_obj_tag(v_x_359_))
{
case 0:
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(0u);
return v___x_360_;
}
case 1:
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(1u);
return v___x_361_;
}
case 2:
{
lean_object* v___x_362_; 
v___x_362_ = lean_unsigned_to_nat(2u);
return v___x_362_;
}
case 3:
{
lean_object* v___x_363_; 
v___x_363_ = lean_unsigned_to_nat(3u);
return v___x_363_;
}
case 4:
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(4u);
return v___x_364_;
}
case 5:
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(5u);
return v___x_365_;
}
default: 
{
lean_object* v___x_366_; 
v___x_366_ = lean_unsigned_to_nat(6u);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(v_x_367_);
lean_dec(v_x_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* v_t_369_, lean_object* v_k_370_){
_start:
{
switch(lean_obj_tag(v_t_369_))
{
case 1:
{
lean_object* v_n_371_; lean_object* v___x_372_; 
v_n_371_ = lean_ctor_get(v_t_369_, 0);
lean_inc(v_n_371_);
lean_dec_ref(v_t_369_);
v___x_372_ = lean_apply_1(v_k_370_, v_n_371_);
return v___x_372_;
}
case 2:
{
lean_object* v_n_373_; lean_object* v___x_374_; 
v_n_373_ = lean_ctor_get(v_t_369_, 0);
lean_inc(v_n_373_);
lean_dec_ref(v_t_369_);
v___x_374_ = lean_apply_1(v_k_370_, v_n_373_);
return v___x_374_;
}
case 3:
{
lean_object* v_n_375_; lean_object* v___x_376_; 
v_n_375_ = lean_ctor_get(v_t_369_, 0);
lean_inc(v_n_375_);
lean_dec_ref(v_t_369_);
v___x_376_ = lean_apply_1(v_k_370_, v_n_375_);
return v___x_376_;
}
default: 
{
lean_dec(v_t_369_);
return v_k_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_379_, v_k_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* v_motive_383_, lean_object* v_ctorIdx_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_k_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(v_motive_383_, v_ctorIdx_384_, v_t_385_, v_h_386_, v_k_387_);
lean_dec(v_ctorIdx_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* v_t_389_, lean_object* v_not_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_389_, v_not_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_not_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_393_, v_not_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* v_t_397_, lean_object* v_rotateLeft_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_397_, v_rotateLeft_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* v_motive_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_rotateLeft_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_401_, v_rotateLeft_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* v_t_405_, lean_object* v_rotateRight_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_405_, v_rotateRight_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_rotateRight_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_409_, v_rotateRight_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* v_t_413_, lean_object* v_arithShiftRightConst_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_413_, v_arithShiftRightConst_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* v_motive_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_arithShiftRightConst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_417_, v_arithShiftRightConst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* v_t_421_, lean_object* v_reverse_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_421_, v_reverse_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* v_motive_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_reverse_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_425_, v_reverse_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* v_t_429_, lean_object* v_clz_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_429_, v_clz_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_clz_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_433_, v_clz_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object* v_t_437_, lean_object* v_cpop_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_437_, v_cpop_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_cpop_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_441_, v_cpop_443_);
return v___x_444_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* v_x_445_){
_start:
{
switch(lean_obj_tag(v_x_445_))
{
case 0:
{
uint64_t v___x_446_; 
v___x_446_ = 0ULL;
return v___x_446_;
}
case 1:
{
lean_object* v_n_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; 
v_n_447_ = lean_ctor_get(v_x_445_, 0);
v___x_448_ = 1ULL;
v___x_449_ = lean_uint64_of_nat(v_n_447_);
v___x_450_ = lean_uint64_mix_hash(v___x_448_, v___x_449_);
return v___x_450_;
}
case 2:
{
lean_object* v_n_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; 
v_n_451_ = lean_ctor_get(v_x_445_, 0);
v___x_452_ = 2ULL;
v___x_453_ = lean_uint64_of_nat(v_n_451_);
v___x_454_ = lean_uint64_mix_hash(v___x_452_, v___x_453_);
return v___x_454_;
}
case 3:
{
lean_object* v_n_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; 
v_n_455_ = lean_ctor_get(v_x_445_, 0);
v___x_456_ = 3ULL;
v___x_457_ = lean_uint64_of_nat(v_n_455_);
v___x_458_ = lean_uint64_mix_hash(v___x_456_, v___x_457_);
return v___x_458_;
}
case 4:
{
uint64_t v___x_459_; 
v___x_459_ = 4ULL;
return v___x_459_;
}
case 5:
{
uint64_t v___x_460_; 
v___x_460_ = 5ULL;
return v___x_460_;
}
default: 
{
uint64_t v___x_461_; 
v___x_461_ = 6ULL;
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object* v_x_462_){
_start:
{
uint64_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_462_);
lean_dec(v_x_462_);
v_r_464_ = lean_box_uint64(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
switch(lean_obj_tag(v_x_467_))
{
case 0:
{
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
case 4:
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
case 5:
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
case 6:
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
default: 
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
}
}
case 1:
{
lean_object* v_n_474_; uint8_t v___x_475_; 
v_n_474_ = lean_ctor_get(v_x_467_, 0);
v___x_475_ = 0;
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
return v___x_475_;
}
case 1:
{
lean_object* v_n_476_; uint8_t v___x_477_; 
v_n_476_ = lean_ctor_get(v_x_468_, 0);
v___x_477_ = lean_nat_dec_eq(v_n_474_, v_n_476_);
if (v___x_477_ == 0)
{
return v___x_475_;
}
else
{
return v___x_477_;
}
}
case 4:
{
return v___x_475_;
}
case 5:
{
return v___x_475_;
}
case 6:
{
return v___x_475_;
}
default: 
{
return v___x_475_;
}
}
}
case 2:
{
lean_object* v_n_478_; uint8_t v___x_479_; 
v_n_478_ = lean_ctor_get(v_x_467_, 0);
v___x_479_ = 0;
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
return v___x_479_;
}
case 2:
{
lean_object* v_n_480_; uint8_t v___x_481_; 
v_n_480_ = lean_ctor_get(v_x_468_, 0);
v___x_481_ = lean_nat_dec_eq(v_n_478_, v_n_480_);
if (v___x_481_ == 0)
{
return v___x_479_;
}
else
{
return v___x_481_;
}
}
case 4:
{
return v___x_479_;
}
case 5:
{
return v___x_479_;
}
case 6:
{
return v___x_479_;
}
default: 
{
return v___x_479_;
}
}
}
case 3:
{
lean_object* v_n_482_; uint8_t v___x_483_; 
v_n_482_ = lean_ctor_get(v_x_467_, 0);
v___x_483_ = 0;
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
return v___x_483_;
}
case 3:
{
lean_object* v_n_484_; uint8_t v___x_485_; 
v_n_484_ = lean_ctor_get(v_x_468_, 0);
v___x_485_ = lean_nat_dec_eq(v_n_482_, v_n_484_);
if (v___x_485_ == 0)
{
return v___x_483_;
}
else
{
return v___x_485_;
}
}
case 4:
{
return v___x_483_;
}
case 5:
{
return v___x_483_;
}
case 6:
{
return v___x_483_;
}
default: 
{
return v___x_483_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_468_))
{
case 1:
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
case 2:
{
uint8_t v___x_487_; 
v___x_487_ = 0;
return v___x_487_;
}
case 3:
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
case 4:
{
uint8_t v___x_489_; 
v___x_489_ = 1;
return v___x_489_;
}
default: 
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_468_))
{
case 1:
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
case 2:
{
uint8_t v___x_492_; 
v___x_492_ = 0;
return v___x_492_;
}
case 3:
{
uint8_t v___x_493_; 
v___x_493_ = 0;
return v___x_493_;
}
case 5:
{
uint8_t v___x_494_; 
v___x_494_ = 1;
return v___x_494_;
}
default: 
{
uint8_t v___x_495_; 
v___x_495_ = 0;
return v___x_495_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_468_))
{
case 1:
{
uint8_t v___x_496_; 
v___x_496_ = 0;
return v___x_496_;
}
case 2:
{
uint8_t v___x_497_; 
v___x_497_ = 0;
return v___x_497_;
}
case 3:
{
uint8_t v___x_498_; 
v___x_498_ = 0;
return v___x_498_;
}
case 6:
{
uint8_t v___x_499_; 
v___x_499_ = 1;
return v___x_499_;
}
default: 
{
uint8_t v___x_500_; 
v___x_500_ = 0;
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_501_, v_x_502_);
lean_dec(v_x_502_);
lean_dec(v_x_501_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_x_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_519_){
_start:
{
switch(lean_obj_tag(v_x_519_))
{
case 0:
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_520_;
}
case 1:
{
lean_object* v_n_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_n_521_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_n_521_);
lean_dec_ref(v_x_519_);
v___x_522_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_523_ = l_Nat_reprFast(v_n_521_);
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
lean_dec_ref(v___x_523_);
return v___x_524_;
}
case 2:
{
lean_object* v_n_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_n_525_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_n_525_);
lean_dec_ref(v_x_519_);
v___x_526_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_527_ = l_Nat_reprFast(v_n_525_);
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
lean_dec_ref(v___x_527_);
return v___x_528_;
}
case 3:
{
lean_object* v_n_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_n_529_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_n_529_);
lean_dec_ref(v_x_519_);
v___x_530_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_531_ = l_Nat_reprFast(v_n_529_);
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
lean_dec_ref(v___x_531_);
return v___x_532_;
}
case 4:
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_533_;
}
case 5:
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_534_;
}
default: 
{
lean_object* v___x_535_; 
v___x_535_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_538_, lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
switch(lean_obj_tag(v_x_539_))
{
case 0:
{
lean_object* v___x_541_; 
v___x_541_ = l_BitVec_not(v_w_538_, v_a_540_);
lean_dec(v_a_540_);
lean_dec(v_w_538_);
return v___x_541_;
}
case 1:
{
lean_object* v_n_542_; lean_object* v___x_543_; 
v_n_542_ = lean_ctor_get(v_x_539_, 0);
v___x_543_ = l_BitVec_rotateLeft(v_w_538_, v_a_540_, v_n_542_);
lean_dec(v_a_540_);
lean_dec(v_w_538_);
return v___x_543_;
}
case 2:
{
lean_object* v_n_544_; lean_object* v___x_545_; 
v_n_544_ = lean_ctor_get(v_x_539_, 0);
v___x_545_ = l_BitVec_rotateRight(v_w_538_, v_a_540_, v_n_544_);
lean_dec(v_a_540_);
lean_dec(v_w_538_);
return v___x_545_;
}
case 3:
{
lean_object* v_n_546_; lean_object* v___x_547_; 
v_n_546_ = lean_ctor_get(v_x_539_, 0);
v___x_547_ = l_BitVec_sshiftRight(v_w_538_, v_a_540_, v_n_546_);
lean_dec(v_w_538_);
return v___x_547_;
}
case 4:
{
lean_object* v___x_548_; 
v___x_548_ = l_BitVec_reverse(v_w_538_, v_a_540_);
lean_dec(v_a_540_);
lean_dec(v_w_538_);
return v___x_548_;
}
case 5:
{
lean_object* v___x_549_; 
v___x_549_ = l_BitVec_clz(v_w_538_, v_a_540_);
lean_dec(v_a_540_);
lean_dec(v_w_538_);
return v___x_549_;
}
default: 
{
lean_object* v___x_550_; 
v___x_550_ = l_BitVec_cpop(v_w_538_, v_a_540_);
lean_dec(v_a_540_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_551_, lean_object* v_x_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_551_, v_x_552_, v_a_553_);
lean_dec(v_x_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object* v_x_555_){
_start:
{
switch(lean_obj_tag(v_x_555_))
{
case 0:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(0u);
return v___x_556_;
}
case 1:
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(1u);
return v___x_557_;
}
case 2:
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(2u);
return v___x_558_;
}
case 3:
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(3u);
return v___x_559_;
}
case 4:
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(4u);
return v___x_560_;
}
case 5:
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(5u);
return v___x_561_;
}
case 6:
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(6u);
return v___x_562_;
}
case 7:
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(7u);
return v___x_563_;
}
case 8:
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(8u);
return v___x_564_;
}
default: 
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(9u);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_566_);
lean_dec_ref(v_x_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object* v_a_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(v_a_571_, v_x_572_);
lean_dec_ref(v_x_572_);
lean_dec(v_a_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_574_, lean_object* v_k_575_){
_start:
{
switch(lean_obj_tag(v_t_574_))
{
case 0:
{
lean_object* v_w_576_; lean_object* v_idx_577_; lean_object* v___x_578_; 
v_w_576_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_576_);
v_idx_577_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_idx_577_);
lean_dec_ref(v_t_574_);
v___x_578_ = lean_apply_2(v_k_575_, v_w_576_, v_idx_577_);
return v___x_578_;
}
case 1:
{
lean_object* v_w_579_; lean_object* v_val_580_; lean_object* v___x_581_; 
v_w_579_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_579_);
v_val_580_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_val_580_);
lean_dec_ref(v_t_574_);
v___x_581_ = lean_apply_2(v_k_575_, v_w_579_, v_val_580_);
return v___x_581_;
}
case 2:
{
lean_object* v_w_582_; lean_object* v_start_583_; lean_object* v_len_584_; lean_object* v_expr_585_; lean_object* v___x_586_; 
v_w_582_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_582_);
v_start_583_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_start_583_);
v_len_584_ = lean_ctor_get(v_t_574_, 2);
lean_inc(v_len_584_);
v_expr_585_ = lean_ctor_get(v_t_574_, 3);
lean_inc_ref(v_expr_585_);
lean_dec_ref(v_t_574_);
v___x_586_ = lean_apply_4(v_k_575_, v_w_582_, v_start_583_, v_len_584_, v_expr_585_);
return v___x_586_;
}
case 3:
{
lean_object* v_w_587_; lean_object* v_lhs_588_; uint8_t v_op_589_; lean_object* v_rhs_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_w_587_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_587_);
v_lhs_588_ = lean_ctor_get(v_t_574_, 1);
lean_inc_ref(v_lhs_588_);
v_op_589_ = lean_ctor_get_uint8(v_t_574_, sizeof(void*)*3);
v_rhs_590_ = lean_ctor_get(v_t_574_, 2);
lean_inc_ref(v_rhs_590_);
lean_dec_ref(v_t_574_);
v___x_591_ = lean_box(v_op_589_);
v___x_592_ = lean_apply_4(v_k_575_, v_w_587_, v_lhs_588_, v___x_591_, v_rhs_590_);
return v___x_592_;
}
case 4:
{
lean_object* v_w_593_; lean_object* v_op_594_; lean_object* v_operand_595_; lean_object* v___x_596_; 
v_w_593_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_593_);
v_op_594_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_op_594_);
v_operand_595_ = lean_ctor_get(v_t_574_, 2);
lean_inc_ref(v_operand_595_);
lean_dec_ref(v_t_574_);
v___x_596_ = lean_apply_3(v_k_575_, v_w_593_, v_op_594_, v_operand_595_);
return v___x_596_;
}
case 5:
{
lean_object* v_l_597_; lean_object* v_r_598_; lean_object* v_w_599_; lean_object* v_lhs_600_; lean_object* v_rhs_601_; lean_object* v___x_602_; 
v_l_597_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_l_597_);
v_r_598_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_r_598_);
v_w_599_ = lean_ctor_get(v_t_574_, 2);
lean_inc(v_w_599_);
v_lhs_600_ = lean_ctor_get(v_t_574_, 3);
lean_inc_ref(v_lhs_600_);
v_rhs_601_ = lean_ctor_get(v_t_574_, 4);
lean_inc_ref(v_rhs_601_);
lean_dec_ref(v_t_574_);
v___x_602_ = lean_apply_6(v_k_575_, v_l_597_, v_r_598_, v_w_599_, v_lhs_600_, v_rhs_601_, lean_box(0));
return v___x_602_;
}
case 6:
{
lean_object* v_w_603_; lean_object* v_w_x27_604_; lean_object* v_n_605_; lean_object* v_expr_606_; lean_object* v___x_607_; 
v_w_603_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_w_603_);
v_w_x27_604_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_w_x27_604_);
v_n_605_ = lean_ctor_get(v_t_574_, 2);
lean_inc(v_n_605_);
v_expr_606_ = lean_ctor_get(v_t_574_, 3);
lean_inc_ref(v_expr_606_);
lean_dec_ref(v_t_574_);
v___x_607_ = lean_apply_5(v_k_575_, v_w_603_, v_w_x27_604_, v_n_605_, v_expr_606_, lean_box(0));
return v___x_607_;
}
default: 
{
lean_object* v_m_608_; lean_object* v_n_609_; lean_object* v_lhs_610_; lean_object* v_rhs_611_; lean_object* v___x_612_; 
v_m_608_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_m_608_);
v_n_609_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_n_609_);
v_lhs_610_ = lean_ctor_get(v_t_574_, 2);
lean_inc_ref(v_lhs_610_);
v_rhs_611_ = lean_ctor_get(v_t_574_, 3);
lean_inc_ref(v_rhs_611_);
lean_dec_ref(v_t_574_);
v___x_612_ = lean_apply_4(v_k_575_, v_m_608_, v_n_609_, v_lhs_610_, v_rhs_611_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_613_, lean_object* v_ctorIdx_614_, lean_object* v_a_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_616_, v_k_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_620_, lean_object* v_ctorIdx_621_, lean_object* v_a_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_k_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_620_, v_ctorIdx_621_, v_a_622_, v_t_623_, v_h_624_, v_k_625_);
lean_dec(v_a_622_);
lean_dec(v_ctorIdx_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_627_, lean_object* v_var_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_627_, v_var_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_630_, lean_object* v_a_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_var_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_632_, v_var_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_636_, lean_object* v_a_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_var_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_636_, v_a_637_, v_t_638_, v_h_639_, v_var_640_);
lean_dec(v_a_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_642_, lean_object* v_const_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_642_, v_const_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_645_, lean_object* v_a_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_const_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_647_, v_const_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_651_, lean_object* v_a_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_const_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_651_, v_a_652_, v_t_653_, v_h_654_, v_const_655_);
lean_dec(v_a_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_657_, lean_object* v_extract_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_657_, v_extract_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_660_, lean_object* v_a_661_, lean_object* v_t_662_, lean_object* v_h_663_, lean_object* v_extract_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_662_, v_extract_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_666_, lean_object* v_a_667_, lean_object* v_t_668_, lean_object* v_h_669_, lean_object* v_extract_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_666_, v_a_667_, v_t_668_, v_h_669_, v_extract_670_);
lean_dec(v_a_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_672_, lean_object* v_bin_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_672_, v_bin_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_675_, lean_object* v_a_676_, lean_object* v_t_677_, lean_object* v_h_678_, lean_object* v_bin_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_677_, v_bin_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_681_, lean_object* v_a_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_bin_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_681_, v_a_682_, v_t_683_, v_h_684_, v_bin_685_);
lean_dec(v_a_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_687_, lean_object* v_un_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_687_, v_un_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_690_, lean_object* v_a_691_, lean_object* v_t_692_, lean_object* v_h_693_, lean_object* v_un_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_692_, v_un_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_696_, lean_object* v_a_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_un_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_696_, v_a_697_, v_t_698_, v_h_699_, v_un_700_);
lean_dec(v_a_697_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_702_, lean_object* v_append_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_702_, v_append_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_705_, lean_object* v_a_706_, lean_object* v_t_707_, lean_object* v_h_708_, lean_object* v_append_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_707_, v_append_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_711_, lean_object* v_a_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_append_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_711_, v_a_712_, v_t_713_, v_h_714_, v_append_715_);
lean_dec(v_a_712_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_717_, lean_object* v_replicate_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_717_, v_replicate_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_720_, lean_object* v_a_721_, lean_object* v_t_722_, lean_object* v_h_723_, lean_object* v_replicate_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_722_, v_replicate_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_726_, lean_object* v_a_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_replicate_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_726_, v_a_727_, v_t_728_, v_h_729_, v_replicate_730_);
lean_dec(v_a_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_732_, lean_object* v_shiftLeft_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_732_, v_shiftLeft_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_735_, lean_object* v_a_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_shiftLeft_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_737_, v_shiftLeft_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_741_, lean_object* v_a_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_shiftLeft_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_741_, v_a_742_, v_t_743_, v_h_744_, v_shiftLeft_745_);
lean_dec(v_a_742_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_747_, lean_object* v_shiftRight_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_747_, v_shiftRight_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_750_, lean_object* v_a_751_, lean_object* v_t_752_, lean_object* v_h_753_, lean_object* v_shiftRight_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_752_, v_shiftRight_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_756_, lean_object* v_a_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_shiftRight_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_756_, v_a_757_, v_t_758_, v_h_759_, v_shiftRight_760_);
lean_dec(v_a_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_762_, lean_object* v_arithShiftRight_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_762_, v_arithShiftRight_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_765_, lean_object* v_a_766_, lean_object* v_t_767_, lean_object* v_h_768_, lean_object* v_arithShiftRight_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_767_, v_arithShiftRight_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_771_, lean_object* v_a_772_, lean_object* v_t_773_, lean_object* v_h_774_, lean_object* v_arithShiftRight_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_771_, v_a_772_, v_t_773_, v_h_774_, v_arithShiftRight_775_);
lean_dec(v_a_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_777_, lean_object* v_var_778_, lean_object* v_const_779_, lean_object* v_extract_780_, lean_object* v_bin_781_, lean_object* v_un_782_, lean_object* v_append_783_, lean_object* v_replicate_784_, lean_object* v_shiftLeft_785_, lean_object* v_shiftRight_786_, lean_object* v_arithShiftRight_787_){
_start:
{
switch(lean_obj_tag(v_t_777_))
{
case 0:
{
lean_object* v_w_788_; lean_object* v_idx_789_; lean_object* v___x_790_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
v_w_788_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_788_);
v_idx_789_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_idx_789_);
lean_dec_ref(v_t_777_);
v___x_790_ = lean_apply_2(v_var_778_, v_w_788_, v_idx_789_);
return v___x_790_;
}
case 1:
{
lean_object* v_w_791_; lean_object* v_val_792_; lean_object* v___x_793_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_var_778_);
v_w_791_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_791_);
v_val_792_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_val_792_);
lean_dec_ref(v_t_777_);
v___x_793_ = lean_apply_2(v_const_779_, v_w_791_, v_val_792_);
return v___x_793_;
}
case 2:
{
lean_object* v_w_794_; lean_object* v_start_795_; lean_object* v_len_796_; lean_object* v_expr_797_; lean_object* v___x_798_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_w_794_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_794_);
v_start_795_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_start_795_);
v_len_796_ = lean_ctor_get(v_t_777_, 2);
lean_inc(v_len_796_);
v_expr_797_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_expr_797_);
lean_dec_ref(v_t_777_);
v___x_798_ = lean_apply_4(v_extract_780_, v_w_794_, v_start_795_, v_len_796_, v_expr_797_);
return v___x_798_;
}
case 3:
{
lean_object* v_w_799_; lean_object* v_lhs_800_; uint8_t v_op_801_; lean_object* v_rhs_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_w_799_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_799_);
v_lhs_800_ = lean_ctor_get(v_t_777_, 1);
lean_inc_ref(v_lhs_800_);
v_op_801_ = lean_ctor_get_uint8(v_t_777_, sizeof(void*)*3 + 8);
v_rhs_802_ = lean_ctor_get(v_t_777_, 2);
lean_inc_ref(v_rhs_802_);
lean_dec_ref(v_t_777_);
v___x_803_ = lean_box(v_op_801_);
v___x_804_ = lean_apply_4(v_bin_781_, v_w_799_, v_lhs_800_, v___x_803_, v_rhs_802_);
return v___x_804_;
}
case 4:
{
lean_object* v_w_805_; lean_object* v_op_806_; lean_object* v_operand_807_; lean_object* v___x_808_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_w_805_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_805_);
v_op_806_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_op_806_);
v_operand_807_ = lean_ctor_get(v_t_777_, 2);
lean_inc_ref(v_operand_807_);
lean_dec_ref(v_t_777_);
v___x_808_ = lean_apply_3(v_un_782_, v_w_805_, v_op_806_, v_operand_807_);
return v___x_808_;
}
case 5:
{
lean_object* v_l_809_; lean_object* v_r_810_; lean_object* v_w_811_; lean_object* v_lhs_812_; lean_object* v_rhs_813_; lean_object* v___x_814_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_l_809_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_l_809_);
v_r_810_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_r_810_);
v_w_811_ = lean_ctor_get(v_t_777_, 2);
lean_inc(v_w_811_);
v_lhs_812_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_lhs_812_);
v_rhs_813_ = lean_ctor_get(v_t_777_, 4);
lean_inc_ref(v_rhs_813_);
lean_dec_ref(v_t_777_);
v___x_814_ = lean_apply_6(v_append_783_, v_l_809_, v_r_810_, v_w_811_, v_lhs_812_, v_rhs_813_, lean_box(0));
return v___x_814_;
}
case 6:
{
lean_object* v_w_815_; lean_object* v_w_x27_816_; lean_object* v_n_817_; lean_object* v_expr_818_; lean_object* v___x_819_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_w_815_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_w_815_);
v_w_x27_816_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_w_x27_816_);
v_n_817_ = lean_ctor_get(v_t_777_, 2);
lean_inc(v_n_817_);
v_expr_818_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_expr_818_);
lean_dec_ref(v_t_777_);
v___x_819_ = lean_apply_5(v_replicate_784_, v_w_815_, v_w_x27_816_, v_n_817_, v_expr_818_, lean_box(0));
return v___x_819_;
}
case 7:
{
lean_object* v_m_820_; lean_object* v_n_821_; lean_object* v_lhs_822_; lean_object* v_rhs_823_; lean_object* v___x_824_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftRight_786_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_m_820_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_m_820_);
v_n_821_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_n_821_);
v_lhs_822_ = lean_ctor_get(v_t_777_, 2);
lean_inc_ref(v_lhs_822_);
v_rhs_823_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_rhs_823_);
lean_dec_ref(v_t_777_);
v___x_824_ = lean_apply_4(v_shiftLeft_785_, v_m_820_, v_n_821_, v_lhs_822_, v_rhs_823_);
return v___x_824_;
}
case 8:
{
lean_object* v_m_825_; lean_object* v_n_826_; lean_object* v_lhs_827_; lean_object* v_rhs_828_; lean_object* v___x_829_; 
lean_dec(v_arithShiftRight_787_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_m_825_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_m_825_);
v_n_826_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_n_826_);
v_lhs_827_ = lean_ctor_get(v_t_777_, 2);
lean_inc_ref(v_lhs_827_);
v_rhs_828_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_rhs_828_);
lean_dec_ref(v_t_777_);
v___x_829_ = lean_apply_4(v_shiftRight_786_, v_m_825_, v_n_826_, v_lhs_827_, v_rhs_828_);
return v___x_829_;
}
default: 
{
lean_object* v_m_830_; lean_object* v_n_831_; lean_object* v_lhs_832_; lean_object* v_rhs_833_; lean_object* v___x_834_; 
lean_dec(v_shiftRight_786_);
lean_dec(v_shiftLeft_785_);
lean_dec(v_replicate_784_);
lean_dec(v_append_783_);
lean_dec(v_un_782_);
lean_dec(v_bin_781_);
lean_dec(v_extract_780_);
lean_dec(v_const_779_);
lean_dec(v_var_778_);
v_m_830_ = lean_ctor_get(v_t_777_, 0);
lean_inc(v_m_830_);
v_n_831_ = lean_ctor_get(v_t_777_, 1);
lean_inc(v_n_831_);
v_lhs_832_ = lean_ctor_get(v_t_777_, 2);
lean_inc_ref(v_lhs_832_);
v_rhs_833_ = lean_ctor_get(v_t_777_, 3);
lean_inc_ref(v_rhs_833_);
lean_dec_ref(v_t_777_);
v___x_834_ = lean_apply_4(v_arithShiftRight_787_, v_m_830_, v_n_831_, v_lhs_832_, v_rhs_833_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_835_, lean_object* v_a_836_, lean_object* v_t_837_, lean_object* v_var_838_, lean_object* v_const_839_, lean_object* v_extract_840_, lean_object* v_bin_841_, lean_object* v_un_842_, lean_object* v_append_843_, lean_object* v_replicate_844_, lean_object* v_shiftLeft_845_, lean_object* v_shiftRight_846_, lean_object* v_arithShiftRight_847_){
_start:
{
switch(lean_obj_tag(v_t_837_))
{
case 0:
{
lean_object* v_w_848_; lean_object* v_idx_849_; lean_object* v___x_850_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
v_w_848_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_848_);
v_idx_849_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_idx_849_);
lean_dec_ref(v_t_837_);
v___x_850_ = lean_apply_2(v_var_838_, v_w_848_, v_idx_849_);
return v___x_850_;
}
case 1:
{
lean_object* v_w_851_; lean_object* v_val_852_; lean_object* v___x_853_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_var_838_);
v_w_851_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_851_);
v_val_852_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_val_852_);
lean_dec_ref(v_t_837_);
v___x_853_ = lean_apply_2(v_const_839_, v_w_851_, v_val_852_);
return v___x_853_;
}
case 2:
{
lean_object* v_w_854_; lean_object* v_start_855_; lean_object* v_len_856_; lean_object* v_expr_857_; lean_object* v___x_858_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_w_854_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_854_);
v_start_855_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_start_855_);
v_len_856_ = lean_ctor_get(v_t_837_, 2);
lean_inc(v_len_856_);
v_expr_857_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_expr_857_);
lean_dec_ref(v_t_837_);
v___x_858_ = lean_apply_4(v_extract_840_, v_w_854_, v_start_855_, v_len_856_, v_expr_857_);
return v___x_858_;
}
case 3:
{
lean_object* v_w_859_; lean_object* v_lhs_860_; uint8_t v_op_861_; lean_object* v_rhs_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_w_859_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_859_);
v_lhs_860_ = lean_ctor_get(v_t_837_, 1);
lean_inc_ref(v_lhs_860_);
v_op_861_ = lean_ctor_get_uint8(v_t_837_, sizeof(void*)*3 + 8);
v_rhs_862_ = lean_ctor_get(v_t_837_, 2);
lean_inc_ref(v_rhs_862_);
lean_dec_ref(v_t_837_);
v___x_863_ = lean_box(v_op_861_);
v___x_864_ = lean_apply_4(v_bin_841_, v_w_859_, v_lhs_860_, v___x_863_, v_rhs_862_);
return v___x_864_;
}
case 4:
{
lean_object* v_w_865_; lean_object* v_op_866_; lean_object* v_operand_867_; lean_object* v___x_868_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_w_865_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_865_);
v_op_866_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_op_866_);
v_operand_867_ = lean_ctor_get(v_t_837_, 2);
lean_inc_ref(v_operand_867_);
lean_dec_ref(v_t_837_);
v___x_868_ = lean_apply_3(v_un_842_, v_w_865_, v_op_866_, v_operand_867_);
return v___x_868_;
}
case 5:
{
lean_object* v_l_869_; lean_object* v_r_870_; lean_object* v_w_871_; lean_object* v_lhs_872_; lean_object* v_rhs_873_; lean_object* v___x_874_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_l_869_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_l_869_);
v_r_870_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_r_870_);
v_w_871_ = lean_ctor_get(v_t_837_, 2);
lean_inc(v_w_871_);
v_lhs_872_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_lhs_872_);
v_rhs_873_ = lean_ctor_get(v_t_837_, 4);
lean_inc_ref(v_rhs_873_);
lean_dec_ref(v_t_837_);
v___x_874_ = lean_apply_6(v_append_843_, v_l_869_, v_r_870_, v_w_871_, v_lhs_872_, v_rhs_873_, lean_box(0));
return v___x_874_;
}
case 6:
{
lean_object* v_w_875_; lean_object* v_w_x27_876_; lean_object* v_n_877_; lean_object* v_expr_878_; lean_object* v___x_879_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_w_875_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_w_875_);
v_w_x27_876_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_w_x27_876_);
v_n_877_ = lean_ctor_get(v_t_837_, 2);
lean_inc(v_n_877_);
v_expr_878_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_expr_878_);
lean_dec_ref(v_t_837_);
v___x_879_ = lean_apply_5(v_replicate_844_, v_w_875_, v_w_x27_876_, v_n_877_, v_expr_878_, lean_box(0));
return v___x_879_;
}
case 7:
{
lean_object* v_m_880_; lean_object* v_n_881_; lean_object* v_lhs_882_; lean_object* v_rhs_883_; lean_object* v___x_884_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftRight_846_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_m_880_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_m_880_);
v_n_881_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_n_881_);
v_lhs_882_ = lean_ctor_get(v_t_837_, 2);
lean_inc_ref(v_lhs_882_);
v_rhs_883_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_rhs_883_);
lean_dec_ref(v_t_837_);
v___x_884_ = lean_apply_4(v_shiftLeft_845_, v_m_880_, v_n_881_, v_lhs_882_, v_rhs_883_);
return v___x_884_;
}
case 8:
{
lean_object* v_m_885_; lean_object* v_n_886_; lean_object* v_lhs_887_; lean_object* v_rhs_888_; lean_object* v___x_889_; 
lean_dec(v_arithShiftRight_847_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_m_885_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_m_885_);
v_n_886_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_n_886_);
v_lhs_887_ = lean_ctor_get(v_t_837_, 2);
lean_inc_ref(v_lhs_887_);
v_rhs_888_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_rhs_888_);
lean_dec_ref(v_t_837_);
v___x_889_ = lean_apply_4(v_shiftRight_846_, v_m_885_, v_n_886_, v_lhs_887_, v_rhs_888_);
return v___x_889_;
}
default: 
{
lean_object* v_m_890_; lean_object* v_n_891_; lean_object* v_lhs_892_; lean_object* v_rhs_893_; lean_object* v___x_894_; 
lean_dec(v_shiftRight_846_);
lean_dec(v_shiftLeft_845_);
lean_dec(v_replicate_844_);
lean_dec(v_append_843_);
lean_dec(v_un_842_);
lean_dec(v_bin_841_);
lean_dec(v_extract_840_);
lean_dec(v_const_839_);
lean_dec(v_var_838_);
v_m_890_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_m_890_);
v_n_891_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_n_891_);
v_lhs_892_ = lean_ctor_get(v_t_837_, 2);
lean_inc_ref(v_lhs_892_);
v_rhs_893_ = lean_ctor_get(v_t_837_, 3);
lean_inc_ref(v_rhs_893_);
lean_dec_ref(v_t_837_);
v___x_894_ = lean_apply_4(v_arithShiftRight_847_, v_m_890_, v_n_891_, v_lhs_892_, v_rhs_893_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_895_, lean_object* v_a_896_, lean_object* v_t_897_, lean_object* v_var_898_, lean_object* v_const_899_, lean_object* v_extract_900_, lean_object* v_bin_901_, lean_object* v_un_902_, lean_object* v_append_903_, lean_object* v_replicate_904_, lean_object* v_shiftLeft_905_, lean_object* v_shiftRight_906_, lean_object* v_arithShiftRight_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_895_, v_a_896_, v_t_897_, v_var_898_, v_const_899_, v_extract_900_, v_bin_901_, v_un_902_, v_append_903_, v_replicate_904_, v_shiftLeft_905_, v_shiftRight_906_, v_arithShiftRight_907_);
lean_dec(v_a_896_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_909_, lean_object* v_idx_910_){
_start:
{
uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; lean_object* v___x_916_; 
v___x_911_ = 5ULL;
v___x_912_ = lean_uint64_of_nat(v_w_909_);
v___x_913_ = lean_uint64_of_nat(v_idx_910_);
v___x_914_ = lean_uint64_mix_hash(v___x_912_, v___x_913_);
v___x_915_ = lean_uint64_mix_hash(v___x_911_, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_916_, 0, v_w_909_);
lean_ctor_set(v___x_916_, 1, v_idx_910_);
lean_ctor_set_uint64(v___x_916_, sizeof(void*)*2, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_917_, lean_object* v_val_918_){
_start:
{
uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; lean_object* v___x_924_; 
v___x_919_ = 7ULL;
v___x_920_ = lean_uint64_of_nat(v_w_917_);
v___x_921_ = l_BitVec_hash(v_w_917_, v_val_918_);
v___x_922_ = lean_uint64_mix_hash(v___x_920_, v___x_921_);
v___x_923_ = lean_uint64_mix_hash(v___x_919_, v___x_922_);
v___x_924_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_924_, 0, v_w_917_);
lean_ctor_set(v___x_924_, 1, v_val_918_);
lean_ctor_set_uint64(v___x_924_, sizeof(void*)*2, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_925_, lean_object* v_start_926_, lean_object* v_len_927_, lean_object* v_expr_928_){
_start:
{
uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v___y_933_; 
v___x_929_ = 11ULL;
v___x_930_ = lean_uint64_of_nat(v_start_926_);
v___x_931_ = lean_uint64_of_nat(v_len_927_);
switch(lean_obj_tag(v_expr_928_))
{
case 0:
{
uint64_t v_hashCode_938_; 
v_hashCode_938_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*2);
v___y_933_ = v_hashCode_938_;
goto v___jp_932_;
}
case 1:
{
uint64_t v_hashCode_939_; 
v_hashCode_939_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*2);
v___y_933_ = v_hashCode_939_;
goto v___jp_932_;
}
case 3:
{
uint64_t v_hashCode_940_; 
v_hashCode_940_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*3);
v___y_933_ = v_hashCode_940_;
goto v___jp_932_;
}
case 4:
{
uint64_t v_hashCode_941_; 
v_hashCode_941_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*3);
v___y_933_ = v_hashCode_941_;
goto v___jp_932_;
}
case 5:
{
uint64_t v_hashCode_942_; 
v_hashCode_942_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*5);
v___y_933_ = v_hashCode_942_;
goto v___jp_932_;
}
default: 
{
uint64_t v_hashCode_943_; 
v_hashCode_943_ = lean_ctor_get_uint64(v_expr_928_, sizeof(void*)*4);
v___y_933_ = v_hashCode_943_;
goto v___jp_932_;
}
}
v___jp_932_:
{
uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; lean_object* v___x_937_; 
v___x_934_ = lean_uint64_mix_hash(v___x_931_, v___y_933_);
v___x_935_ = lean_uint64_mix_hash(v___x_930_, v___x_934_);
v___x_936_ = lean_uint64_mix_hash(v___x_929_, v___x_935_);
v___x_937_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_937_, 0, v_w_925_);
lean_ctor_set(v___x_937_, 1, v_start_926_);
lean_ctor_set(v___x_937_, 2, v_len_927_);
lean_ctor_set(v___x_937_, 3, v_expr_928_);
lean_ctor_set_uint64(v___x_937_, sizeof(void*)*4, v___x_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_944_, lean_object* v_lhs_945_, uint8_t v_op_946_, lean_object* v_rhs_947_){
_start:
{
uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v___y_951_; uint64_t v___y_952_; uint64_t v___y_953_; uint64_t v___y_960_; 
v___x_948_ = 13ULL;
v___x_949_ = lean_uint64_of_nat(v_w_944_);
switch(lean_obj_tag(v_lhs_945_))
{
case 0:
{
uint64_t v_hashCode_968_; 
v_hashCode_968_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*2);
v___y_960_ = v_hashCode_968_;
goto v___jp_959_;
}
case 1:
{
uint64_t v_hashCode_969_; 
v_hashCode_969_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*2);
v___y_960_ = v_hashCode_969_;
goto v___jp_959_;
}
case 3:
{
uint64_t v_hashCode_970_; 
v_hashCode_970_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*3);
v___y_960_ = v_hashCode_970_;
goto v___jp_959_;
}
case 4:
{
uint64_t v_hashCode_971_; 
v_hashCode_971_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*3);
v___y_960_ = v_hashCode_971_;
goto v___jp_959_;
}
case 5:
{
uint64_t v_hashCode_972_; 
v_hashCode_972_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*5);
v___y_960_ = v_hashCode_972_;
goto v___jp_959_;
}
default: 
{
uint64_t v_hashCode_973_; 
v_hashCode_973_ = lean_ctor_get_uint64(v_lhs_945_, sizeof(void*)*4);
v___y_960_ = v_hashCode_973_;
goto v___jp_959_;
}
}
v___jp_950_:
{
uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v___x_957_; lean_object* v___x_958_; 
v___x_954_ = lean_uint64_mix_hash(v___y_952_, v___y_953_);
v___x_955_ = lean_uint64_mix_hash(v___y_951_, v___x_954_);
v___x_956_ = lean_uint64_mix_hash(v___x_949_, v___x_955_);
v___x_957_ = lean_uint64_mix_hash(v___x_948_, v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_958_, 0, v_w_944_);
lean_ctor_set(v___x_958_, 1, v_lhs_945_);
lean_ctor_set(v___x_958_, 2, v_rhs_947_);
lean_ctor_set_uint64(v___x_958_, sizeof(void*)*3, v___x_957_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*3 + 8, v_op_946_);
return v___x_958_;
}
v___jp_959_:
{
uint64_t v___x_961_; 
v___x_961_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_946_);
switch(lean_obj_tag(v_rhs_947_))
{
case 0:
{
uint64_t v_hashCode_962_; 
v_hashCode_962_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*2);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_962_;
goto v___jp_950_;
}
case 1:
{
uint64_t v_hashCode_963_; 
v_hashCode_963_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*2);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_963_;
goto v___jp_950_;
}
case 3:
{
uint64_t v_hashCode_964_; 
v_hashCode_964_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*3);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_964_;
goto v___jp_950_;
}
case 4:
{
uint64_t v_hashCode_965_; 
v_hashCode_965_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*3);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_965_;
goto v___jp_950_;
}
case 5:
{
uint64_t v_hashCode_966_; 
v_hashCode_966_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*5);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_966_;
goto v___jp_950_;
}
default: 
{
uint64_t v_hashCode_967_; 
v_hashCode_967_ = lean_ctor_get_uint64(v_rhs_947_, sizeof(void*)*4);
v___y_951_ = v___y_960_;
v___y_952_ = v___x_961_;
v___y_953_ = v_hashCode_967_;
goto v___jp_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_974_, lean_object* v_lhs_975_, lean_object* v_op_976_, lean_object* v_rhs_977_){
_start:
{
uint8_t v_op_boxed_978_; lean_object* v_res_979_; 
v_op_boxed_978_ = lean_unbox(v_op_976_);
v_res_979_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_974_, v_lhs_975_, v_op_boxed_978_, v_rhs_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_980_, lean_object* v_op_981_, lean_object* v_operand_982_){
_start:
{
uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v___y_987_; 
v___x_983_ = 17ULL;
v___x_984_ = lean_uint64_of_nat(v_w_980_);
v___x_985_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_981_);
switch(lean_obj_tag(v_operand_982_))
{
case 0:
{
uint64_t v_hashCode_992_; 
v_hashCode_992_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*2);
v___y_987_ = v_hashCode_992_;
goto v___jp_986_;
}
case 1:
{
uint64_t v_hashCode_993_; 
v_hashCode_993_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*2);
v___y_987_ = v_hashCode_993_;
goto v___jp_986_;
}
case 3:
{
uint64_t v_hashCode_994_; 
v_hashCode_994_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*3);
v___y_987_ = v_hashCode_994_;
goto v___jp_986_;
}
case 4:
{
uint64_t v_hashCode_995_; 
v_hashCode_995_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*3);
v___y_987_ = v_hashCode_995_;
goto v___jp_986_;
}
case 5:
{
uint64_t v_hashCode_996_; 
v_hashCode_996_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*5);
v___y_987_ = v_hashCode_996_;
goto v___jp_986_;
}
default: 
{
uint64_t v_hashCode_997_; 
v_hashCode_997_ = lean_ctor_get_uint64(v_operand_982_, sizeof(void*)*4);
v___y_987_ = v_hashCode_997_;
goto v___jp_986_;
}
}
v___jp_986_:
{
uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_uint64_mix_hash(v___x_985_, v___y_987_);
v___x_989_ = lean_uint64_mix_hash(v___x_984_, v___x_988_);
v___x_990_ = lean_uint64_mix_hash(v___x_983_, v___x_989_);
v___x_991_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_991_, 0, v_w_980_);
lean_ctor_set(v___x_991_, 1, v_op_981_);
lean_ctor_set(v___x_991_, 2, v_operand_982_);
lean_ctor_set_uint64(v___x_991_, sizeof(void*)*3, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_998_, lean_object* v_r_999_, lean_object* v_w_1000_, lean_object* v_lhs_1001_, lean_object* v_rhs_1002_){
_start:
{
uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___y_1006_; uint64_t v___y_1007_; uint64_t v___y_1013_; 
v___x_1003_ = 19ULL;
v___x_1004_ = lean_uint64_of_nat(v_w_1000_);
switch(lean_obj_tag(v_lhs_1001_))
{
case 0:
{
uint64_t v_hashCode_1020_; 
v_hashCode_1020_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*2);
v___y_1013_ = v_hashCode_1020_;
goto v___jp_1012_;
}
case 1:
{
uint64_t v_hashCode_1021_; 
v_hashCode_1021_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*2);
v___y_1013_ = v_hashCode_1021_;
goto v___jp_1012_;
}
case 3:
{
uint64_t v_hashCode_1022_; 
v_hashCode_1022_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*3);
v___y_1013_ = v_hashCode_1022_;
goto v___jp_1012_;
}
case 4:
{
uint64_t v_hashCode_1023_; 
v_hashCode_1023_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*3);
v___y_1013_ = v_hashCode_1023_;
goto v___jp_1012_;
}
case 5:
{
uint64_t v_hashCode_1024_; 
v_hashCode_1024_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*5);
v___y_1013_ = v_hashCode_1024_;
goto v___jp_1012_;
}
default: 
{
uint64_t v_hashCode_1025_; 
v_hashCode_1025_ = lean_ctor_get_uint64(v_lhs_1001_, sizeof(void*)*4);
v___y_1013_ = v_hashCode_1025_;
goto v___jp_1012_;
}
}
v___jp_1005_:
{
uint64_t v___x_1008_; uint64_t v___x_1009_; uint64_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = lean_uint64_mix_hash(v___y_1006_, v___y_1007_);
v___x_1009_ = lean_uint64_mix_hash(v___x_1004_, v___x_1008_);
v___x_1010_ = lean_uint64_mix_hash(v___x_1003_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_1011_, 0, v_l_998_);
lean_ctor_set(v___x_1011_, 1, v_r_999_);
lean_ctor_set(v___x_1011_, 2, v_w_1000_);
lean_ctor_set(v___x_1011_, 3, v_lhs_1001_);
lean_ctor_set(v___x_1011_, 4, v_rhs_1002_);
lean_ctor_set_uint64(v___x_1011_, sizeof(void*)*5, v___x_1010_);
return v___x_1011_;
}
v___jp_1012_:
{
switch(lean_obj_tag(v_rhs_1002_))
{
case 0:
{
uint64_t v_hashCode_1014_; 
v_hashCode_1014_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*2);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1014_;
goto v___jp_1005_;
}
case 1:
{
uint64_t v_hashCode_1015_; 
v_hashCode_1015_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*2);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1015_;
goto v___jp_1005_;
}
case 3:
{
uint64_t v_hashCode_1016_; 
v_hashCode_1016_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*3);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1016_;
goto v___jp_1005_;
}
case 4:
{
uint64_t v_hashCode_1017_; 
v_hashCode_1017_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*3);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1017_;
goto v___jp_1005_;
}
case 5:
{
uint64_t v_hashCode_1018_; 
v_hashCode_1018_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*5);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1018_;
goto v___jp_1005_;
}
default: 
{
uint64_t v_hashCode_1019_; 
v_hashCode_1019_ = lean_ctor_get_uint64(v_rhs_1002_, sizeof(void*)*4);
v___y_1006_ = v___y_1013_;
v___y_1007_ = v_hashCode_1019_;
goto v___jp_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_1026_, lean_object* v_r_1027_, lean_object* v_w_1028_, lean_object* v_lhs_1029_, lean_object* v_rhs_1030_, lean_object* v_h_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_1026_, v_r_1027_, v_w_1028_, v_lhs_1029_, v_rhs_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_1033_, lean_object* v_w_x27_1034_, lean_object* v_n_1035_, lean_object* v_expr_1036_){
_start:
{
uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___y_1041_; 
v___x_1037_ = 23ULL;
v___x_1038_ = lean_uint64_of_nat(v_w_x27_1034_);
v___x_1039_ = lean_uint64_of_nat(v_n_1035_);
switch(lean_obj_tag(v_expr_1036_))
{
case 0:
{
uint64_t v_hashCode_1046_; 
v_hashCode_1046_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*2);
v___y_1041_ = v_hashCode_1046_;
goto v___jp_1040_;
}
case 1:
{
uint64_t v_hashCode_1047_; 
v_hashCode_1047_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*2);
v___y_1041_ = v_hashCode_1047_;
goto v___jp_1040_;
}
case 3:
{
uint64_t v_hashCode_1048_; 
v_hashCode_1048_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*3);
v___y_1041_ = v_hashCode_1048_;
goto v___jp_1040_;
}
case 4:
{
uint64_t v_hashCode_1049_; 
v_hashCode_1049_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*3);
v___y_1041_ = v_hashCode_1049_;
goto v___jp_1040_;
}
case 5:
{
uint64_t v_hashCode_1050_; 
v_hashCode_1050_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*5);
v___y_1041_ = v_hashCode_1050_;
goto v___jp_1040_;
}
default: 
{
uint64_t v_hashCode_1051_; 
v_hashCode_1051_ = lean_ctor_get_uint64(v_expr_1036_, sizeof(void*)*4);
v___y_1041_ = v_hashCode_1051_;
goto v___jp_1040_;
}
}
v___jp_1040_:
{
uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_uint64_mix_hash(v___x_1039_, v___y_1041_);
v___x_1043_ = lean_uint64_mix_hash(v___x_1038_, v___x_1042_);
v___x_1044_ = lean_uint64_mix_hash(v___x_1037_, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1045_, 0, v_w_1033_);
lean_ctor_set(v___x_1045_, 1, v_w_x27_1034_);
lean_ctor_set(v___x_1045_, 2, v_n_1035_);
lean_ctor_set(v___x_1045_, 3, v_expr_1036_);
lean_ctor_set_uint64(v___x_1045_, sizeof(void*)*4, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1052_, lean_object* v_w_x27_1053_, lean_object* v_n_1054_, lean_object* v_expr_1055_, lean_object* v_h_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1052_, v_w_x27_1053_, v_n_1054_, v_expr_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1058_, lean_object* v_n_1059_, lean_object* v_lhs_1060_, lean_object* v_rhs_1061_){
_start:
{
uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v___y_1065_; uint64_t v___y_1066_; uint64_t v___y_1072_; 
v___x_1062_ = 29ULL;
v___x_1063_ = lean_uint64_of_nat(v_m_1058_);
switch(lean_obj_tag(v_lhs_1060_))
{
case 0:
{
uint64_t v_hashCode_1079_; 
v_hashCode_1079_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*2);
v___y_1072_ = v_hashCode_1079_;
goto v___jp_1071_;
}
case 1:
{
uint64_t v_hashCode_1080_; 
v_hashCode_1080_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*2);
v___y_1072_ = v_hashCode_1080_;
goto v___jp_1071_;
}
case 3:
{
uint64_t v_hashCode_1081_; 
v_hashCode_1081_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*3);
v___y_1072_ = v_hashCode_1081_;
goto v___jp_1071_;
}
case 4:
{
uint64_t v_hashCode_1082_; 
v_hashCode_1082_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*3);
v___y_1072_ = v_hashCode_1082_;
goto v___jp_1071_;
}
case 5:
{
uint64_t v_hashCode_1083_; 
v_hashCode_1083_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*5);
v___y_1072_ = v_hashCode_1083_;
goto v___jp_1071_;
}
default: 
{
uint64_t v_hashCode_1084_; 
v_hashCode_1084_ = lean_ctor_get_uint64(v_lhs_1060_, sizeof(void*)*4);
v___y_1072_ = v_hashCode_1084_;
goto v___jp_1071_;
}
}
v___jp_1064_:
{
uint64_t v___x_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = lean_uint64_mix_hash(v___y_1065_, v___y_1066_);
v___x_1068_ = lean_uint64_mix_hash(v___x_1063_, v___x_1067_);
v___x_1069_ = lean_uint64_mix_hash(v___x_1062_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1070_, 0, v_m_1058_);
lean_ctor_set(v___x_1070_, 1, v_n_1059_);
lean_ctor_set(v___x_1070_, 2, v_lhs_1060_);
lean_ctor_set(v___x_1070_, 3, v_rhs_1061_);
lean_ctor_set_uint64(v___x_1070_, sizeof(void*)*4, v___x_1069_);
return v___x_1070_;
}
v___jp_1071_:
{
switch(lean_obj_tag(v_rhs_1061_))
{
case 0:
{
uint64_t v_hashCode_1073_; 
v_hashCode_1073_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*2);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1073_;
goto v___jp_1064_;
}
case 1:
{
uint64_t v_hashCode_1074_; 
v_hashCode_1074_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*2);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1074_;
goto v___jp_1064_;
}
case 3:
{
uint64_t v_hashCode_1075_; 
v_hashCode_1075_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*3);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1075_;
goto v___jp_1064_;
}
case 4:
{
uint64_t v_hashCode_1076_; 
v_hashCode_1076_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*3);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1076_;
goto v___jp_1064_;
}
case 5:
{
uint64_t v_hashCode_1077_; 
v_hashCode_1077_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*5);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1077_;
goto v___jp_1064_;
}
default: 
{
uint64_t v_hashCode_1078_; 
v_hashCode_1078_ = lean_ctor_get_uint64(v_rhs_1061_, sizeof(void*)*4);
v___y_1065_ = v___y_1072_;
v___y_1066_ = v_hashCode_1078_;
goto v___jp_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1085_, lean_object* v_n_1086_, lean_object* v_lhs_1087_, lean_object* v_rhs_1088_){
_start:
{
uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___y_1092_; uint64_t v___y_1093_; uint64_t v___y_1099_; 
v___x_1089_ = 31ULL;
v___x_1090_ = lean_uint64_of_nat(v_m_1085_);
switch(lean_obj_tag(v_lhs_1087_))
{
case 0:
{
uint64_t v_hashCode_1106_; 
v_hashCode_1106_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*2);
v___y_1099_ = v_hashCode_1106_;
goto v___jp_1098_;
}
case 1:
{
uint64_t v_hashCode_1107_; 
v_hashCode_1107_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*2);
v___y_1099_ = v_hashCode_1107_;
goto v___jp_1098_;
}
case 3:
{
uint64_t v_hashCode_1108_; 
v_hashCode_1108_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*3);
v___y_1099_ = v_hashCode_1108_;
goto v___jp_1098_;
}
case 4:
{
uint64_t v_hashCode_1109_; 
v_hashCode_1109_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*3);
v___y_1099_ = v_hashCode_1109_;
goto v___jp_1098_;
}
case 5:
{
uint64_t v_hashCode_1110_; 
v_hashCode_1110_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*5);
v___y_1099_ = v_hashCode_1110_;
goto v___jp_1098_;
}
default: 
{
uint64_t v_hashCode_1111_; 
v_hashCode_1111_ = lean_ctor_get_uint64(v_lhs_1087_, sizeof(void*)*4);
v___y_1099_ = v_hashCode_1111_;
goto v___jp_1098_;
}
}
v___jp_1091_:
{
uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_uint64_mix_hash(v___y_1092_, v___y_1093_);
v___x_1095_ = lean_uint64_mix_hash(v___x_1090_, v___x_1094_);
v___x_1096_ = lean_uint64_mix_hash(v___x_1089_, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1097_, 0, v_m_1085_);
lean_ctor_set(v___x_1097_, 1, v_n_1086_);
lean_ctor_set(v___x_1097_, 2, v_lhs_1087_);
lean_ctor_set(v___x_1097_, 3, v_rhs_1088_);
lean_ctor_set_uint64(v___x_1097_, sizeof(void*)*4, v___x_1096_);
return v___x_1097_;
}
v___jp_1098_:
{
switch(lean_obj_tag(v_rhs_1088_))
{
case 0:
{
uint64_t v_hashCode_1100_; 
v_hashCode_1100_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*2);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1100_;
goto v___jp_1091_;
}
case 1:
{
uint64_t v_hashCode_1101_; 
v_hashCode_1101_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*2);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1101_;
goto v___jp_1091_;
}
case 3:
{
uint64_t v_hashCode_1102_; 
v_hashCode_1102_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*3);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1102_;
goto v___jp_1091_;
}
case 4:
{
uint64_t v_hashCode_1103_; 
v_hashCode_1103_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*3);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1103_;
goto v___jp_1091_;
}
case 5:
{
uint64_t v_hashCode_1104_; 
v_hashCode_1104_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*5);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1104_;
goto v___jp_1091_;
}
default: 
{
uint64_t v_hashCode_1105_; 
v_hashCode_1105_ = lean_ctor_get_uint64(v_rhs_1088_, sizeof(void*)*4);
v___y_1092_ = v___y_1099_;
v___y_1093_ = v_hashCode_1105_;
goto v___jp_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1112_, lean_object* v_n_1113_, lean_object* v_lhs_1114_, lean_object* v_rhs_1115_){
_start:
{
uint64_t v___x_1116_; uint64_t v___x_1117_; uint64_t v___y_1119_; uint64_t v___y_1120_; uint64_t v___y_1126_; 
v___x_1116_ = 37ULL;
v___x_1117_ = lean_uint64_of_nat(v_m_1112_);
switch(lean_obj_tag(v_lhs_1114_))
{
case 0:
{
uint64_t v_hashCode_1133_; 
v_hashCode_1133_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*2);
v___y_1126_ = v_hashCode_1133_;
goto v___jp_1125_;
}
case 1:
{
uint64_t v_hashCode_1134_; 
v_hashCode_1134_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*2);
v___y_1126_ = v_hashCode_1134_;
goto v___jp_1125_;
}
case 3:
{
uint64_t v_hashCode_1135_; 
v_hashCode_1135_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*3);
v___y_1126_ = v_hashCode_1135_;
goto v___jp_1125_;
}
case 4:
{
uint64_t v_hashCode_1136_; 
v_hashCode_1136_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*3);
v___y_1126_ = v_hashCode_1136_;
goto v___jp_1125_;
}
case 5:
{
uint64_t v_hashCode_1137_; 
v_hashCode_1137_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*5);
v___y_1126_ = v_hashCode_1137_;
goto v___jp_1125_;
}
default: 
{
uint64_t v_hashCode_1138_; 
v_hashCode_1138_ = lean_ctor_get_uint64(v_lhs_1114_, sizeof(void*)*4);
v___y_1126_ = v_hashCode_1138_;
goto v___jp_1125_;
}
}
v___jp_1118_:
{
uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1121_ = lean_uint64_mix_hash(v___y_1119_, v___y_1120_);
v___x_1122_ = lean_uint64_mix_hash(v___x_1117_, v___x_1121_);
v___x_1123_ = lean_uint64_mix_hash(v___x_1116_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1124_, 0, v_m_1112_);
lean_ctor_set(v___x_1124_, 1, v_n_1113_);
lean_ctor_set(v___x_1124_, 2, v_lhs_1114_);
lean_ctor_set(v___x_1124_, 3, v_rhs_1115_);
lean_ctor_set_uint64(v___x_1124_, sizeof(void*)*4, v___x_1123_);
return v___x_1124_;
}
v___jp_1125_:
{
switch(lean_obj_tag(v_rhs_1115_))
{
case 0:
{
uint64_t v_hashCode_1127_; 
v_hashCode_1127_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*2);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1127_;
goto v___jp_1118_;
}
case 1:
{
uint64_t v_hashCode_1128_; 
v_hashCode_1128_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*2);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1128_;
goto v___jp_1118_;
}
case 3:
{
uint64_t v_hashCode_1129_; 
v_hashCode_1129_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*3);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1129_;
goto v___jp_1118_;
}
case 4:
{
uint64_t v_hashCode_1130_; 
v_hashCode_1130_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*3);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1130_;
goto v___jp_1118_;
}
case 5:
{
uint64_t v_hashCode_1131_; 
v_hashCode_1131_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*5);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1131_;
goto v___jp_1118_;
}
default: 
{
uint64_t v_hashCode_1132_; 
v_hashCode_1132_ = lean_ctor_get_uint64(v_rhs_1115_, sizeof(void*)*4);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v_hashCode_1132_;
goto v___jp_1118_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1139_){
_start:
{
switch(lean_obj_tag(v_x_1139_))
{
case 0:
{
uint64_t v_hashCode_1140_; 
v_hashCode_1140_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*2);
return v_hashCode_1140_;
}
case 1:
{
uint64_t v_hashCode_1141_; 
v_hashCode_1141_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*2);
return v_hashCode_1141_;
}
case 3:
{
uint64_t v_hashCode_1142_; 
v_hashCode_1142_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*3);
return v_hashCode_1142_;
}
case 4:
{
uint64_t v_hashCode_1143_; 
v_hashCode_1143_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*3);
return v_hashCode_1143_;
}
case 5:
{
uint64_t v_hashCode_1144_; 
v_hashCode_1144_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*5);
return v_hashCode_1144_;
}
default: 
{
uint64_t v_hashCode_1145_; 
v_hashCode_1145_ = lean_ctor_get_uint64(v_x_1139_, sizeof(void*)*4);
return v_hashCode_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* v_x_1146_){
_start:
{
uint64_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1146_);
lean_dec_ref(v_x_1146_);
v_r_1148_ = lean_box_uint64(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1149_, lean_object* v_x_1150_){
_start:
{
switch(lean_obj_tag(v_x_1150_))
{
case 0:
{
uint64_t v_hashCode_1151_; 
v_hashCode_1151_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*2);
return v_hashCode_1151_;
}
case 1:
{
uint64_t v_hashCode_1152_; 
v_hashCode_1152_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*2);
return v_hashCode_1152_;
}
case 3:
{
uint64_t v_hashCode_1153_; 
v_hashCode_1153_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*3);
return v_hashCode_1153_;
}
case 4:
{
uint64_t v_hashCode_1154_; 
v_hashCode_1154_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*3);
return v_hashCode_1154_;
}
case 5:
{
uint64_t v_hashCode_1155_; 
v_hashCode_1155_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*5);
return v_hashCode_1155_;
}
default: 
{
uint64_t v_hashCode_1156_; 
v_hashCode_1156_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*4);
return v_hashCode_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1157_, lean_object* v_x_1158_){
_start:
{
uint64_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1157_, v_x_1158_);
lean_dec_ref(v_x_1158_);
lean_dec(v_a_1157_);
v_r_1160_ = lean_box_uint64(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object* v_expr_1161_){
_start:
{
switch(lean_obj_tag(v_expr_1161_))
{
case 0:
{
uint64_t v_hashCode_1162_; 
v_hashCode_1162_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*2);
return v_hashCode_1162_;
}
case 1:
{
uint64_t v_hashCode_1163_; 
v_hashCode_1163_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*2);
return v_hashCode_1163_;
}
case 3:
{
uint64_t v_hashCode_1164_; 
v_hashCode_1164_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*3);
return v_hashCode_1164_;
}
case 4:
{
uint64_t v_hashCode_1165_; 
v_hashCode_1165_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*3);
return v_hashCode_1165_;
}
case 5:
{
uint64_t v_hashCode_1166_; 
v_hashCode_1166_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*5);
return v_hashCode_1166_;
}
default: 
{
uint64_t v_hashCode_1167_; 
v_hashCode_1167_ = lean_ctor_get_uint64(v_expr_1161_, sizeof(void*)*4);
return v_hashCode_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object* v_expr_1168_){
_start:
{
uint64_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(v_expr_1168_);
lean_dec_ref(v_expr_1168_);
v_r_1170_ = lean_box_uint64(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1172_){
_start:
{
lean_object* v___f_1173_; 
v___f_1173_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0));
return v___f_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* v_w_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_1174_);
lean_dec(v_w_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1176_, lean_object* v_r_1177_){
_start:
{
size_t v___x_1178_; size_t v___x_1179_; uint8_t v___x_1180_; uint64_t v___y_1182_; uint64_t v___y_1183_; uint64_t v___y_1264_; 
v___x_1178_ = lean_ptr_addr(v_l_1176_);
v___x_1179_ = lean_ptr_addr(v_r_1177_);
v___x_1180_ = lean_usize_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
switch(lean_obj_tag(v_l_1176_))
{
case 0:
{
uint64_t v_hashCode_1271_; 
v_hashCode_1271_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*2);
v___y_1264_ = v_hashCode_1271_;
goto v___jp_1263_;
}
case 1:
{
uint64_t v_hashCode_1272_; 
v_hashCode_1272_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*2);
v___y_1264_ = v_hashCode_1272_;
goto v___jp_1263_;
}
case 3:
{
uint64_t v_hashCode_1273_; 
v_hashCode_1273_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*3);
v___y_1264_ = v_hashCode_1273_;
goto v___jp_1263_;
}
case 4:
{
uint64_t v_hashCode_1274_; 
v_hashCode_1274_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*3);
v___y_1264_ = v_hashCode_1274_;
goto v___jp_1263_;
}
case 5:
{
uint64_t v_hashCode_1275_; 
v_hashCode_1275_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*5);
v___y_1264_ = v_hashCode_1275_;
goto v___jp_1263_;
}
default: 
{
uint64_t v_hashCode_1276_; 
v_hashCode_1276_ = lean_ctor_get_uint64(v_l_1176_, sizeof(void*)*4);
v___y_1264_ = v_hashCode_1276_;
goto v___jp_1263_;
}
}
}
else
{
return v___x_1180_;
}
v___jp_1181_:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_uint64_dec_eq(v___y_1182_, v___y_1183_);
if (v___x_1184_ == 0)
{
return v___x_1180_;
}
else
{
if (v___x_1180_ == 0)
{
switch(lean_obj_tag(v_l_1176_))
{
case 0:
{
if (lean_obj_tag(v_r_1177_) == 0)
{
lean_object* v_idx_1185_; lean_object* v_idx_1186_; uint8_t v___x_1187_; 
v_idx_1185_ = lean_ctor_get(v_l_1176_, 1);
v_idx_1186_ = lean_ctor_get(v_r_1177_, 1);
v___x_1187_ = lean_nat_dec_eq(v_idx_1185_, v_idx_1186_);
return v___x_1187_;
}
else
{
return v___x_1180_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1177_) == 1)
{
lean_object* v_val_1188_; lean_object* v_val_1189_; uint8_t v___x_1190_; 
v_val_1188_ = lean_ctor_get(v_l_1176_, 1);
v_val_1189_ = lean_ctor_get(v_r_1177_, 1);
v___x_1190_ = lean_nat_dec_eq(v_val_1188_, v_val_1189_);
return v___x_1190_;
}
else
{
return v___x_1180_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1177_) == 2)
{
lean_object* v_w_1191_; lean_object* v_start_1192_; lean_object* v_expr_1193_; lean_object* v_w_1194_; lean_object* v_start_1195_; lean_object* v_expr_1196_; uint8_t v___x_1197_; 
v_w_1191_ = lean_ctor_get(v_l_1176_, 0);
v_start_1192_ = lean_ctor_get(v_l_1176_, 1);
v_expr_1193_ = lean_ctor_get(v_l_1176_, 3);
v_w_1194_ = lean_ctor_get(v_r_1177_, 0);
v_start_1195_ = lean_ctor_get(v_r_1177_, 1);
v_expr_1196_ = lean_ctor_get(v_r_1177_, 3);
v___x_1197_ = lean_nat_dec_eq(v_w_1191_, v_w_1194_);
if (v___x_1197_ == 0)
{
return v___x_1197_;
}
else
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_eq(v_start_1192_, v_start_1195_);
if (v___x_1198_ == 0)
{
return v___x_1198_;
}
else
{
v_l_1176_ = v_expr_1193_;
v_r_1177_ = v_expr_1196_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1177_) == 3)
{
lean_object* v_lhs_1200_; uint8_t v_op_1201_; lean_object* v_rhs_1202_; lean_object* v_lhs_1203_; uint8_t v_op_1204_; lean_object* v_rhs_1205_; uint8_t v___x_1206_; 
v_lhs_1200_ = lean_ctor_get(v_l_1176_, 1);
v_op_1201_ = lean_ctor_get_uint8(v_l_1176_, sizeof(void*)*3 + 8);
v_rhs_1202_ = lean_ctor_get(v_l_1176_, 2);
v_lhs_1203_ = lean_ctor_get(v_r_1177_, 1);
v_op_1204_ = lean_ctor_get_uint8(v_r_1177_, sizeof(void*)*3 + 8);
v_rhs_1205_ = lean_ctor_get(v_r_1177_, 2);
v___x_1206_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_op_1201_, v_op_1204_);
if (v___x_1206_ == 0)
{
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1200_, v_lhs_1203_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
v_l_1176_ = v_rhs_1202_;
v_r_1177_ = v_rhs_1205_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1177_) == 4)
{
lean_object* v_op_1209_; lean_object* v_operand_1210_; lean_object* v_op_1211_; lean_object* v_operand_1212_; uint8_t v___x_1213_; 
v_op_1209_ = lean_ctor_get(v_l_1176_, 1);
v_operand_1210_ = lean_ctor_get(v_l_1176_, 2);
v_op_1211_ = lean_ctor_get(v_r_1177_, 1);
v_operand_1212_ = lean_ctor_get(v_r_1177_, 2);
v___x_1213_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1209_, v_op_1211_);
if (v___x_1213_ == 0)
{
return v___x_1213_;
}
else
{
v_l_1176_ = v_operand_1210_;
v_r_1177_ = v_operand_1212_;
goto _start;
}
}
else
{
return v___x_1180_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1177_) == 5)
{
lean_object* v_l_1215_; lean_object* v_r_1216_; lean_object* v_lhs_1217_; lean_object* v_rhs_1218_; lean_object* v_l_1219_; lean_object* v_r_1220_; lean_object* v_lhs_1221_; lean_object* v_rhs_1222_; uint8_t v___x_1223_; 
v_l_1215_ = lean_ctor_get(v_l_1176_, 0);
v_r_1216_ = lean_ctor_get(v_l_1176_, 1);
v_lhs_1217_ = lean_ctor_get(v_l_1176_, 3);
v_rhs_1218_ = lean_ctor_get(v_l_1176_, 4);
v_l_1219_ = lean_ctor_get(v_r_1177_, 0);
v_r_1220_ = lean_ctor_get(v_r_1177_, 1);
v_lhs_1221_ = lean_ctor_get(v_r_1177_, 3);
v_rhs_1222_ = lean_ctor_get(v_r_1177_, 4);
v___x_1223_ = lean_nat_dec_eq(v_l_1215_, v_l_1219_);
if (v___x_1223_ == 0)
{
return v___x_1223_;
}
else
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_nat_dec_eq(v_r_1216_, v_r_1220_);
if (v___x_1224_ == 0)
{
return v___x_1224_;
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1217_, v_lhs_1221_);
if (v___x_1225_ == 0)
{
return v___x_1225_;
}
else
{
v_l_1176_ = v_rhs_1218_;
v_r_1177_ = v_rhs_1222_;
goto _start;
}
}
}
}
else
{
return v___x_1180_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1177_) == 6)
{
lean_object* v_w_1227_; lean_object* v_n_1228_; lean_object* v_expr_1229_; lean_object* v_w_1230_; lean_object* v_n_1231_; lean_object* v_expr_1232_; uint8_t v___x_1233_; 
v_w_1227_ = lean_ctor_get(v_l_1176_, 0);
v_n_1228_ = lean_ctor_get(v_l_1176_, 2);
v_expr_1229_ = lean_ctor_get(v_l_1176_, 3);
v_w_1230_ = lean_ctor_get(v_r_1177_, 0);
v_n_1231_ = lean_ctor_get(v_r_1177_, 2);
v_expr_1232_ = lean_ctor_get(v_r_1177_, 3);
v___x_1233_ = lean_nat_dec_eq(v_n_1228_, v_n_1231_);
if (v___x_1233_ == 0)
{
return v___x_1233_;
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_eq(v_w_1227_, v_w_1230_);
if (v___x_1234_ == 0)
{
return v___x_1234_;
}
else
{
v_l_1176_ = v_expr_1229_;
v_r_1177_ = v_expr_1232_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1177_) == 7)
{
lean_object* v_n_1236_; lean_object* v_lhs_1237_; lean_object* v_rhs_1238_; lean_object* v_n_1239_; lean_object* v_lhs_1240_; lean_object* v_rhs_1241_; uint8_t v___x_1242_; 
v_n_1236_ = lean_ctor_get(v_l_1176_, 1);
v_lhs_1237_ = lean_ctor_get(v_l_1176_, 2);
v_rhs_1238_ = lean_ctor_get(v_l_1176_, 3);
v_n_1239_ = lean_ctor_get(v_r_1177_, 1);
v_lhs_1240_ = lean_ctor_get(v_r_1177_, 2);
v_rhs_1241_ = lean_ctor_get(v_r_1177_, 3);
v___x_1242_ = lean_nat_dec_eq(v_n_1236_, v_n_1239_);
if (v___x_1242_ == 0)
{
return v___x_1242_;
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1237_, v_lhs_1240_);
if (v___x_1243_ == 0)
{
return v___x_1243_;
}
else
{
v_l_1176_ = v_rhs_1238_;
v_r_1177_ = v_rhs_1241_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1177_) == 8)
{
lean_object* v_n_1245_; lean_object* v_lhs_1246_; lean_object* v_rhs_1247_; lean_object* v_n_1248_; lean_object* v_lhs_1249_; lean_object* v_rhs_1250_; uint8_t v___x_1251_; 
v_n_1245_ = lean_ctor_get(v_l_1176_, 1);
v_lhs_1246_ = lean_ctor_get(v_l_1176_, 2);
v_rhs_1247_ = lean_ctor_get(v_l_1176_, 3);
v_n_1248_ = lean_ctor_get(v_r_1177_, 1);
v_lhs_1249_ = lean_ctor_get(v_r_1177_, 2);
v_rhs_1250_ = lean_ctor_get(v_r_1177_, 3);
v___x_1251_ = lean_nat_dec_eq(v_n_1245_, v_n_1248_);
if (v___x_1251_ == 0)
{
return v___x_1251_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1246_, v_lhs_1249_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
v_l_1176_ = v_rhs_1247_;
v_r_1177_ = v_rhs_1250_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
default: 
{
if (lean_obj_tag(v_r_1177_) == 9)
{
lean_object* v_n_1254_; lean_object* v_lhs_1255_; lean_object* v_rhs_1256_; lean_object* v_n_1257_; lean_object* v_lhs_1258_; lean_object* v_rhs_1259_; uint8_t v___x_1260_; 
v_n_1254_ = lean_ctor_get(v_l_1176_, 1);
v_lhs_1255_ = lean_ctor_get(v_l_1176_, 2);
v_rhs_1256_ = lean_ctor_get(v_l_1176_, 3);
v_n_1257_ = lean_ctor_get(v_r_1177_, 1);
v_lhs_1258_ = lean_ctor_get(v_r_1177_, 2);
v_rhs_1259_ = lean_ctor_get(v_r_1177_, 3);
v___x_1260_ = lean_nat_dec_eq(v_n_1254_, v_n_1257_);
if (v___x_1260_ == 0)
{
return v___x_1260_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1255_, v_lhs_1258_);
if (v___x_1261_ == 0)
{
return v___x_1261_;
}
else
{
v_l_1176_ = v_rhs_1256_;
v_r_1177_ = v_rhs_1259_;
goto _start;
}
}
}
else
{
return v___x_1180_;
}
}
}
}
else
{
return v___x_1180_;
}
}
}
v___jp_1263_:
{
switch(lean_obj_tag(v_r_1177_))
{
case 0:
{
uint64_t v_hashCode_1265_; 
v_hashCode_1265_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*2);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1265_;
goto v___jp_1181_;
}
case 1:
{
uint64_t v_hashCode_1266_; 
v_hashCode_1266_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*2);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1266_;
goto v___jp_1181_;
}
case 3:
{
uint64_t v_hashCode_1267_; 
v_hashCode_1267_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*3);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1267_;
goto v___jp_1181_;
}
case 4:
{
uint64_t v_hashCode_1268_; 
v_hashCode_1268_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*3);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1268_;
goto v___jp_1181_;
}
case 5:
{
uint64_t v_hashCode_1269_; 
v_hashCode_1269_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*5);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1269_;
goto v___jp_1181_;
}
default: 
{
uint64_t v_hashCode_1270_; 
v_hashCode_1270_ = lean_ctor_get_uint64(v_r_1177_, sizeof(void*)*4);
v___y_1182_ = v___y_1264_;
v___y_1183_ = v_hashCode_1270_;
goto v___jp_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1277_, lean_object* v_r_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1277_, v_r_1278_);
lean_dec_ref(v_r_1278_);
lean_dec_ref(v_l_1277_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1281_, lean_object* v_l_1282_, lean_object* v_r_1283_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1282_, v_r_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1285_, lean_object* v_l_1286_, lean_object* v_r_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1285_, v_l_1286_, v_r_1287_);
lean_dec_ref(v_r_1287_);
lean_dec_ref(v_l_1286_);
lean_dec(v_w_1285_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1299_, lean_object* v_x_1300_){
_start:
{
switch(lean_obj_tag(v_x_1300_))
{
case 0:
{
lean_object* v_idx_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_w_1299_);
v_idx_1301_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_idx_1301_);
lean_dec_ref(v_x_1300_);
v___x_1302_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1303_ = l_Nat_reprFast(v_idx_1301_);
v___x_1304_ = lean_string_append(v___x_1302_, v___x_1303_);
lean_dec_ref(v___x_1303_);
return v___x_1304_;
}
case 1:
{
lean_object* v_val_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_val_1305_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_val_1305_);
lean_dec_ref(v_x_1300_);
v___x_1306_ = l_BitVec_repr(v_w_1299_, v_val_1305_);
v___x_1307_ = l_Std_Format_defWidth;
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = l_Std_Format_pretty(v___x_1306_, v___x_1307_, v___x_1308_, v___x_1308_);
return v___x_1309_;
}
case 2:
{
lean_object* v_w_1310_; lean_object* v_start_1311_; lean_object* v_expr_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_w_1310_ = lean_ctor_get(v_x_1300_, 0);
lean_inc(v_w_1310_);
v_start_1311_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_start_1311_);
v_expr_1312_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_expr_1312_);
lean_dec_ref(v_x_1300_);
v___x_1313_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1310_, v_expr_1312_);
v___x_1314_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1315_ = lean_string_append(v___x_1313_, v___x_1314_);
v___x_1316_ = l_Nat_reprFast(v_start_1311_);
v___x_1317_ = lean_string_append(v___x_1315_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1319_ = lean_string_append(v___x_1317_, v___x_1318_);
v___x_1320_ = l_Nat_reprFast(v_w_1299_);
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
return v___x_1323_;
}
case 3:
{
lean_object* v_lhs_1324_; uint8_t v_op_1325_; lean_object* v_rhs_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_lhs_1324_ = lean_ctor_get(v_x_1300_, 1);
lean_inc_ref(v_lhs_1324_);
v_op_1325_ = lean_ctor_get_uint8(v_x_1300_, sizeof(void*)*3 + 8);
v_rhs_1326_ = lean_ctor_get(v_x_1300_, 2);
lean_inc_ref(v_rhs_1326_);
lean_dec_ref(v_x_1300_);
v___x_1327_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1299_);
v___x_1328_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_lhs_1324_);
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
v___x_1332_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1325_);
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = lean_string_append(v___x_1333_, v___x_1330_);
v___x_1335_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_rhs_1326_);
v___x_1336_ = lean_string_append(v___x_1334_, v___x_1335_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
return v___x_1338_;
}
case 4:
{
lean_object* v_op_1339_; lean_object* v_operand_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_op_1339_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_op_1339_);
v_operand_1340_ = lean_ctor_get(v_x_1300_, 2);
lean_inc_ref(v_operand_1340_);
lean_dec_ref(v_x_1300_);
v___x_1341_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1342_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1339_);
v___x_1343_ = lean_string_append(v___x_1341_, v___x_1342_);
lean_dec_ref(v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
v___x_1346_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_operand_1340_);
v___x_1347_ = lean_string_append(v___x_1345_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
return v___x_1349_;
}
case 5:
{
lean_object* v_l_1350_; lean_object* v_r_1351_; lean_object* v_lhs_1352_; lean_object* v_rhs_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_w_1299_);
v_l_1350_ = lean_ctor_get(v_x_1300_, 0);
lean_inc(v_l_1350_);
v_r_1351_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_r_1351_);
v_lhs_1352_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_lhs_1352_);
v_rhs_1353_ = lean_ctor_get(v_x_1300_, 4);
lean_inc_ref(v_rhs_1353_);
lean_dec_ref(v_x_1300_);
v___x_1354_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1355_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1350_, v_lhs_1352_);
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1351_, v_rhs_1353_);
v___x_1360_ = lean_string_append(v___x_1358_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1362_ = lean_string_append(v___x_1360_, v___x_1361_);
return v___x_1362_;
}
case 6:
{
lean_object* v_w_1363_; lean_object* v_n_1364_; lean_object* v_expr_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v_w_1299_);
v_w_1363_ = lean_ctor_get(v_x_1300_, 0);
lean_inc(v_w_1363_);
v_n_1364_ = lean_ctor_get(v_x_1300_, 2);
lean_inc(v_n_1364_);
v_expr_1365_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_expr_1365_);
lean_dec_ref(v_x_1300_);
v___x_1366_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1367_ = l_Nat_reprFast(v_n_1364_);
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
v___x_1371_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1363_, v_expr_1365_);
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
return v___x_1374_;
}
case 7:
{
lean_object* v_n_1375_; lean_object* v_lhs_1376_; lean_object* v_rhs_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_n_1375_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_n_1375_);
v_lhs_1376_ = lean_ctor_get(v_x_1300_, 2);
lean_inc_ref(v_lhs_1376_);
v_rhs_1377_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_rhs_1377_);
lean_dec_ref(v_x_1300_);
v___x_1378_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1379_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_lhs_1376_);
v___x_1380_ = lean_string_append(v___x_1378_, v___x_1379_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
v___x_1383_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1375_, v_rhs_1377_);
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
return v___x_1386_;
}
case 8:
{
lean_object* v_n_1387_; lean_object* v_lhs_1388_; lean_object* v_rhs_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_n_1387_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_n_1387_);
v_lhs_1388_ = lean_ctor_get(v_x_1300_, 2);
lean_inc_ref(v_lhs_1388_);
v_rhs_1389_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_rhs_1389_);
lean_dec_ref(v_x_1300_);
v___x_1390_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1391_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_lhs_1388_);
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
v___x_1395_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1387_, v_rhs_1389_);
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
return v___x_1398_;
}
default: 
{
lean_object* v_n_1399_; lean_object* v_lhs_1400_; lean_object* v_rhs_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_n_1399_ = lean_ctor_get(v_x_1300_, 1);
lean_inc(v_n_1399_);
v_lhs_1400_ = lean_ctor_get(v_x_1300_, 2);
lean_inc_ref(v_lhs_1400_);
v_rhs_1401_ = lean_ctor_get(v_x_1300_, 3);
lean_inc_ref(v_rhs_1401_);
lean_dec_ref(v_x_1300_);
v___x_1402_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1403_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1299_, v_lhs_1400_);
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1406_ = lean_string_append(v___x_1404_, v___x_1405_);
v___x_1407_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1399_, v_rhs_1401_);
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1410_ = lean_string_append(v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1412_, 0, v_w_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1413_, lean_object* v_idx_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_RArray_getImpl___redArg(v_assign_1413_, v_idx_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1416_, lean_object* v_idx_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1416_, v_idx_1417_);
lean_dec(v_idx_1417_);
lean_dec_ref(v_assign_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1419_, lean_object* v_assign_1420_, lean_object* v_x_1421_){
_start:
{
switch(lean_obj_tag(v_x_1421_))
{
case 0:
{
lean_object* v_idx_1422_; lean_object* v_packedBv_1423_; lean_object* v_w_1424_; lean_object* v_bv_1425_; uint8_t v___x_1426_; 
v_idx_1422_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_idx_1422_);
lean_dec_ref(v_x_1421_);
v_packedBv_1423_ = l_Lean_RArray_getImpl___redArg(v_assign_1420_, v_idx_1422_);
lean_dec(v_idx_1422_);
v_w_1424_ = lean_ctor_get(v_packedBv_1423_, 0);
lean_inc(v_w_1424_);
v_bv_1425_ = lean_ctor_get(v_packedBv_1423_, 1);
lean_inc(v_bv_1425_);
lean_dec(v_packedBv_1423_);
v___x_1426_ = lean_nat_dec_eq(v_w_1424_, v_w_1419_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
v___x_1427_ = l_BitVec_setWidth(v_w_1424_, v_w_1419_, v_bv_1425_);
lean_dec(v_bv_1425_);
lean_dec(v_w_1419_);
lean_dec(v_w_1424_);
return v___x_1427_;
}
else
{
lean_dec(v_w_1424_);
lean_dec(v_w_1419_);
return v_bv_1425_;
}
}
case 1:
{
lean_object* v_val_1428_; 
lean_dec(v_w_1419_);
v_val_1428_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_val_1428_);
lean_dec_ref(v_x_1421_);
return v_val_1428_;
}
case 2:
{
lean_object* v_w_1429_; lean_object* v_start_1430_; lean_object* v_expr_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_w_1429_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_w_1429_);
v_start_1430_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_start_1430_);
v_expr_1431_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_expr_1431_);
lean_dec_ref(v_x_1421_);
v___x_1432_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1429_, v_assign_1420_, v_expr_1431_);
v___x_1433_ = l_BitVec_extractLsb_x27___redArg(v_start_1430_, v_w_1419_, v___x_1432_);
lean_dec(v___x_1432_);
lean_dec(v_w_1419_);
lean_dec(v_start_1430_);
return v___x_1433_;
}
case 3:
{
lean_object* v_lhs_1434_; uint8_t v_op_1435_; lean_object* v_rhs_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_lhs_1434_ = lean_ctor_get(v_x_1421_, 1);
lean_inc_ref(v_lhs_1434_);
v_op_1435_ = lean_ctor_get_uint8(v_x_1421_, sizeof(void*)*3 + 8);
v_rhs_1436_ = lean_ctor_get(v_x_1421_, 2);
lean_inc_ref(v_rhs_1436_);
lean_dec_ref(v_x_1421_);
lean_inc_n(v_w_1419_, 2);
v___x_1437_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_lhs_1434_);
v___x_1438_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_rhs_1436_);
v___x_1439_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1419_, v_op_1435_, v___x_1437_, v___x_1438_);
lean_dec(v___x_1438_);
lean_dec(v___x_1437_);
lean_dec(v_w_1419_);
return v___x_1439_;
}
case 4:
{
lean_object* v_op_1440_; lean_object* v_operand_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_op_1440_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_op_1440_);
v_operand_1441_ = lean_ctor_get(v_x_1421_, 2);
lean_inc_ref(v_operand_1441_);
lean_dec_ref(v_x_1421_);
lean_inc(v_w_1419_);
v___x_1442_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_operand_1441_);
v___x_1443_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1419_, v_op_1440_, v___x_1442_);
lean_dec(v_op_1440_);
return v___x_1443_;
}
case 5:
{
lean_object* v_l_1444_; lean_object* v_r_1445_; lean_object* v_lhs_1446_; lean_object* v_rhs_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_w_1419_);
v_l_1444_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_l_1444_);
v_r_1445_ = lean_ctor_get(v_x_1421_, 1);
lean_inc_n(v_r_1445_, 2);
v_lhs_1446_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_lhs_1446_);
v_rhs_1447_ = lean_ctor_get(v_x_1421_, 4);
lean_inc_ref(v_rhs_1447_);
lean_dec_ref(v_x_1421_);
v___x_1448_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1444_, v_assign_1420_, v_lhs_1446_);
v___x_1449_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1445_, v_assign_1420_, v_rhs_1447_);
v___x_1450_ = l_BitVec_append___redArg(v_r_1445_, v___x_1448_, v___x_1449_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_dec(v_r_1445_);
return v___x_1450_;
}
case 6:
{
lean_object* v_w_1451_; lean_object* v_n_1452_; lean_object* v_expr_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v_w_1419_);
v_w_1451_ = lean_ctor_get(v_x_1421_, 0);
lean_inc_n(v_w_1451_, 2);
v_n_1452_ = lean_ctor_get(v_x_1421_, 2);
lean_inc(v_n_1452_);
v_expr_1453_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_expr_1453_);
lean_dec_ref(v_x_1421_);
v___x_1454_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1451_, v_assign_1420_, v_expr_1453_);
v___x_1455_ = l_BitVec_replicate(v_w_1451_, v_n_1452_, v___x_1454_);
lean_dec(v___x_1454_);
lean_dec(v_n_1452_);
lean_dec(v_w_1451_);
return v___x_1455_;
}
case 7:
{
lean_object* v_n_1456_; lean_object* v_lhs_1457_; lean_object* v_rhs_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_n_1456_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_n_1456_);
v_lhs_1457_ = lean_ctor_get(v_x_1421_, 2);
lean_inc_ref(v_lhs_1457_);
v_rhs_1458_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_rhs_1458_);
lean_dec_ref(v_x_1421_);
lean_inc(v_w_1419_);
v___x_1459_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_lhs_1457_);
v___x_1460_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1456_, v_assign_1420_, v_rhs_1458_);
v___x_1461_ = l_BitVec_shiftLeft(v_w_1419_, v___x_1459_, v___x_1460_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v_w_1419_);
return v___x_1461_;
}
case 8:
{
lean_object* v_n_1462_; lean_object* v_lhs_1463_; lean_object* v_rhs_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_n_1462_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_n_1462_);
v_lhs_1463_ = lean_ctor_get(v_x_1421_, 2);
lean_inc_ref(v_lhs_1463_);
v_rhs_1464_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_rhs_1464_);
lean_dec_ref(v_x_1421_);
v___x_1465_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_lhs_1463_);
v___x_1466_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1462_, v_assign_1420_, v_rhs_1464_);
v___x_1467_ = lean_nat_shiftr(v___x_1465_, v___x_1466_);
lean_dec(v___x_1466_);
lean_dec(v___x_1465_);
return v___x_1467_;
}
default: 
{
lean_object* v_n_1468_; lean_object* v_lhs_1469_; lean_object* v_rhs_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_n_1468_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_n_1468_);
v_lhs_1469_ = lean_ctor_get(v_x_1421_, 2);
lean_inc_ref(v_lhs_1469_);
v_rhs_1470_ = lean_ctor_get(v_x_1421_, 3);
lean_inc_ref(v_rhs_1470_);
lean_dec_ref(v_x_1421_);
lean_inc(v_w_1419_);
v___x_1471_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1419_, v_assign_1420_, v_lhs_1469_);
v___x_1472_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1468_, v_assign_1420_, v_rhs_1470_);
v___x_1473_ = l_BitVec_sshiftRight(v_w_1419_, v___x_1471_, v___x_1472_);
lean_dec(v___x_1472_);
lean_dec(v_w_1419_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1474_, lean_object* v_assign_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1474_, v_assign_1475_, v_x_1476_);
lean_dec_ref(v_assign_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* v_w_1478_, lean_object* v_x_1479_, lean_object* v_h__1_1480_, lean_object* v_h__2_1481_, lean_object* v_h__3_1482_, lean_object* v_h__4_1483_, lean_object* v_h__5_1484_, lean_object* v_h__6_1485_, lean_object* v_h__7_1486_, lean_object* v_h__8_1487_, lean_object* v_h__9_1488_, lean_object* v_h__10_1489_){
_start:
{
switch(lean_obj_tag(v_x_1479_))
{
case 0:
{
lean_object* v_idx_1490_; lean_object* v___x_1491_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
v_idx_1490_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_idx_1490_);
lean_dec_ref(v_x_1479_);
v___x_1491_ = lean_apply_2(v_h__1_1480_, v_w_1478_, v_idx_1490_);
return v___x_1491_;
}
case 1:
{
lean_object* v_val_1492_; lean_object* v___x_1493_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__1_1480_);
v_val_1492_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_val_1492_);
lean_dec_ref(v_x_1479_);
v___x_1493_ = lean_apply_2(v_h__2_1481_, v_w_1478_, v_val_1492_);
return v___x_1493_;
}
case 2:
{
lean_object* v_w_1494_; lean_object* v_start_1495_; lean_object* v_expr_1496_; lean_object* v___x_1497_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_w_1494_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_w_1494_);
v_start_1495_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_start_1495_);
v_expr_1496_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_expr_1496_);
lean_dec_ref(v_x_1479_);
v___x_1497_ = lean_apply_4(v_h__3_1482_, v_w_1478_, v_w_1494_, v_start_1495_, v_expr_1496_);
return v___x_1497_;
}
case 3:
{
lean_object* v_lhs_1498_; uint8_t v_op_1499_; lean_object* v_rhs_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_lhs_1498_ = lean_ctor_get(v_x_1479_, 1);
lean_inc_ref(v_lhs_1498_);
v_op_1499_ = lean_ctor_get_uint8(v_x_1479_, sizeof(void*)*3 + 8);
v_rhs_1500_ = lean_ctor_get(v_x_1479_, 2);
lean_inc_ref(v_rhs_1500_);
lean_dec_ref(v_x_1479_);
v___x_1501_ = lean_box(v_op_1499_);
v___x_1502_ = lean_apply_4(v_h__4_1483_, v_w_1478_, v_lhs_1498_, v___x_1501_, v_rhs_1500_);
return v___x_1502_;
}
case 4:
{
lean_object* v_op_1503_; lean_object* v_operand_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_op_1503_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_op_1503_);
v_operand_1504_ = lean_ctor_get(v_x_1479_, 2);
lean_inc_ref(v_operand_1504_);
lean_dec_ref(v_x_1479_);
v___x_1505_ = lean_apply_3(v_h__5_1484_, v_w_1478_, v_op_1503_, v_operand_1504_);
return v___x_1505_;
}
case 5:
{
lean_object* v_l_1506_; lean_object* v_r_1507_; lean_object* v_lhs_1508_; lean_object* v_rhs_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_l_1506_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_l_1506_);
v_r_1507_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_r_1507_);
v_lhs_1508_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_lhs_1508_);
v_rhs_1509_ = lean_ctor_get(v_x_1479_, 4);
lean_inc_ref(v_rhs_1509_);
lean_dec_ref(v_x_1479_);
v___x_1510_ = lean_apply_6(v_h__6_1485_, v_w_1478_, v_l_1506_, v_r_1507_, v_lhs_1508_, v_rhs_1509_, lean_box(0));
return v___x_1510_;
}
case 6:
{
lean_object* v_w_1511_; lean_object* v_n_1512_; lean_object* v_expr_1513_; lean_object* v___x_1514_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_w_1511_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_w_1511_);
v_n_1512_ = lean_ctor_get(v_x_1479_, 2);
lean_inc(v_n_1512_);
v_expr_1513_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_expr_1513_);
lean_dec_ref(v_x_1479_);
v___x_1514_ = lean_apply_5(v_h__7_1486_, v_w_1478_, v_w_1511_, v_n_1512_, v_expr_1513_, lean_box(0));
return v___x_1514_;
}
case 7:
{
lean_object* v_n_1515_; lean_object* v_lhs_1516_; lean_object* v_rhs_1517_; lean_object* v___x_1518_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__9_1488_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_n_1515_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_n_1515_);
v_lhs_1516_ = lean_ctor_get(v_x_1479_, 2);
lean_inc_ref(v_lhs_1516_);
v_rhs_1517_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_rhs_1517_);
lean_dec_ref(v_x_1479_);
v___x_1518_ = lean_apply_4(v_h__8_1487_, v_w_1478_, v_n_1515_, v_lhs_1516_, v_rhs_1517_);
return v___x_1518_;
}
case 8:
{
lean_object* v_n_1519_; lean_object* v_lhs_1520_; lean_object* v_rhs_1521_; lean_object* v___x_1522_; 
lean_dec(v_h__10_1489_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_n_1519_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_n_1519_);
v_lhs_1520_ = lean_ctor_get(v_x_1479_, 2);
lean_inc_ref(v_lhs_1520_);
v_rhs_1521_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_rhs_1521_);
lean_dec_ref(v_x_1479_);
v___x_1522_ = lean_apply_4(v_h__9_1488_, v_w_1478_, v_n_1519_, v_lhs_1520_, v_rhs_1521_);
return v___x_1522_;
}
default: 
{
lean_object* v_n_1523_; lean_object* v_lhs_1524_; lean_object* v_rhs_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__9_1488_);
lean_dec(v_h__8_1487_);
lean_dec(v_h__7_1486_);
lean_dec(v_h__6_1485_);
lean_dec(v_h__5_1484_);
lean_dec(v_h__4_1483_);
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
lean_dec(v_h__1_1480_);
v_n_1523_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_n_1523_);
v_lhs_1524_ = lean_ctor_get(v_x_1479_, 2);
lean_inc_ref(v_lhs_1524_);
v_rhs_1525_ = lean_ctor_get(v_x_1479_, 3);
lean_inc_ref(v_rhs_1525_);
lean_dec_ref(v_x_1479_);
v___x_1526_ = lean_apply_4(v_h__10_1489_, v_w_1478_, v_n_1523_, v_lhs_1524_, v_rhs_1525_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* v_motive_1527_, lean_object* v_w_1528_, lean_object* v_x_1529_, lean_object* v_h__1_1530_, lean_object* v_h__2_1531_, lean_object* v_h__3_1532_, lean_object* v_h__4_1533_, lean_object* v_h__5_1534_, lean_object* v_h__6_1535_, lean_object* v_h__7_1536_, lean_object* v_h__8_1537_, lean_object* v_h__9_1538_, lean_object* v_h__10_1539_){
_start:
{
switch(lean_obj_tag(v_x_1529_))
{
case 0:
{
lean_object* v_idx_1540_; lean_object* v___x_1541_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
v_idx_1540_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_idx_1540_);
lean_dec_ref(v_x_1529_);
v___x_1541_ = lean_apply_2(v_h__1_1530_, v_w_1528_, v_idx_1540_);
return v___x_1541_;
}
case 1:
{
lean_object* v_val_1542_; lean_object* v___x_1543_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__1_1530_);
v_val_1542_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_val_1542_);
lean_dec_ref(v_x_1529_);
v___x_1543_ = lean_apply_2(v_h__2_1531_, v_w_1528_, v_val_1542_);
return v___x_1543_;
}
case 2:
{
lean_object* v_w_1544_; lean_object* v_start_1545_; lean_object* v_expr_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_w_1544_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_w_1544_);
v_start_1545_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_start_1545_);
v_expr_1546_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_expr_1546_);
lean_dec_ref(v_x_1529_);
v___x_1547_ = lean_apply_4(v_h__3_1532_, v_w_1528_, v_w_1544_, v_start_1545_, v_expr_1546_);
return v___x_1547_;
}
case 3:
{
lean_object* v_lhs_1548_; uint8_t v_op_1549_; lean_object* v_rhs_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_lhs_1548_ = lean_ctor_get(v_x_1529_, 1);
lean_inc_ref(v_lhs_1548_);
v_op_1549_ = lean_ctor_get_uint8(v_x_1529_, sizeof(void*)*3 + 8);
v_rhs_1550_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_rhs_1550_);
lean_dec_ref(v_x_1529_);
v___x_1551_ = lean_box(v_op_1549_);
v___x_1552_ = lean_apply_4(v_h__4_1533_, v_w_1528_, v_lhs_1548_, v___x_1551_, v_rhs_1550_);
return v___x_1552_;
}
case 4:
{
lean_object* v_op_1553_; lean_object* v_operand_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_op_1553_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_op_1553_);
v_operand_1554_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_operand_1554_);
lean_dec_ref(v_x_1529_);
v___x_1555_ = lean_apply_3(v_h__5_1534_, v_w_1528_, v_op_1553_, v_operand_1554_);
return v___x_1555_;
}
case 5:
{
lean_object* v_l_1556_; lean_object* v_r_1557_; lean_object* v_lhs_1558_; lean_object* v_rhs_1559_; lean_object* v___x_1560_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_l_1556_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_l_1556_);
v_r_1557_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_r_1557_);
v_lhs_1558_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_lhs_1558_);
v_rhs_1559_ = lean_ctor_get(v_x_1529_, 4);
lean_inc_ref(v_rhs_1559_);
lean_dec_ref(v_x_1529_);
v___x_1560_ = lean_apply_6(v_h__6_1535_, v_w_1528_, v_l_1556_, v_r_1557_, v_lhs_1558_, v_rhs_1559_, lean_box(0));
return v___x_1560_;
}
case 6:
{
lean_object* v_w_1561_; lean_object* v_n_1562_; lean_object* v_expr_1563_; lean_object* v___x_1564_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_w_1561_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_w_1561_);
v_n_1562_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_n_1562_);
v_expr_1563_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_expr_1563_);
lean_dec_ref(v_x_1529_);
v___x_1564_ = lean_apply_5(v_h__7_1536_, v_w_1528_, v_w_1561_, v_n_1562_, v_expr_1563_, lean_box(0));
return v___x_1564_;
}
case 7:
{
lean_object* v_n_1565_; lean_object* v_lhs_1566_; lean_object* v_rhs_1567_; lean_object* v___x_1568_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__9_1538_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_n_1565_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_n_1565_);
v_lhs_1566_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_lhs_1566_);
v_rhs_1567_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_rhs_1567_);
lean_dec_ref(v_x_1529_);
v___x_1568_ = lean_apply_4(v_h__8_1537_, v_w_1528_, v_n_1565_, v_lhs_1566_, v_rhs_1567_);
return v___x_1568_;
}
case 8:
{
lean_object* v_n_1569_; lean_object* v_lhs_1570_; lean_object* v_rhs_1571_; lean_object* v___x_1572_; 
lean_dec(v_h__10_1539_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_n_1569_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_n_1569_);
v_lhs_1570_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_lhs_1570_);
v_rhs_1571_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_rhs_1571_);
lean_dec_ref(v_x_1529_);
v___x_1572_ = lean_apply_4(v_h__9_1538_, v_w_1528_, v_n_1569_, v_lhs_1570_, v_rhs_1571_);
return v___x_1572_;
}
default: 
{
lean_object* v_n_1573_; lean_object* v_lhs_1574_; lean_object* v_rhs_1575_; lean_object* v___x_1576_; 
lean_dec(v_h__9_1538_);
lean_dec(v_h__8_1537_);
lean_dec(v_h__7_1536_);
lean_dec(v_h__6_1535_);
lean_dec(v_h__5_1534_);
lean_dec(v_h__4_1533_);
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
lean_dec(v_h__1_1530_);
v_n_1573_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_n_1573_);
v_lhs_1574_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_lhs_1574_);
v_rhs_1575_ = lean_ctor_get(v_x_1529_, 3);
lean_inc_ref(v_rhs_1575_);
lean_dec_ref(v_x_1529_);
v___x_1576_ = lean_apply_4(v_h__10_1539_, v_w_1528_, v_n_1573_, v_lhs_1574_, v_rhs_1575_);
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t v_x_1577_){
_start:
{
if (v_x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(1u);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object* v_x_1580_){
_start:
{
uint8_t v_x_boxed_1581_; lean_object* v_res_1582_; 
v_x_boxed_1581_ = lean_unbox(v_x_1580_);
v_res_1582_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_boxed_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object* v_x_1585_){
_start:
{
uint8_t v_x_4__boxed_1586_; lean_object* v_res_1587_; 
v_x_4__boxed_1586_ = lean_unbox(v_x_1585_);
v_res_1587_ = l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(v_x_4__boxed_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1588_){
_start:
{
lean_inc(v_k_1588_);
return v_k_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1589_);
lean_dec(v_k_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1591_, lean_object* v_ctorIdx_1592_, uint8_t v_t_1593_, lean_object* v_h_1594_, lean_object* v_k_1595_){
_start:
{
lean_inc(v_k_1595_);
return v_k_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1596_, lean_object* v_ctorIdx_1597_, lean_object* v_t_1598_, lean_object* v_h_1599_, lean_object* v_k_1600_){
_start:
{
uint8_t v_t_boxed_1601_; lean_object* v_res_1602_; 
v_t_boxed_1601_ = lean_unbox(v_t_1598_);
v_res_1602_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1596_, v_ctorIdx_1597_, v_t_boxed_1601_, v_h_1599_, v_k_1600_);
lean_dec(v_k_1600_);
lean_dec(v_ctorIdx_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1603_){
_start:
{
lean_inc(v_eq_1603_);
return v_eq_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1604_);
lean_dec(v_eq_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1606_, uint8_t v_t_1607_, lean_object* v_h_1608_, lean_object* v_eq_1609_){
_start:
{
lean_inc(v_eq_1609_);
return v_eq_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1610_, lean_object* v_t_1611_, lean_object* v_h_1612_, lean_object* v_eq_1613_){
_start:
{
uint8_t v_t_boxed_1614_; lean_object* v_res_1615_; 
v_t_boxed_1614_ = lean_unbox(v_t_1611_);
v_res_1615_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1610_, v_t_boxed_1614_, v_h_1612_, v_eq_1613_);
lean_dec(v_eq_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1616_){
_start:
{
lean_inc(v_ult_1616_);
return v_ult_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1617_);
lean_dec(v_ult_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1619_, uint8_t v_t_1620_, lean_object* v_h_1621_, lean_object* v_ult_1622_){
_start:
{
lean_inc(v_ult_1622_);
return v_ult_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_ult_1626_){
_start:
{
uint8_t v_t_boxed_1627_; lean_object* v_res_1628_; 
v_t_boxed_1627_ = lean_unbox(v_t_1624_);
v_res_1628_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1623_, v_t_boxed_1627_, v_h_1625_, v_ult_1626_);
lean_dec(v_ult_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1631_){
_start:
{
if (v_x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1634_){
_start:
{
uint8_t v_x_22__boxed_1635_; lean_object* v_res_1636_; 
v_x_22__boxed_1635_ = lean_unbox(v_x_1634_);
v_res_1636_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
if (v_x_1639_ == 0)
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_nat_dec_eq(v_a_1640_, v_a_1641_);
return v___x_1642_;
}
else
{
uint8_t v___x_1643_; 
v___x_1643_ = lean_nat_dec_lt(v_a_1640_, v_a_1641_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_x_100__boxed_1647_; uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_x_100__boxed_1647_ = lean_unbox(v_x_1644_);
v_res_1648_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_100__boxed_1647_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec(v_a_1645_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1650_, uint8_t v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1651_, v_a_1652_, v_a_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1655_, lean_object* v_x_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
uint8_t v_x_113__boxed_1659_; uint8_t v_res_1660_; lean_object* v_r_1661_; 
v_x_113__boxed_1659_ = lean_unbox(v_x_1656_);
v_res_1660_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1655_, v_x_113__boxed_1659_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_w_1655_);
v_r_1661_ = lean_box(v_res_1660_);
return v_r_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx(v_x_1665_);
lean_dec_ref(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1667_, lean_object* v_k_1668_){
_start:
{
if (lean_obj_tag(v_t_1667_) == 0)
{
lean_object* v_w_1669_; lean_object* v_lhs_1670_; uint8_t v_op_1671_; lean_object* v_rhs_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_w_1669_ = lean_ctor_get(v_t_1667_, 0);
lean_inc(v_w_1669_);
v_lhs_1670_ = lean_ctor_get(v_t_1667_, 1);
lean_inc_ref(v_lhs_1670_);
v_op_1671_ = lean_ctor_get_uint8(v_t_1667_, sizeof(void*)*3);
v_rhs_1672_ = lean_ctor_get(v_t_1667_, 2);
lean_inc_ref(v_rhs_1672_);
lean_dec_ref(v_t_1667_);
v___x_1673_ = lean_box(v_op_1671_);
v___x_1674_ = lean_apply_4(v_k_1668_, v_w_1669_, v_lhs_1670_, v___x_1673_, v_rhs_1672_);
return v___x_1674_;
}
else
{
lean_object* v_w_1675_; lean_object* v_expr_1676_; lean_object* v_idx_1677_; lean_object* v___x_1678_; 
v_w_1675_ = lean_ctor_get(v_t_1667_, 0);
lean_inc(v_w_1675_);
v_expr_1676_ = lean_ctor_get(v_t_1667_, 1);
lean_inc_ref(v_expr_1676_);
v_idx_1677_ = lean_ctor_get(v_t_1667_, 2);
lean_inc(v_idx_1677_);
lean_dec_ref(v_t_1667_);
v___x_1678_ = lean_apply_3(v_k_1668_, v_w_1675_, v_expr_1676_, v_idx_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1679_, lean_object* v_ctorIdx_1680_, lean_object* v_t_1681_, lean_object* v_h_1682_, lean_object* v_k_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1681_, v_k_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1685_, lean_object* v_ctorIdx_1686_, lean_object* v_t_1687_, lean_object* v_h_1688_, lean_object* v_k_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1685_, v_ctorIdx_1686_, v_t_1687_, v_h_1688_, v_k_1689_);
lean_dec(v_ctorIdx_1686_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1691_, lean_object* v_bin_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1691_, v_bin_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1694_, lean_object* v_t_1695_, lean_object* v_h_1696_, lean_object* v_bin_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1695_, v_bin_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1699_, lean_object* v_getLsbD_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1699_, v_getLsbD_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1702_, lean_object* v_t_1703_, lean_object* v_h_1704_, lean_object* v_getLsbD_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1703_, v_getLsbD_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
lean_object* v_w_1708_; lean_object* v_lhs_1709_; uint8_t v_op_1710_; lean_object* v_rhs_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_w_1708_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_n(v_w_1708_, 2);
v_lhs_1709_ = lean_ctor_get(v_x_1707_, 1);
lean_inc_ref(v_lhs_1709_);
v_op_1710_ = lean_ctor_get_uint8(v_x_1707_, sizeof(void*)*3);
v_rhs_1711_ = lean_ctor_get(v_x_1707_, 2);
lean_inc_ref(v_rhs_1711_);
lean_dec_ref(v_x_1707_);
v___x_1712_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1713_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1708_, v_lhs_1709_);
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1716_ = lean_string_append(v___x_1714_, v___x_1715_);
v___x_1717_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1710_);
v___x_1718_ = lean_string_append(v___x_1716_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = lean_string_append(v___x_1718_, v___x_1715_);
v___x_1720_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1708_, v_rhs_1711_);
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_w_1724_; lean_object* v_expr_1725_; lean_object* v_idx_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_w_1724_ = lean_ctor_get(v_x_1707_, 0);
lean_inc(v_w_1724_);
v_expr_1725_ = lean_ctor_get(v_x_1707_, 1);
lean_inc_ref(v_expr_1725_);
v_idx_1726_ = lean_ctor_get(v_x_1707_, 2);
lean_inc(v_idx_1726_);
lean_dec_ref(v_x_1707_);
v___x_1727_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1724_, v_expr_1725_);
v___x_1728_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
v___x_1730_ = l_Nat_reprFast(v_idx_1726_);
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
lean_object* v_w_1738_; lean_object* v_lhs_1739_; uint8_t v_op_1740_; lean_object* v_rhs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_w_1738_ = lean_ctor_get(v_x_1737_, 0);
lean_inc_n(v_w_1738_, 2);
v_lhs_1739_ = lean_ctor_get(v_x_1737_, 1);
lean_inc_ref(v_lhs_1739_);
v_op_1740_ = lean_ctor_get_uint8(v_x_1737_, sizeof(void*)*3);
v_rhs_1741_ = lean_ctor_get(v_x_1737_, 2);
lean_inc_ref(v_rhs_1741_);
lean_dec_ref(v_x_1737_);
v___x_1742_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1738_, v_assign_1736_, v_lhs_1739_);
v___x_1743_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1738_, v_assign_1736_, v_rhs_1741_);
v___x_1744_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1740_, v___x_1742_, v___x_1743_);
lean_dec(v___x_1743_);
lean_dec(v___x_1742_);
return v___x_1744_;
}
else
{
lean_object* v_w_1745_; lean_object* v_expr_1746_; lean_object* v_idx_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_w_1745_ = lean_ctor_get(v_x_1737_, 0);
lean_inc(v_w_1745_);
v_expr_1746_ = lean_ctor_get(v_x_1737_, 1);
lean_inc_ref(v_expr_1746_);
v_idx_1747_ = lean_ctor_get(v_x_1737_, 2);
lean_inc(v_idx_1747_);
lean_dec_ref(v_x_1737_);
v___x_1748_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1745_, v_assign_1736_, v_expr_1746_);
v___x_1749_ = l_Nat_testBit(v___x_1748_, v_idx_1747_);
lean_dec(v_idx_1747_);
lean_dec(v___x_1748_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1750_, lean_object* v_x_1751_){
_start:
{
uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_res_1752_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1750_, v_x_1751_);
lean_dec_ref(v_assign_1750_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1754_, lean_object* v_x_1755_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1754_, v_x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1757_, lean_object* v_x_1758_){
_start:
{
uint8_t v_res_1759_; lean_object* v_r_1760_; 
v_res_1759_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1757_, v_x_1758_);
lean_dec_ref(v_assign_1757_);
v_r_1760_ = lean_box(v_res_1759_);
return v_r_1760_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1761_, lean_object* v_expr_1762_){
_start:
{
lean_object* v___f_1763_; uint8_t v___x_1764_; 
v___f_1763_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1763_, 0, v_assign_1761_);
v___x_1764_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1763_, v_expr_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1765_, lean_object* v_expr_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1765_, v_expr_1766_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Std_Tactic_BVDecide_instInhabitedBVBit = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit);
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
