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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* v_k_163_){
_start:
{
lean_inc(v_k_163_);
return v_k_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* v_k_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_164_);
lean_dec(v_k_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* v_motive_166_, lean_object* v_ctorIdx_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_k_170_){
_start:
{
lean_inc(v_k_170_);
return v_k_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object* v_motive_171_, lean_object* v_ctorIdx_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_k_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(v_motive_171_, v_ctorIdx_172_, v_t_boxed_176_, v_h_174_, v_k_175_);
lean_dec(v_k_175_);
lean_dec(v_ctorIdx_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object* v_and_178_){
_start:
{
lean_inc(v_and_178_);
return v_and_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object* v_and_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(v_and_179_);
lean_dec(v_and_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_and_184_){
_start:
{
lean_inc(v_and_184_);
return v_and_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_and_188_){
_start:
{
uint8_t v_t_boxed_189_; lean_object* v_res_190_; 
v_t_boxed_189_ = lean_unbox(v_t_186_);
v_res_190_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(v_motive_185_, v_t_boxed_189_, v_h_187_, v_and_188_);
lean_dec(v_and_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* v_or_191_){
_start:
{
lean_inc(v_or_191_);
return v_or_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* v_or_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_192_);
lean_dec(v_or_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* v_motive_194_, uint8_t v_t_195_, lean_object* v_h_196_, lean_object* v_or_197_){
_start:
{
lean_inc(v_or_197_);
return v_or_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_or_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(v_motive_198_, v_t_boxed_202_, v_h_200_, v_or_201_);
lean_dec(v_or_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* v_xor_204_){
_start:
{
lean_inc(v_xor_204_);
return v_xor_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* v_xor_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_205_);
lean_dec(v_xor_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_xor_210_){
_start:
{
lean_inc(v_xor_210_);
return v_xor_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_xor_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_xor_214_);
lean_dec(v_xor_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* v_add_217_){
_start:
{
lean_inc(v_add_217_);
return v_add_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* v_add_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_218_);
lean_dec(v_add_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_add_223_){
_start:
{
lean_inc(v_add_223_);
return v_add_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_add_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_add_227_);
lean_dec(v_add_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object* v_mul_230_){
_start:
{
lean_inc(v_mul_230_);
return v_mul_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object* v_mul_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(v_mul_231_);
lean_dec(v_mul_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_mul_236_){
_start:
{
lean_inc(v_mul_236_);
return v_mul_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_mul_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_mul_240_);
lean_dec(v_mul_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* v_udiv_243_){
_start:
{
lean_inc(v_udiv_243_);
return v_udiv_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* v_udiv_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_244_);
lean_dec(v_udiv_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_udiv_249_){
_start:
{
lean_inc(v_udiv_249_);
return v_udiv_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_udiv_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_udiv_253_);
lean_dec(v_udiv_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* v_umod_256_){
_start:
{
lean_inc(v_umod_256_);
return v_umod_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* v_umod_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_257_);
lean_dec(v_umod_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_umod_262_){
_start:
{
lean_inc(v_umod_262_);
return v_umod_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_umod_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_umod_266_);
lean_dec(v_umod_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t v_x_269_){
_start:
{
switch(v_x_269_)
{
case 0:
{
uint64_t v___x_270_; 
v___x_270_ = 0ULL;
return v___x_270_;
}
case 1:
{
uint64_t v___x_271_; 
v___x_271_ = 1ULL;
return v___x_271_;
}
case 2:
{
uint64_t v___x_272_; 
v___x_272_ = 2ULL;
return v___x_272_;
}
case 3:
{
uint64_t v___x_273_; 
v___x_273_ = 3ULL;
return v___x_273_;
}
case 4:
{
uint64_t v___x_274_; 
v___x_274_ = 4ULL;
return v___x_274_;
}
case 5:
{
uint64_t v___x_275_; 
v___x_275_ = 5ULL;
return v___x_275_;
}
default: 
{
uint64_t v___x_276_; 
v___x_276_ = 6ULL;
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* v_x_277_){
_start:
{
uint8_t v_x_88__boxed_278_; uint64_t v_res_279_; lean_object* v_r_280_; 
v_x_88__boxed_278_ = lean_unbox(v_x_277_);
v_res_279_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_278_);
v_r_280_ = lean_box_uint64(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* v_n_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(2u);
v___x_285_ = lean_nat_dec_le(v_n_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(4u);
v___x_287_ = lean_nat_dec_le(v_n_283_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(5u);
v___x_289_ = lean_nat_dec_le(v_n_283_, v___x_288_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 6;
return v___x_290_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = 5;
return v___x_291_;
}
}
else
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_nat_dec_le(v_n_283_, v___x_292_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 4;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 3;
return v___x_295_;
}
}
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_nat_dec_le(v_n_283_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_dec_le(v_n_283_, v___x_298_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 2;
return v___x_300_;
}
else
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
}
else
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* v_n_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_303_);
lean_dec(v_n_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t v_x_306_, uint8_t v_y_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_306_);
v___x_309_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_y_307_);
v___x_310_ = lean_nat_dec_eq(v___x_308_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* v_x_311_, lean_object* v_y_312_){
_start:
{
uint8_t v_x_13__boxed_313_; uint8_t v_y_14__boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_x_13__boxed_313_ = lean_unbox(v_x_311_);
v_y_14__boxed_314_ = lean_unbox(v_y_312_);
v_res_315_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_13__boxed_313_, v_y_14__boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t v_x_324_){
_start:
{
switch(v_x_324_)
{
case 0:
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return v___x_325_;
}
case 1:
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return v___x_326_;
}
case 2:
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return v___x_327_;
}
case 3:
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return v___x_328_;
}
case 4:
{
lean_object* v___x_329_; 
v___x_329_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return v___x_329_;
}
case 5:
{
lean_object* v___x_330_; 
v___x_330_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return v___x_330_;
}
default: 
{
lean_object* v___x_331_; 
v___x_331_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* v_x_332_){
_start:
{
uint8_t v_x_67__boxed_333_; lean_object* v_res_334_; 
v_x_67__boxed_333_ = lean_unbox(v_x_332_);
v_res_334_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* v_w_337_, uint8_t v_x_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
switch(v_x_338_)
{
case 0:
{
lean_object* v___x_341_; 
v___x_341_ = lean_nat_land(v_a_339_, v_a_340_);
return v___x_341_;
}
case 1:
{
lean_object* v___x_342_; 
v___x_342_ = lean_nat_lor(v_a_339_, v_a_340_);
return v___x_342_;
}
case 2:
{
lean_object* v___x_343_; 
v___x_343_ = lean_nat_lxor(v_a_339_, v_a_340_);
return v___x_343_;
}
case 3:
{
lean_object* v___x_344_; 
v___x_344_ = l_BitVec_add(v_w_337_, v_a_339_, v_a_340_);
return v___x_344_;
}
case 4:
{
lean_object* v___x_345_; 
v___x_345_ = l_BitVec_mul(v_w_337_, v_a_339_, v_a_340_);
return v___x_345_;
}
case 5:
{
lean_object* v___x_346_; 
v___x_346_ = lean_nat_div(v_a_339_, v_a_340_);
return v___x_346_;
}
default: 
{
lean_object* v___x_347_; 
v___x_347_ = lean_nat_mod(v_a_339_, v_a_340_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* v_w_348_, lean_object* v_x_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_x_340__boxed_352_; lean_object* v_res_353_; 
v_x_340__boxed_352_ = lean_unbox(v_x_349_);
v_res_353_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_348_, v_x_340__boxed_352_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec(v_a_350_);
lean_dec(v_w_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(lean_object* v_x_354_){
_start:
{
switch(lean_obj_tag(v_x_354_))
{
case 0:
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(0u);
return v___x_355_;
}
case 1:
{
lean_object* v___x_356_; 
v___x_356_ = lean_unsigned_to_nat(1u);
return v___x_356_;
}
case 2:
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(2u);
return v___x_357_;
}
case 3:
{
lean_object* v___x_358_; 
v___x_358_ = lean_unsigned_to_nat(3u);
return v___x_358_;
}
case 4:
{
lean_object* v___x_359_; 
v___x_359_ = lean_unsigned_to_nat(4u);
return v___x_359_;
}
case 5:
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(5u);
return v___x_360_;
}
default: 
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(6u);
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(v_x_362_);
lean_dec(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* v_t_364_, lean_object* v_k_365_){
_start:
{
switch(lean_obj_tag(v_t_364_))
{
case 1:
{
lean_object* v_n_366_; lean_object* v___x_367_; 
v_n_366_ = lean_ctor_get(v_t_364_, 0);
lean_inc(v_n_366_);
lean_dec_ref_known(v_t_364_, 1);
v___x_367_ = lean_apply_1(v_k_365_, v_n_366_);
return v___x_367_;
}
case 2:
{
lean_object* v_n_368_; lean_object* v___x_369_; 
v_n_368_ = lean_ctor_get(v_t_364_, 0);
lean_inc(v_n_368_);
lean_dec_ref_known(v_t_364_, 1);
v___x_369_ = lean_apply_1(v_k_365_, v_n_368_);
return v___x_369_;
}
case 3:
{
lean_object* v_n_370_; lean_object* v___x_371_; 
v_n_370_ = lean_ctor_get(v_t_364_, 0);
lean_inc(v_n_370_);
lean_dec_ref_known(v_t_364_, 1);
v___x_371_ = lean_apply_1(v_k_365_, v_n_370_);
return v___x_371_;
}
default: 
{
lean_dec(v_t_364_);
return v_k_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* v_motive_372_, lean_object* v_ctorIdx_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_k_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_374_, v_k_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* v_motive_378_, lean_object* v_ctorIdx_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_k_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(v_motive_378_, v_ctorIdx_379_, v_t_380_, v_h_381_, v_k_382_);
lean_dec(v_ctorIdx_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* v_t_384_, lean_object* v_not_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_384_, v_not_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* v_motive_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_not_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_388_, v_not_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* v_t_392_, lean_object* v_rotateLeft_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_392_, v_rotateLeft_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* v_motive_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_rotateLeft_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_396_, v_rotateLeft_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* v_t_400_, lean_object* v_rotateRight_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_400_, v_rotateRight_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_rotateRight_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_404_, v_rotateRight_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* v_t_408_, lean_object* v_arithShiftRightConst_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_408_, v_arithShiftRightConst_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_arithShiftRightConst_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_412_, v_arithShiftRightConst_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* v_t_416_, lean_object* v_reverse_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_416_, v_reverse_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_reverse_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_420_, v_reverse_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* v_t_424_, lean_object* v_clz_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_424_, v_clz_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_clz_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_428_, v_clz_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object* v_t_432_, lean_object* v_cpop_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_432_, v_cpop_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object* v_motive_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_cpop_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_436_, v_cpop_438_);
return v___x_439_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* v_x_440_){
_start:
{
switch(lean_obj_tag(v_x_440_))
{
case 0:
{
uint64_t v___x_441_; 
v___x_441_ = 0ULL;
return v___x_441_;
}
case 1:
{
lean_object* v_n_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; 
v_n_442_ = lean_ctor_get(v_x_440_, 0);
v___x_443_ = 1ULL;
v___x_444_ = lean_uint64_of_nat(v_n_442_);
v___x_445_ = lean_uint64_mix_hash(v___x_443_, v___x_444_);
return v___x_445_;
}
case 2:
{
lean_object* v_n_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; 
v_n_446_ = lean_ctor_get(v_x_440_, 0);
v___x_447_ = 2ULL;
v___x_448_ = lean_uint64_of_nat(v_n_446_);
v___x_449_ = lean_uint64_mix_hash(v___x_447_, v___x_448_);
return v___x_449_;
}
case 3:
{
lean_object* v_n_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; 
v_n_450_ = lean_ctor_get(v_x_440_, 0);
v___x_451_ = 3ULL;
v___x_452_ = lean_uint64_of_nat(v_n_450_);
v___x_453_ = lean_uint64_mix_hash(v___x_451_, v___x_452_);
return v___x_453_;
}
case 4:
{
uint64_t v___x_454_; 
v___x_454_ = 4ULL;
return v___x_454_;
}
case 5:
{
uint64_t v___x_455_; 
v___x_455_ = 5ULL;
return v___x_455_;
}
default: 
{
uint64_t v___x_456_; 
v___x_456_ = 6ULL;
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object* v_x_457_){
_start:
{
uint64_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_457_);
lean_dec(v_x_457_);
v_r_459_ = lean_box_uint64(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
switch(lean_obj_tag(v_x_462_))
{
case 0:
{
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
uint8_t v___x_464_; 
v___x_464_ = 1;
return v___x_464_;
}
case 4:
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
case 5:
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
case 6:
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
default: 
{
uint8_t v___x_468_; 
v___x_468_ = 0;
return v___x_468_;
}
}
}
case 1:
{
lean_object* v_n_469_; uint8_t v___x_470_; 
v_n_469_ = lean_ctor_get(v_x_462_, 0);
v___x_470_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_470_;
}
case 1:
{
lean_object* v_n_471_; uint8_t v___x_472_; 
v_n_471_ = lean_ctor_get(v_x_463_, 0);
v___x_472_ = lean_nat_dec_eq(v_n_469_, v_n_471_);
if (v___x_472_ == 0)
{
return v___x_470_;
}
else
{
return v___x_472_;
}
}
case 4:
{
return v___x_470_;
}
case 5:
{
return v___x_470_;
}
case 6:
{
return v___x_470_;
}
default: 
{
return v___x_470_;
}
}
}
case 2:
{
lean_object* v_n_473_; uint8_t v___x_474_; 
v_n_473_ = lean_ctor_get(v_x_462_, 0);
v___x_474_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_474_;
}
case 2:
{
lean_object* v_n_475_; uint8_t v___x_476_; 
v_n_475_ = lean_ctor_get(v_x_463_, 0);
v___x_476_ = lean_nat_dec_eq(v_n_473_, v_n_475_);
if (v___x_476_ == 0)
{
return v___x_474_;
}
else
{
return v___x_476_;
}
}
case 4:
{
return v___x_474_;
}
case 5:
{
return v___x_474_;
}
case 6:
{
return v___x_474_;
}
default: 
{
return v___x_474_;
}
}
}
case 3:
{
lean_object* v_n_477_; uint8_t v___x_478_; 
v_n_477_ = lean_ctor_get(v_x_462_, 0);
v___x_478_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_478_;
}
case 3:
{
lean_object* v_n_479_; uint8_t v___x_480_; 
v_n_479_ = lean_ctor_get(v_x_463_, 0);
v___x_480_ = lean_nat_dec_eq(v_n_477_, v_n_479_);
if (v___x_480_ == 0)
{
return v___x_478_;
}
else
{
return v___x_480_;
}
}
case 4:
{
return v___x_478_;
}
case 5:
{
return v___x_478_;
}
case 6:
{
return v___x_478_;
}
default: 
{
return v___x_478_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_463_))
{
case 1:
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
case 2:
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
case 3:
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
case 4:
{
uint8_t v___x_484_; 
v___x_484_ = 1;
return v___x_484_;
}
default: 
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
}
case 5:
{
switch(lean_obj_tag(v_x_463_))
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
case 5:
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
default: 
{
switch(lean_obj_tag(v_x_463_))
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
case 6:
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec(v_x_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_500_, v_x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec(v_x_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_514_){
_start:
{
switch(lean_obj_tag(v_x_514_))
{
case 0:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_515_;
}
case 1:
{
lean_object* v_n_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_n_516_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_n_516_);
lean_dec_ref_known(v_x_514_, 1);
v___x_517_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_518_ = l_Nat_reprFast(v_n_516_);
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
lean_dec_ref(v___x_518_);
return v___x_519_;
}
case 2:
{
lean_object* v_n_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_n_520_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_n_520_);
lean_dec_ref_known(v_x_514_, 1);
v___x_521_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_522_ = l_Nat_reprFast(v_n_520_);
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
lean_dec_ref(v___x_522_);
return v___x_523_;
}
case 3:
{
lean_object* v_n_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_n_524_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_n_524_);
lean_dec_ref_known(v_x_514_, 1);
v___x_525_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_526_ = l_Nat_reprFast(v_n_524_);
v___x_527_ = lean_string_append(v___x_525_, v___x_526_);
lean_dec_ref(v___x_526_);
return v___x_527_;
}
case 4:
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_528_;
}
case 5:
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_529_;
}
default: 
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_533_, lean_object* v_x_534_, lean_object* v_a_535_){
_start:
{
switch(lean_obj_tag(v_x_534_))
{
case 0:
{
lean_object* v___x_536_; 
v___x_536_ = l_BitVec_not(v_w_533_, v_a_535_);
lean_dec(v_a_535_);
lean_dec(v_w_533_);
return v___x_536_;
}
case 1:
{
lean_object* v_n_537_; lean_object* v___x_538_; 
v_n_537_ = lean_ctor_get(v_x_534_, 0);
v___x_538_ = l_BitVec_rotateLeft(v_w_533_, v_a_535_, v_n_537_);
lean_dec(v_a_535_);
lean_dec(v_w_533_);
return v___x_538_;
}
case 2:
{
lean_object* v_n_539_; lean_object* v___x_540_; 
v_n_539_ = lean_ctor_get(v_x_534_, 0);
v___x_540_ = l_BitVec_rotateRight(v_w_533_, v_a_535_, v_n_539_);
lean_dec(v_a_535_);
lean_dec(v_w_533_);
return v___x_540_;
}
case 3:
{
lean_object* v_n_541_; lean_object* v___x_542_; 
v_n_541_ = lean_ctor_get(v_x_534_, 0);
v___x_542_ = l_BitVec_sshiftRight(v_w_533_, v_a_535_, v_n_541_);
lean_dec(v_w_533_);
return v___x_542_;
}
case 4:
{
lean_object* v___x_543_; 
v___x_543_ = l_BitVec_reverse(v_w_533_, v_a_535_);
lean_dec(v_a_535_);
lean_dec(v_w_533_);
return v___x_543_;
}
case 5:
{
lean_object* v___x_544_; 
v___x_544_ = l_BitVec_clz(v_w_533_, v_a_535_);
lean_dec(v_a_535_);
lean_dec(v_w_533_);
return v___x_544_;
}
default: 
{
lean_object* v___x_545_; 
v___x_545_ = l_BitVec_cpop(v_w_533_, v_a_535_);
lean_dec(v_a_535_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_546_, lean_object* v_x_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_546_, v_x_547_, v_a_548_);
lean_dec(v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object* v_x_550_){
_start:
{
switch(lean_obj_tag(v_x_550_))
{
case 0:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(0u);
return v___x_551_;
}
case 1:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(1u);
return v___x_552_;
}
case 2:
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(2u);
return v___x_553_;
}
case 3:
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(3u);
return v___x_554_;
}
case 4:
{
lean_object* v___x_555_; 
v___x_555_ = lean_unsigned_to_nat(4u);
return v___x_555_;
}
case 5:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(5u);
return v___x_556_;
}
case 6:
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(6u);
return v___x_557_;
}
case 7:
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(7u);
return v___x_558_;
}
case 8:
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(8u);
return v___x_559_;
}
default: 
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(9u);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_561_);
lean_dec_ref(v_x_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object* v_a_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(v_a_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec(v_a_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_569_, lean_object* v_k_570_){
_start:
{
switch(lean_obj_tag(v_t_569_))
{
case 0:
{
lean_object* v_w_571_; lean_object* v_idx_572_; lean_object* v___x_573_; 
v_w_571_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_571_);
v_idx_572_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_idx_572_);
lean_dec_ref_known(v_t_569_, 2);
v___x_573_ = lean_apply_2(v_k_570_, v_w_571_, v_idx_572_);
return v___x_573_;
}
case 1:
{
lean_object* v_w_574_; lean_object* v_val_575_; lean_object* v___x_576_; 
v_w_574_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_574_);
v_val_575_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_val_575_);
lean_dec_ref_known(v_t_569_, 2);
v___x_576_ = lean_apply_2(v_k_570_, v_w_574_, v_val_575_);
return v___x_576_;
}
case 2:
{
lean_object* v_w_577_; lean_object* v_start_578_; lean_object* v_len_579_; lean_object* v_expr_580_; lean_object* v___x_581_; 
v_w_577_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_577_);
v_start_578_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_start_578_);
v_len_579_ = lean_ctor_get(v_t_569_, 2);
lean_inc(v_len_579_);
v_expr_580_ = lean_ctor_get(v_t_569_, 3);
lean_inc_ref(v_expr_580_);
lean_dec_ref_known(v_t_569_, 4);
v___x_581_ = lean_apply_4(v_k_570_, v_w_577_, v_start_578_, v_len_579_, v_expr_580_);
return v___x_581_;
}
case 3:
{
lean_object* v_w_582_; lean_object* v_lhs_583_; uint8_t v_op_584_; lean_object* v_rhs_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_w_582_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_582_);
v_lhs_583_ = lean_ctor_get(v_t_569_, 1);
lean_inc_ref(v_lhs_583_);
v_op_584_ = lean_ctor_get_uint8(v_t_569_, sizeof(void*)*3);
v_rhs_585_ = lean_ctor_get(v_t_569_, 2);
lean_inc_ref(v_rhs_585_);
lean_dec_ref_known(v_t_569_, 3);
v___x_586_ = lean_box(v_op_584_);
v___x_587_ = lean_apply_4(v_k_570_, v_w_582_, v_lhs_583_, v___x_586_, v_rhs_585_);
return v___x_587_;
}
case 4:
{
lean_object* v_w_588_; lean_object* v_op_589_; lean_object* v_operand_590_; lean_object* v___x_591_; 
v_w_588_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_588_);
v_op_589_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_op_589_);
v_operand_590_ = lean_ctor_get(v_t_569_, 2);
lean_inc_ref(v_operand_590_);
lean_dec_ref_known(v_t_569_, 3);
v___x_591_ = lean_apply_3(v_k_570_, v_w_588_, v_op_589_, v_operand_590_);
return v___x_591_;
}
case 5:
{
lean_object* v_l_592_; lean_object* v_r_593_; lean_object* v_w_594_; lean_object* v_lhs_595_; lean_object* v_rhs_596_; lean_object* v___x_597_; 
v_l_592_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_l_592_);
v_r_593_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_r_593_);
v_w_594_ = lean_ctor_get(v_t_569_, 2);
lean_inc(v_w_594_);
v_lhs_595_ = lean_ctor_get(v_t_569_, 3);
lean_inc_ref(v_lhs_595_);
v_rhs_596_ = lean_ctor_get(v_t_569_, 4);
lean_inc_ref(v_rhs_596_);
lean_dec_ref_known(v_t_569_, 5);
v___x_597_ = lean_apply_6(v_k_570_, v_l_592_, v_r_593_, v_w_594_, v_lhs_595_, v_rhs_596_, lean_box(0));
return v___x_597_;
}
case 6:
{
lean_object* v_w_598_; lean_object* v_w_x27_599_; lean_object* v_n_600_; lean_object* v_expr_601_; lean_object* v___x_602_; 
v_w_598_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_w_598_);
v_w_x27_599_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_w_x27_599_);
v_n_600_ = lean_ctor_get(v_t_569_, 2);
lean_inc(v_n_600_);
v_expr_601_ = lean_ctor_get(v_t_569_, 3);
lean_inc_ref(v_expr_601_);
lean_dec_ref_known(v_t_569_, 4);
v___x_602_ = lean_apply_5(v_k_570_, v_w_598_, v_w_x27_599_, v_n_600_, v_expr_601_, lean_box(0));
return v___x_602_;
}
default: 
{
lean_object* v_m_603_; lean_object* v_n_604_; lean_object* v_lhs_605_; lean_object* v_rhs_606_; lean_object* v___x_607_; 
v_m_603_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_m_603_);
v_n_604_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_n_604_);
v_lhs_605_ = lean_ctor_get(v_t_569_, 2);
lean_inc_ref(v_lhs_605_);
v_rhs_606_ = lean_ctor_get(v_t_569_, 3);
lean_inc_ref(v_rhs_606_);
lean_dec_ref(v_t_569_);
v___x_607_ = lean_apply_4(v_k_570_, v_m_603_, v_n_604_, v_lhs_605_, v_rhs_606_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_608_, lean_object* v_ctorIdx_609_, lean_object* v_a_610_, lean_object* v_t_611_, lean_object* v_h_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_611_, v_k_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_615_, lean_object* v_ctorIdx_616_, lean_object* v_a_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_k_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_615_, v_ctorIdx_616_, v_a_617_, v_t_618_, v_h_619_, v_k_620_);
lean_dec(v_a_617_);
lean_dec(v_ctorIdx_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_622_, lean_object* v_var_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_622_, v_var_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_625_, lean_object* v_a_626_, lean_object* v_t_627_, lean_object* v_h_628_, lean_object* v_var_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_627_, v_var_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_631_, lean_object* v_a_632_, lean_object* v_t_633_, lean_object* v_h_634_, lean_object* v_var_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_631_, v_a_632_, v_t_633_, v_h_634_, v_var_635_);
lean_dec(v_a_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_637_, lean_object* v_const_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_637_, v_const_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_640_, lean_object* v_a_641_, lean_object* v_t_642_, lean_object* v_h_643_, lean_object* v_const_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_642_, v_const_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_646_, lean_object* v_a_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_const_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_646_, v_a_647_, v_t_648_, v_h_649_, v_const_650_);
lean_dec(v_a_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_652_, lean_object* v_extract_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_652_, v_extract_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_655_, lean_object* v_a_656_, lean_object* v_t_657_, lean_object* v_h_658_, lean_object* v_extract_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_657_, v_extract_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_661_, lean_object* v_a_662_, lean_object* v_t_663_, lean_object* v_h_664_, lean_object* v_extract_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_661_, v_a_662_, v_t_663_, v_h_664_, v_extract_665_);
lean_dec(v_a_662_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_667_, lean_object* v_bin_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_667_, v_bin_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_670_, lean_object* v_a_671_, lean_object* v_t_672_, lean_object* v_h_673_, lean_object* v_bin_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_672_, v_bin_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_676_, lean_object* v_a_677_, lean_object* v_t_678_, lean_object* v_h_679_, lean_object* v_bin_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_676_, v_a_677_, v_t_678_, v_h_679_, v_bin_680_);
lean_dec(v_a_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_682_, lean_object* v_un_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_682_, v_un_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_685_, lean_object* v_a_686_, lean_object* v_t_687_, lean_object* v_h_688_, lean_object* v_un_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_687_, v_un_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_691_, lean_object* v_a_692_, lean_object* v_t_693_, lean_object* v_h_694_, lean_object* v_un_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_691_, v_a_692_, v_t_693_, v_h_694_, v_un_695_);
lean_dec(v_a_692_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_697_, lean_object* v_append_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_697_, v_append_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_700_, lean_object* v_a_701_, lean_object* v_t_702_, lean_object* v_h_703_, lean_object* v_append_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_702_, v_append_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_706_, lean_object* v_a_707_, lean_object* v_t_708_, lean_object* v_h_709_, lean_object* v_append_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_706_, v_a_707_, v_t_708_, v_h_709_, v_append_710_);
lean_dec(v_a_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_712_, lean_object* v_replicate_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_712_, v_replicate_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_715_, lean_object* v_a_716_, lean_object* v_t_717_, lean_object* v_h_718_, lean_object* v_replicate_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_717_, v_replicate_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_721_, lean_object* v_a_722_, lean_object* v_t_723_, lean_object* v_h_724_, lean_object* v_replicate_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_721_, v_a_722_, v_t_723_, v_h_724_, v_replicate_725_);
lean_dec(v_a_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_727_, lean_object* v_shiftLeft_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_727_, v_shiftLeft_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_730_, lean_object* v_a_731_, lean_object* v_t_732_, lean_object* v_h_733_, lean_object* v_shiftLeft_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_732_, v_shiftLeft_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_736_, lean_object* v_a_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_shiftLeft_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_736_, v_a_737_, v_t_738_, v_h_739_, v_shiftLeft_740_);
lean_dec(v_a_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_742_, lean_object* v_shiftRight_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_742_, v_shiftRight_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_745_, lean_object* v_a_746_, lean_object* v_t_747_, lean_object* v_h_748_, lean_object* v_shiftRight_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_747_, v_shiftRight_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_751_, lean_object* v_a_752_, lean_object* v_t_753_, lean_object* v_h_754_, lean_object* v_shiftRight_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_751_, v_a_752_, v_t_753_, v_h_754_, v_shiftRight_755_);
lean_dec(v_a_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_757_, lean_object* v_arithShiftRight_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_757_, v_arithShiftRight_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_760_, lean_object* v_a_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_arithShiftRight_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_762_, v_arithShiftRight_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_766_, lean_object* v_a_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_arithShiftRight_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_766_, v_a_767_, v_t_768_, v_h_769_, v_arithShiftRight_770_);
lean_dec(v_a_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_772_, lean_object* v_var_773_, lean_object* v_const_774_, lean_object* v_extract_775_, lean_object* v_bin_776_, lean_object* v_un_777_, lean_object* v_append_778_, lean_object* v_replicate_779_, lean_object* v_shiftLeft_780_, lean_object* v_shiftRight_781_, lean_object* v_arithShiftRight_782_){
_start:
{
switch(lean_obj_tag(v_t_772_))
{
case 0:
{
lean_object* v_w_783_; lean_object* v_idx_784_; lean_object* v___x_785_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
v_w_783_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_783_);
v_idx_784_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_idx_784_);
lean_dec_ref_known(v_t_772_, 2);
v___x_785_ = lean_apply_2(v_var_773_, v_w_783_, v_idx_784_);
return v___x_785_;
}
case 1:
{
lean_object* v_w_786_; lean_object* v_val_787_; lean_object* v___x_788_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_var_773_);
v_w_786_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_786_);
v_val_787_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_val_787_);
lean_dec_ref_known(v_t_772_, 2);
v___x_788_ = lean_apply_2(v_const_774_, v_w_786_, v_val_787_);
return v___x_788_;
}
case 2:
{
lean_object* v_w_789_; lean_object* v_start_790_; lean_object* v_len_791_; lean_object* v_expr_792_; lean_object* v___x_793_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_w_789_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_789_);
v_start_790_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_start_790_);
v_len_791_ = lean_ctor_get(v_t_772_, 2);
lean_inc(v_len_791_);
v_expr_792_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_expr_792_);
lean_dec_ref_known(v_t_772_, 4);
v___x_793_ = lean_apply_4(v_extract_775_, v_w_789_, v_start_790_, v_len_791_, v_expr_792_);
return v___x_793_;
}
case 3:
{
lean_object* v_w_794_; lean_object* v_lhs_795_; uint8_t v_op_796_; lean_object* v_rhs_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_w_794_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_794_);
v_lhs_795_ = lean_ctor_get(v_t_772_, 1);
lean_inc_ref(v_lhs_795_);
v_op_796_ = lean_ctor_get_uint8(v_t_772_, sizeof(void*)*3 + 8);
v_rhs_797_ = lean_ctor_get(v_t_772_, 2);
lean_inc_ref(v_rhs_797_);
lean_dec_ref_known(v_t_772_, 3);
v___x_798_ = lean_box(v_op_796_);
v___x_799_ = lean_apply_4(v_bin_776_, v_w_794_, v_lhs_795_, v___x_798_, v_rhs_797_);
return v___x_799_;
}
case 4:
{
lean_object* v_w_800_; lean_object* v_op_801_; lean_object* v_operand_802_; lean_object* v___x_803_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_w_800_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_800_);
v_op_801_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_op_801_);
v_operand_802_ = lean_ctor_get(v_t_772_, 2);
lean_inc_ref(v_operand_802_);
lean_dec_ref_known(v_t_772_, 3);
v___x_803_ = lean_apply_3(v_un_777_, v_w_800_, v_op_801_, v_operand_802_);
return v___x_803_;
}
case 5:
{
lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v_w_806_; lean_object* v_lhs_807_; lean_object* v_rhs_808_; lean_object* v___x_809_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_l_804_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_l_804_);
v_r_805_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_r_805_);
v_w_806_ = lean_ctor_get(v_t_772_, 2);
lean_inc(v_w_806_);
v_lhs_807_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_lhs_807_);
v_rhs_808_ = lean_ctor_get(v_t_772_, 4);
lean_inc_ref(v_rhs_808_);
lean_dec_ref_known(v_t_772_, 5);
v___x_809_ = lean_apply_6(v_append_778_, v_l_804_, v_r_805_, v_w_806_, v_lhs_807_, v_rhs_808_, lean_box(0));
return v___x_809_;
}
case 6:
{
lean_object* v_w_810_; lean_object* v_w_x27_811_; lean_object* v_n_812_; lean_object* v_expr_813_; lean_object* v___x_814_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_w_810_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_w_810_);
v_w_x27_811_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_w_x27_811_);
v_n_812_ = lean_ctor_get(v_t_772_, 2);
lean_inc(v_n_812_);
v_expr_813_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_expr_813_);
lean_dec_ref_known(v_t_772_, 4);
v___x_814_ = lean_apply_5(v_replicate_779_, v_w_810_, v_w_x27_811_, v_n_812_, v_expr_813_, lean_box(0));
return v___x_814_;
}
case 7:
{
lean_object* v_m_815_; lean_object* v_n_816_; lean_object* v_lhs_817_; lean_object* v_rhs_818_; lean_object* v___x_819_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftRight_781_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_m_815_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_m_815_);
v_n_816_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_n_816_);
v_lhs_817_ = lean_ctor_get(v_t_772_, 2);
lean_inc_ref(v_lhs_817_);
v_rhs_818_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_rhs_818_);
lean_dec_ref_known(v_t_772_, 4);
v___x_819_ = lean_apply_4(v_shiftLeft_780_, v_m_815_, v_n_816_, v_lhs_817_, v_rhs_818_);
return v___x_819_;
}
case 8:
{
lean_object* v_m_820_; lean_object* v_n_821_; lean_object* v_lhs_822_; lean_object* v_rhs_823_; lean_object* v___x_824_; 
lean_dec(v_arithShiftRight_782_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_m_820_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_m_820_);
v_n_821_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_n_821_);
v_lhs_822_ = lean_ctor_get(v_t_772_, 2);
lean_inc_ref(v_lhs_822_);
v_rhs_823_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_rhs_823_);
lean_dec_ref_known(v_t_772_, 4);
v___x_824_ = lean_apply_4(v_shiftRight_781_, v_m_820_, v_n_821_, v_lhs_822_, v_rhs_823_);
return v___x_824_;
}
default: 
{
lean_object* v_m_825_; lean_object* v_n_826_; lean_object* v_lhs_827_; lean_object* v_rhs_828_; lean_object* v___x_829_; 
lean_dec(v_shiftRight_781_);
lean_dec(v_shiftLeft_780_);
lean_dec(v_replicate_779_);
lean_dec(v_append_778_);
lean_dec(v_un_777_);
lean_dec(v_bin_776_);
lean_dec(v_extract_775_);
lean_dec(v_const_774_);
lean_dec(v_var_773_);
v_m_825_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_m_825_);
v_n_826_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_n_826_);
v_lhs_827_ = lean_ctor_get(v_t_772_, 2);
lean_inc_ref(v_lhs_827_);
v_rhs_828_ = lean_ctor_get(v_t_772_, 3);
lean_inc_ref(v_rhs_828_);
lean_dec_ref_known(v_t_772_, 4);
v___x_829_ = lean_apply_4(v_arithShiftRight_782_, v_m_825_, v_n_826_, v_lhs_827_, v_rhs_828_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_830_, lean_object* v_a_831_, lean_object* v_t_832_, lean_object* v_var_833_, lean_object* v_const_834_, lean_object* v_extract_835_, lean_object* v_bin_836_, lean_object* v_un_837_, lean_object* v_append_838_, lean_object* v_replicate_839_, lean_object* v_shiftLeft_840_, lean_object* v_shiftRight_841_, lean_object* v_arithShiftRight_842_){
_start:
{
switch(lean_obj_tag(v_t_832_))
{
case 0:
{
lean_object* v_w_843_; lean_object* v_idx_844_; lean_object* v___x_845_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
v_w_843_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_843_);
v_idx_844_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_idx_844_);
lean_dec_ref_known(v_t_832_, 2);
v___x_845_ = lean_apply_2(v_var_833_, v_w_843_, v_idx_844_);
return v___x_845_;
}
case 1:
{
lean_object* v_w_846_; lean_object* v_val_847_; lean_object* v___x_848_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_var_833_);
v_w_846_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_846_);
v_val_847_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_val_847_);
lean_dec_ref_known(v_t_832_, 2);
v___x_848_ = lean_apply_2(v_const_834_, v_w_846_, v_val_847_);
return v___x_848_;
}
case 2:
{
lean_object* v_w_849_; lean_object* v_start_850_; lean_object* v_len_851_; lean_object* v_expr_852_; lean_object* v___x_853_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_w_849_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_849_);
v_start_850_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_start_850_);
v_len_851_ = lean_ctor_get(v_t_832_, 2);
lean_inc(v_len_851_);
v_expr_852_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_expr_852_);
lean_dec_ref_known(v_t_832_, 4);
v___x_853_ = lean_apply_4(v_extract_835_, v_w_849_, v_start_850_, v_len_851_, v_expr_852_);
return v___x_853_;
}
case 3:
{
lean_object* v_w_854_; lean_object* v_lhs_855_; uint8_t v_op_856_; lean_object* v_rhs_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_w_854_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_854_);
v_lhs_855_ = lean_ctor_get(v_t_832_, 1);
lean_inc_ref(v_lhs_855_);
v_op_856_ = lean_ctor_get_uint8(v_t_832_, sizeof(void*)*3 + 8);
v_rhs_857_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_rhs_857_);
lean_dec_ref_known(v_t_832_, 3);
v___x_858_ = lean_box(v_op_856_);
v___x_859_ = lean_apply_4(v_bin_836_, v_w_854_, v_lhs_855_, v___x_858_, v_rhs_857_);
return v___x_859_;
}
case 4:
{
lean_object* v_w_860_; lean_object* v_op_861_; lean_object* v_operand_862_; lean_object* v___x_863_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_w_860_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_860_);
v_op_861_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_op_861_);
v_operand_862_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_operand_862_);
lean_dec_ref_known(v_t_832_, 3);
v___x_863_ = lean_apply_3(v_un_837_, v_w_860_, v_op_861_, v_operand_862_);
return v___x_863_;
}
case 5:
{
lean_object* v_l_864_; lean_object* v_r_865_; lean_object* v_w_866_; lean_object* v_lhs_867_; lean_object* v_rhs_868_; lean_object* v___x_869_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_l_864_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_l_864_);
v_r_865_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_r_865_);
v_w_866_ = lean_ctor_get(v_t_832_, 2);
lean_inc(v_w_866_);
v_lhs_867_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_lhs_867_);
v_rhs_868_ = lean_ctor_get(v_t_832_, 4);
lean_inc_ref(v_rhs_868_);
lean_dec_ref_known(v_t_832_, 5);
v___x_869_ = lean_apply_6(v_append_838_, v_l_864_, v_r_865_, v_w_866_, v_lhs_867_, v_rhs_868_, lean_box(0));
return v___x_869_;
}
case 6:
{
lean_object* v_w_870_; lean_object* v_w_x27_871_; lean_object* v_n_872_; lean_object* v_expr_873_; lean_object* v___x_874_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_w_870_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_w_870_);
v_w_x27_871_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_w_x27_871_);
v_n_872_ = lean_ctor_get(v_t_832_, 2);
lean_inc(v_n_872_);
v_expr_873_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_expr_873_);
lean_dec_ref_known(v_t_832_, 4);
v___x_874_ = lean_apply_5(v_replicate_839_, v_w_870_, v_w_x27_871_, v_n_872_, v_expr_873_, lean_box(0));
return v___x_874_;
}
case 7:
{
lean_object* v_m_875_; lean_object* v_n_876_; lean_object* v_lhs_877_; lean_object* v_rhs_878_; lean_object* v___x_879_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftRight_841_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_m_875_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_m_875_);
v_n_876_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_n_876_);
v_lhs_877_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_lhs_877_);
v_rhs_878_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_rhs_878_);
lean_dec_ref_known(v_t_832_, 4);
v___x_879_ = lean_apply_4(v_shiftLeft_840_, v_m_875_, v_n_876_, v_lhs_877_, v_rhs_878_);
return v___x_879_;
}
case 8:
{
lean_object* v_m_880_; lean_object* v_n_881_; lean_object* v_lhs_882_; lean_object* v_rhs_883_; lean_object* v___x_884_; 
lean_dec(v_arithShiftRight_842_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_m_880_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_m_880_);
v_n_881_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_n_881_);
v_lhs_882_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_lhs_882_);
v_rhs_883_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_rhs_883_);
lean_dec_ref_known(v_t_832_, 4);
v___x_884_ = lean_apply_4(v_shiftRight_841_, v_m_880_, v_n_881_, v_lhs_882_, v_rhs_883_);
return v___x_884_;
}
default: 
{
lean_object* v_m_885_; lean_object* v_n_886_; lean_object* v_lhs_887_; lean_object* v_rhs_888_; lean_object* v___x_889_; 
lean_dec(v_shiftRight_841_);
lean_dec(v_shiftLeft_840_);
lean_dec(v_replicate_839_);
lean_dec(v_append_838_);
lean_dec(v_un_837_);
lean_dec(v_bin_836_);
lean_dec(v_extract_835_);
lean_dec(v_const_834_);
lean_dec(v_var_833_);
v_m_885_ = lean_ctor_get(v_t_832_, 0);
lean_inc(v_m_885_);
v_n_886_ = lean_ctor_get(v_t_832_, 1);
lean_inc(v_n_886_);
v_lhs_887_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_lhs_887_);
v_rhs_888_ = lean_ctor_get(v_t_832_, 3);
lean_inc_ref(v_rhs_888_);
lean_dec_ref_known(v_t_832_, 4);
v___x_889_ = lean_apply_4(v_arithShiftRight_842_, v_m_885_, v_n_886_, v_lhs_887_, v_rhs_888_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_890_, lean_object* v_a_891_, lean_object* v_t_892_, lean_object* v_var_893_, lean_object* v_const_894_, lean_object* v_extract_895_, lean_object* v_bin_896_, lean_object* v_un_897_, lean_object* v_append_898_, lean_object* v_replicate_899_, lean_object* v_shiftLeft_900_, lean_object* v_shiftRight_901_, lean_object* v_arithShiftRight_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_890_, v_a_891_, v_t_892_, v_var_893_, v_const_894_, v_extract_895_, v_bin_896_, v_un_897_, v_append_898_, v_replicate_899_, v_shiftLeft_900_, v_shiftRight_901_, v_arithShiftRight_902_);
lean_dec(v_a_891_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_904_, lean_object* v_idx_905_){
_start:
{
uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; lean_object* v___x_911_; 
v___x_906_ = 5ULL;
v___x_907_ = lean_uint64_of_nat(v_w_904_);
v___x_908_ = lean_uint64_of_nat(v_idx_905_);
v___x_909_ = lean_uint64_mix_hash(v___x_907_, v___x_908_);
v___x_910_ = lean_uint64_mix_hash(v___x_906_, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_911_, 0, v_w_904_);
lean_ctor_set(v___x_911_, 1, v_idx_905_);
lean_ctor_set_uint64(v___x_911_, sizeof(void*)*2, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_912_, lean_object* v_val_913_){
_start:
{
uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; lean_object* v___x_919_; 
v___x_914_ = 7ULL;
v___x_915_ = lean_uint64_of_nat(v_w_912_);
v___x_916_ = l_BitVec_hash(v_w_912_, v_val_913_);
v___x_917_ = lean_uint64_mix_hash(v___x_915_, v___x_916_);
v___x_918_ = lean_uint64_mix_hash(v___x_914_, v___x_917_);
v___x_919_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_919_, 0, v_w_912_);
lean_ctor_set(v___x_919_, 1, v_val_913_);
lean_ctor_set_uint64(v___x_919_, sizeof(void*)*2, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_920_, lean_object* v_start_921_, lean_object* v_len_922_, lean_object* v_expr_923_){
_start:
{
uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___y_928_; 
v___x_924_ = 11ULL;
v___x_925_ = lean_uint64_of_nat(v_start_921_);
v___x_926_ = lean_uint64_of_nat(v_len_922_);
switch(lean_obj_tag(v_expr_923_))
{
case 0:
{
uint64_t v_hashCode_933_; 
v_hashCode_933_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*2);
v___y_928_ = v_hashCode_933_;
goto v___jp_927_;
}
case 1:
{
uint64_t v_hashCode_934_; 
v_hashCode_934_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*2);
v___y_928_ = v_hashCode_934_;
goto v___jp_927_;
}
case 3:
{
uint64_t v_hashCode_935_; 
v_hashCode_935_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*3);
v___y_928_ = v_hashCode_935_;
goto v___jp_927_;
}
case 4:
{
uint64_t v_hashCode_936_; 
v_hashCode_936_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*3);
v___y_928_ = v_hashCode_936_;
goto v___jp_927_;
}
case 5:
{
uint64_t v_hashCode_937_; 
v_hashCode_937_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*5);
v___y_928_ = v_hashCode_937_;
goto v___jp_927_;
}
default: 
{
uint64_t v_hashCode_938_; 
v_hashCode_938_ = lean_ctor_get_uint64(v_expr_923_, sizeof(void*)*4);
v___y_928_ = v_hashCode_938_;
goto v___jp_927_;
}
}
v___jp_927_:
{
uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; lean_object* v___x_932_; 
v___x_929_ = lean_uint64_mix_hash(v___x_926_, v___y_928_);
v___x_930_ = lean_uint64_mix_hash(v___x_925_, v___x_929_);
v___x_931_ = lean_uint64_mix_hash(v___x_924_, v___x_930_);
v___x_932_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_932_, 0, v_w_920_);
lean_ctor_set(v___x_932_, 1, v_start_921_);
lean_ctor_set(v___x_932_, 2, v_len_922_);
lean_ctor_set(v___x_932_, 3, v_expr_923_);
lean_ctor_set_uint64(v___x_932_, sizeof(void*)*4, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_939_, lean_object* v_lhs_940_, uint8_t v_op_941_, lean_object* v_rhs_942_){
_start:
{
uint64_t v___x_943_; uint64_t v___x_944_; uint64_t v___y_946_; uint64_t v___y_947_; uint64_t v___y_948_; uint64_t v___y_955_; 
v___x_943_ = 13ULL;
v___x_944_ = lean_uint64_of_nat(v_w_939_);
switch(lean_obj_tag(v_lhs_940_))
{
case 0:
{
uint64_t v_hashCode_963_; 
v_hashCode_963_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*2);
v___y_955_ = v_hashCode_963_;
goto v___jp_954_;
}
case 1:
{
uint64_t v_hashCode_964_; 
v_hashCode_964_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*2);
v___y_955_ = v_hashCode_964_;
goto v___jp_954_;
}
case 3:
{
uint64_t v_hashCode_965_; 
v_hashCode_965_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*3);
v___y_955_ = v_hashCode_965_;
goto v___jp_954_;
}
case 4:
{
uint64_t v_hashCode_966_; 
v_hashCode_966_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*3);
v___y_955_ = v_hashCode_966_;
goto v___jp_954_;
}
case 5:
{
uint64_t v_hashCode_967_; 
v_hashCode_967_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*5);
v___y_955_ = v_hashCode_967_;
goto v___jp_954_;
}
default: 
{
uint64_t v_hashCode_968_; 
v_hashCode_968_ = lean_ctor_get_uint64(v_lhs_940_, sizeof(void*)*4);
v___y_955_ = v_hashCode_968_;
goto v___jp_954_;
}
}
v___jp_945_:
{
uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; lean_object* v___x_953_; 
v___x_949_ = lean_uint64_mix_hash(v___y_946_, v___y_948_);
v___x_950_ = lean_uint64_mix_hash(v___y_947_, v___x_949_);
v___x_951_ = lean_uint64_mix_hash(v___x_944_, v___x_950_);
v___x_952_ = lean_uint64_mix_hash(v___x_943_, v___x_951_);
v___x_953_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_953_, 0, v_w_939_);
lean_ctor_set(v___x_953_, 1, v_lhs_940_);
lean_ctor_set(v___x_953_, 2, v_rhs_942_);
lean_ctor_set_uint64(v___x_953_, sizeof(void*)*3, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*3 + 8, v_op_941_);
return v___x_953_;
}
v___jp_954_:
{
uint64_t v___x_956_; 
v___x_956_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_941_);
switch(lean_obj_tag(v_rhs_942_))
{
case 0:
{
uint64_t v_hashCode_957_; 
v_hashCode_957_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*2);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_957_;
goto v___jp_945_;
}
case 1:
{
uint64_t v_hashCode_958_; 
v_hashCode_958_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*2);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_958_;
goto v___jp_945_;
}
case 3:
{
uint64_t v_hashCode_959_; 
v_hashCode_959_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*3);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_959_;
goto v___jp_945_;
}
case 4:
{
uint64_t v_hashCode_960_; 
v_hashCode_960_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*3);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_960_;
goto v___jp_945_;
}
case 5:
{
uint64_t v_hashCode_961_; 
v_hashCode_961_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*5);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_961_;
goto v___jp_945_;
}
default: 
{
uint64_t v_hashCode_962_; 
v_hashCode_962_ = lean_ctor_get_uint64(v_rhs_942_, sizeof(void*)*4);
v___y_946_ = v___x_956_;
v___y_947_ = v___y_955_;
v___y_948_ = v_hashCode_962_;
goto v___jp_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_969_, lean_object* v_lhs_970_, lean_object* v_op_971_, lean_object* v_rhs_972_){
_start:
{
uint8_t v_op_boxed_973_; lean_object* v_res_974_; 
v_op_boxed_973_ = lean_unbox(v_op_971_);
v_res_974_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_969_, v_lhs_970_, v_op_boxed_973_, v_rhs_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_975_, lean_object* v_op_976_, lean_object* v_operand_977_){
_start:
{
uint64_t v___x_978_; uint64_t v___x_979_; uint64_t v___x_980_; uint64_t v___y_982_; 
v___x_978_ = 17ULL;
v___x_979_ = lean_uint64_of_nat(v_w_975_);
v___x_980_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_976_);
switch(lean_obj_tag(v_operand_977_))
{
case 0:
{
uint64_t v_hashCode_987_; 
v_hashCode_987_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*2);
v___y_982_ = v_hashCode_987_;
goto v___jp_981_;
}
case 1:
{
uint64_t v_hashCode_988_; 
v_hashCode_988_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*2);
v___y_982_ = v_hashCode_988_;
goto v___jp_981_;
}
case 3:
{
uint64_t v_hashCode_989_; 
v_hashCode_989_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*3);
v___y_982_ = v_hashCode_989_;
goto v___jp_981_;
}
case 4:
{
uint64_t v_hashCode_990_; 
v_hashCode_990_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*3);
v___y_982_ = v_hashCode_990_;
goto v___jp_981_;
}
case 5:
{
uint64_t v_hashCode_991_; 
v_hashCode_991_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*5);
v___y_982_ = v_hashCode_991_;
goto v___jp_981_;
}
default: 
{
uint64_t v_hashCode_992_; 
v_hashCode_992_ = lean_ctor_get_uint64(v_operand_977_, sizeof(void*)*4);
v___y_982_ = v_hashCode_992_;
goto v___jp_981_;
}
}
v___jp_981_:
{
uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_uint64_mix_hash(v___x_980_, v___y_982_);
v___x_984_ = lean_uint64_mix_hash(v___x_979_, v___x_983_);
v___x_985_ = lean_uint64_mix_hash(v___x_978_, v___x_984_);
v___x_986_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_986_, 0, v_w_975_);
lean_ctor_set(v___x_986_, 1, v_op_976_);
lean_ctor_set(v___x_986_, 2, v_operand_977_);
lean_ctor_set_uint64(v___x_986_, sizeof(void*)*3, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_993_, lean_object* v_r_994_, lean_object* v_w_995_, lean_object* v_lhs_996_, lean_object* v_rhs_997_){
_start:
{
uint64_t v___x_998_; uint64_t v___x_999_; uint64_t v___y_1001_; uint64_t v___y_1002_; uint64_t v___y_1008_; 
v___x_998_ = 19ULL;
v___x_999_ = lean_uint64_of_nat(v_w_995_);
switch(lean_obj_tag(v_lhs_996_))
{
case 0:
{
uint64_t v_hashCode_1015_; 
v_hashCode_1015_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*2);
v___y_1008_ = v_hashCode_1015_;
goto v___jp_1007_;
}
case 1:
{
uint64_t v_hashCode_1016_; 
v_hashCode_1016_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*2);
v___y_1008_ = v_hashCode_1016_;
goto v___jp_1007_;
}
case 3:
{
uint64_t v_hashCode_1017_; 
v_hashCode_1017_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*3);
v___y_1008_ = v_hashCode_1017_;
goto v___jp_1007_;
}
case 4:
{
uint64_t v_hashCode_1018_; 
v_hashCode_1018_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*3);
v___y_1008_ = v_hashCode_1018_;
goto v___jp_1007_;
}
case 5:
{
uint64_t v_hashCode_1019_; 
v_hashCode_1019_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*5);
v___y_1008_ = v_hashCode_1019_;
goto v___jp_1007_;
}
default: 
{
uint64_t v_hashCode_1020_; 
v_hashCode_1020_ = lean_ctor_get_uint64(v_lhs_996_, sizeof(void*)*4);
v___y_1008_ = v_hashCode_1020_;
goto v___jp_1007_;
}
}
v___jp_1000_:
{
uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = lean_uint64_mix_hash(v___y_1001_, v___y_1002_);
v___x_1004_ = lean_uint64_mix_hash(v___x_999_, v___x_1003_);
v___x_1005_ = lean_uint64_mix_hash(v___x_998_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_1006_, 0, v_l_993_);
lean_ctor_set(v___x_1006_, 1, v_r_994_);
lean_ctor_set(v___x_1006_, 2, v_w_995_);
lean_ctor_set(v___x_1006_, 3, v_lhs_996_);
lean_ctor_set(v___x_1006_, 4, v_rhs_997_);
lean_ctor_set_uint64(v___x_1006_, sizeof(void*)*5, v___x_1005_);
return v___x_1006_;
}
v___jp_1007_:
{
switch(lean_obj_tag(v_rhs_997_))
{
case 0:
{
uint64_t v_hashCode_1009_; 
v_hashCode_1009_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*2);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1009_;
goto v___jp_1000_;
}
case 1:
{
uint64_t v_hashCode_1010_; 
v_hashCode_1010_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*2);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1010_;
goto v___jp_1000_;
}
case 3:
{
uint64_t v_hashCode_1011_; 
v_hashCode_1011_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*3);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1011_;
goto v___jp_1000_;
}
case 4:
{
uint64_t v_hashCode_1012_; 
v_hashCode_1012_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*3);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1012_;
goto v___jp_1000_;
}
case 5:
{
uint64_t v_hashCode_1013_; 
v_hashCode_1013_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*5);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1013_;
goto v___jp_1000_;
}
default: 
{
uint64_t v_hashCode_1014_; 
v_hashCode_1014_ = lean_ctor_get_uint64(v_rhs_997_, sizeof(void*)*4);
v___y_1001_ = v___y_1008_;
v___y_1002_ = v_hashCode_1014_;
goto v___jp_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_1021_, lean_object* v_r_1022_, lean_object* v_w_1023_, lean_object* v_lhs_1024_, lean_object* v_rhs_1025_, lean_object* v_h_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_1021_, v_r_1022_, v_w_1023_, v_lhs_1024_, v_rhs_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_1028_, lean_object* v_w_x27_1029_, lean_object* v_n_1030_, lean_object* v_expr_1031_){
_start:
{
uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___y_1036_; 
v___x_1032_ = 23ULL;
v___x_1033_ = lean_uint64_of_nat(v_w_x27_1029_);
v___x_1034_ = lean_uint64_of_nat(v_n_1030_);
switch(lean_obj_tag(v_expr_1031_))
{
case 0:
{
uint64_t v_hashCode_1041_; 
v_hashCode_1041_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*2);
v___y_1036_ = v_hashCode_1041_;
goto v___jp_1035_;
}
case 1:
{
uint64_t v_hashCode_1042_; 
v_hashCode_1042_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*2);
v___y_1036_ = v_hashCode_1042_;
goto v___jp_1035_;
}
case 3:
{
uint64_t v_hashCode_1043_; 
v_hashCode_1043_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*3);
v___y_1036_ = v_hashCode_1043_;
goto v___jp_1035_;
}
case 4:
{
uint64_t v_hashCode_1044_; 
v_hashCode_1044_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*3);
v___y_1036_ = v_hashCode_1044_;
goto v___jp_1035_;
}
case 5:
{
uint64_t v_hashCode_1045_; 
v_hashCode_1045_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*5);
v___y_1036_ = v_hashCode_1045_;
goto v___jp_1035_;
}
default: 
{
uint64_t v_hashCode_1046_; 
v_hashCode_1046_ = lean_ctor_get_uint64(v_expr_1031_, sizeof(void*)*4);
v___y_1036_ = v_hashCode_1046_;
goto v___jp_1035_;
}
}
v___jp_1035_:
{
uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1037_ = lean_uint64_mix_hash(v___x_1034_, v___y_1036_);
v___x_1038_ = lean_uint64_mix_hash(v___x_1033_, v___x_1037_);
v___x_1039_ = lean_uint64_mix_hash(v___x_1032_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1040_, 0, v_w_1028_);
lean_ctor_set(v___x_1040_, 1, v_w_x27_1029_);
lean_ctor_set(v___x_1040_, 2, v_n_1030_);
lean_ctor_set(v___x_1040_, 3, v_expr_1031_);
lean_ctor_set_uint64(v___x_1040_, sizeof(void*)*4, v___x_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1047_, lean_object* v_w_x27_1048_, lean_object* v_n_1049_, lean_object* v_expr_1050_, lean_object* v_h_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1047_, v_w_x27_1048_, v_n_1049_, v_expr_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1053_, lean_object* v_n_1054_, lean_object* v_lhs_1055_, lean_object* v_rhs_1056_){
_start:
{
uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v___y_1060_; uint64_t v___y_1061_; uint64_t v___y_1067_; 
v___x_1057_ = 29ULL;
v___x_1058_ = lean_uint64_of_nat(v_m_1053_);
switch(lean_obj_tag(v_lhs_1055_))
{
case 0:
{
uint64_t v_hashCode_1074_; 
v_hashCode_1074_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*2);
v___y_1067_ = v_hashCode_1074_;
goto v___jp_1066_;
}
case 1:
{
uint64_t v_hashCode_1075_; 
v_hashCode_1075_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*2);
v___y_1067_ = v_hashCode_1075_;
goto v___jp_1066_;
}
case 3:
{
uint64_t v_hashCode_1076_; 
v_hashCode_1076_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*3);
v___y_1067_ = v_hashCode_1076_;
goto v___jp_1066_;
}
case 4:
{
uint64_t v_hashCode_1077_; 
v_hashCode_1077_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*3);
v___y_1067_ = v_hashCode_1077_;
goto v___jp_1066_;
}
case 5:
{
uint64_t v_hashCode_1078_; 
v_hashCode_1078_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*5);
v___y_1067_ = v_hashCode_1078_;
goto v___jp_1066_;
}
default: 
{
uint64_t v_hashCode_1079_; 
v_hashCode_1079_ = lean_ctor_get_uint64(v_lhs_1055_, sizeof(void*)*4);
v___y_1067_ = v_hashCode_1079_;
goto v___jp_1066_;
}
}
v___jp_1059_:
{
uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_uint64_mix_hash(v___y_1060_, v___y_1061_);
v___x_1063_ = lean_uint64_mix_hash(v___x_1058_, v___x_1062_);
v___x_1064_ = lean_uint64_mix_hash(v___x_1057_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1065_, 0, v_m_1053_);
lean_ctor_set(v___x_1065_, 1, v_n_1054_);
lean_ctor_set(v___x_1065_, 2, v_lhs_1055_);
lean_ctor_set(v___x_1065_, 3, v_rhs_1056_);
lean_ctor_set_uint64(v___x_1065_, sizeof(void*)*4, v___x_1064_);
return v___x_1065_;
}
v___jp_1066_:
{
switch(lean_obj_tag(v_rhs_1056_))
{
case 0:
{
uint64_t v_hashCode_1068_; 
v_hashCode_1068_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*2);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1068_;
goto v___jp_1059_;
}
case 1:
{
uint64_t v_hashCode_1069_; 
v_hashCode_1069_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*2);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1069_;
goto v___jp_1059_;
}
case 3:
{
uint64_t v_hashCode_1070_; 
v_hashCode_1070_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*3);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1070_;
goto v___jp_1059_;
}
case 4:
{
uint64_t v_hashCode_1071_; 
v_hashCode_1071_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*3);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1071_;
goto v___jp_1059_;
}
case 5:
{
uint64_t v_hashCode_1072_; 
v_hashCode_1072_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*5);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1072_;
goto v___jp_1059_;
}
default: 
{
uint64_t v_hashCode_1073_; 
v_hashCode_1073_ = lean_ctor_get_uint64(v_rhs_1056_, sizeof(void*)*4);
v___y_1060_ = v___y_1067_;
v___y_1061_ = v_hashCode_1073_;
goto v___jp_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1080_, lean_object* v_n_1081_, lean_object* v_lhs_1082_, lean_object* v_rhs_1083_){
_start:
{
uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___y_1087_; uint64_t v___y_1088_; uint64_t v___y_1094_; 
v___x_1084_ = 31ULL;
v___x_1085_ = lean_uint64_of_nat(v_m_1080_);
switch(lean_obj_tag(v_lhs_1082_))
{
case 0:
{
uint64_t v_hashCode_1101_; 
v_hashCode_1101_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*2);
v___y_1094_ = v_hashCode_1101_;
goto v___jp_1093_;
}
case 1:
{
uint64_t v_hashCode_1102_; 
v_hashCode_1102_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*2);
v___y_1094_ = v_hashCode_1102_;
goto v___jp_1093_;
}
case 3:
{
uint64_t v_hashCode_1103_; 
v_hashCode_1103_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*3);
v___y_1094_ = v_hashCode_1103_;
goto v___jp_1093_;
}
case 4:
{
uint64_t v_hashCode_1104_; 
v_hashCode_1104_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*3);
v___y_1094_ = v_hashCode_1104_;
goto v___jp_1093_;
}
case 5:
{
uint64_t v_hashCode_1105_; 
v_hashCode_1105_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*5);
v___y_1094_ = v_hashCode_1105_;
goto v___jp_1093_;
}
default: 
{
uint64_t v_hashCode_1106_; 
v_hashCode_1106_ = lean_ctor_get_uint64(v_lhs_1082_, sizeof(void*)*4);
v___y_1094_ = v_hashCode_1106_;
goto v___jp_1093_;
}
}
v___jp_1086_:
{
uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1089_ = lean_uint64_mix_hash(v___y_1087_, v___y_1088_);
v___x_1090_ = lean_uint64_mix_hash(v___x_1085_, v___x_1089_);
v___x_1091_ = lean_uint64_mix_hash(v___x_1084_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1092_, 0, v_m_1080_);
lean_ctor_set(v___x_1092_, 1, v_n_1081_);
lean_ctor_set(v___x_1092_, 2, v_lhs_1082_);
lean_ctor_set(v___x_1092_, 3, v_rhs_1083_);
lean_ctor_set_uint64(v___x_1092_, sizeof(void*)*4, v___x_1091_);
return v___x_1092_;
}
v___jp_1093_:
{
switch(lean_obj_tag(v_rhs_1083_))
{
case 0:
{
uint64_t v_hashCode_1095_; 
v_hashCode_1095_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*2);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1095_;
goto v___jp_1086_;
}
case 1:
{
uint64_t v_hashCode_1096_; 
v_hashCode_1096_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*2);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1096_;
goto v___jp_1086_;
}
case 3:
{
uint64_t v_hashCode_1097_; 
v_hashCode_1097_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*3);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1097_;
goto v___jp_1086_;
}
case 4:
{
uint64_t v_hashCode_1098_; 
v_hashCode_1098_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*3);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1098_;
goto v___jp_1086_;
}
case 5:
{
uint64_t v_hashCode_1099_; 
v_hashCode_1099_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*5);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1099_;
goto v___jp_1086_;
}
default: 
{
uint64_t v_hashCode_1100_; 
v_hashCode_1100_ = lean_ctor_get_uint64(v_rhs_1083_, sizeof(void*)*4);
v___y_1087_ = v___y_1094_;
v___y_1088_ = v_hashCode_1100_;
goto v___jp_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1107_, lean_object* v_n_1108_, lean_object* v_lhs_1109_, lean_object* v_rhs_1110_){
_start:
{
uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___y_1114_; uint64_t v___y_1115_; uint64_t v___y_1121_; 
v___x_1111_ = 37ULL;
v___x_1112_ = lean_uint64_of_nat(v_m_1107_);
switch(lean_obj_tag(v_lhs_1109_))
{
case 0:
{
uint64_t v_hashCode_1128_; 
v_hashCode_1128_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*2);
v___y_1121_ = v_hashCode_1128_;
goto v___jp_1120_;
}
case 1:
{
uint64_t v_hashCode_1129_; 
v_hashCode_1129_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*2);
v___y_1121_ = v_hashCode_1129_;
goto v___jp_1120_;
}
case 3:
{
uint64_t v_hashCode_1130_; 
v_hashCode_1130_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*3);
v___y_1121_ = v_hashCode_1130_;
goto v___jp_1120_;
}
case 4:
{
uint64_t v_hashCode_1131_; 
v_hashCode_1131_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*3);
v___y_1121_ = v_hashCode_1131_;
goto v___jp_1120_;
}
case 5:
{
uint64_t v_hashCode_1132_; 
v_hashCode_1132_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*5);
v___y_1121_ = v_hashCode_1132_;
goto v___jp_1120_;
}
default: 
{
uint64_t v_hashCode_1133_; 
v_hashCode_1133_ = lean_ctor_get_uint64(v_lhs_1109_, sizeof(void*)*4);
v___y_1121_ = v_hashCode_1133_;
goto v___jp_1120_;
}
}
v___jp_1113_:
{
uint64_t v___x_1116_; uint64_t v___x_1117_; uint64_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_uint64_mix_hash(v___y_1114_, v___y_1115_);
v___x_1117_ = lean_uint64_mix_hash(v___x_1112_, v___x_1116_);
v___x_1118_ = lean_uint64_mix_hash(v___x_1111_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1119_, 0, v_m_1107_);
lean_ctor_set(v___x_1119_, 1, v_n_1108_);
lean_ctor_set(v___x_1119_, 2, v_lhs_1109_);
lean_ctor_set(v___x_1119_, 3, v_rhs_1110_);
lean_ctor_set_uint64(v___x_1119_, sizeof(void*)*4, v___x_1118_);
return v___x_1119_;
}
v___jp_1120_:
{
switch(lean_obj_tag(v_rhs_1110_))
{
case 0:
{
uint64_t v_hashCode_1122_; 
v_hashCode_1122_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*2);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1122_;
goto v___jp_1113_;
}
case 1:
{
uint64_t v_hashCode_1123_; 
v_hashCode_1123_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*2);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1123_;
goto v___jp_1113_;
}
case 3:
{
uint64_t v_hashCode_1124_; 
v_hashCode_1124_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*3);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1124_;
goto v___jp_1113_;
}
case 4:
{
uint64_t v_hashCode_1125_; 
v_hashCode_1125_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*3);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1125_;
goto v___jp_1113_;
}
case 5:
{
uint64_t v_hashCode_1126_; 
v_hashCode_1126_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*5);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1126_;
goto v___jp_1113_;
}
default: 
{
uint64_t v_hashCode_1127_; 
v_hashCode_1127_ = lean_ctor_get_uint64(v_rhs_1110_, sizeof(void*)*4);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v_hashCode_1127_;
goto v___jp_1113_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1134_){
_start:
{
switch(lean_obj_tag(v_x_1134_))
{
case 0:
{
uint64_t v_hashCode_1135_; 
v_hashCode_1135_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*2);
return v_hashCode_1135_;
}
case 1:
{
uint64_t v_hashCode_1136_; 
v_hashCode_1136_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*2);
return v_hashCode_1136_;
}
case 3:
{
uint64_t v_hashCode_1137_; 
v_hashCode_1137_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*3);
return v_hashCode_1137_;
}
case 4:
{
uint64_t v_hashCode_1138_; 
v_hashCode_1138_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*3);
return v_hashCode_1138_;
}
case 5:
{
uint64_t v_hashCode_1139_; 
v_hashCode_1139_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*5);
return v_hashCode_1139_;
}
default: 
{
uint64_t v_hashCode_1140_; 
v_hashCode_1140_ = lean_ctor_get_uint64(v_x_1134_, sizeof(void*)*4);
return v_hashCode_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* v_x_1141_){
_start:
{
uint64_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1141_);
lean_dec_ref(v_x_1141_);
v_r_1143_ = lean_box_uint64(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
switch(lean_obj_tag(v_x_1145_))
{
case 0:
{
uint64_t v_hashCode_1146_; 
v_hashCode_1146_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*2);
return v_hashCode_1146_;
}
case 1:
{
uint64_t v_hashCode_1147_; 
v_hashCode_1147_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*2);
return v_hashCode_1147_;
}
case 3:
{
uint64_t v_hashCode_1148_; 
v_hashCode_1148_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*3);
return v_hashCode_1148_;
}
case 4:
{
uint64_t v_hashCode_1149_; 
v_hashCode_1149_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*3);
return v_hashCode_1149_;
}
case 5:
{
uint64_t v_hashCode_1150_; 
v_hashCode_1150_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*5);
return v_hashCode_1150_;
}
default: 
{
uint64_t v_hashCode_1151_; 
v_hashCode_1151_ = lean_ctor_get_uint64(v_x_1145_, sizeof(void*)*4);
return v_hashCode_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
uint64_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1152_, v_x_1153_);
lean_dec_ref(v_x_1153_);
lean_dec(v_a_1152_);
v_r_1155_ = lean_box_uint64(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object* v_expr_1156_){
_start:
{
switch(lean_obj_tag(v_expr_1156_))
{
case 0:
{
uint64_t v_hashCode_1157_; 
v_hashCode_1157_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*2);
return v_hashCode_1157_;
}
case 1:
{
uint64_t v_hashCode_1158_; 
v_hashCode_1158_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*2);
return v_hashCode_1158_;
}
case 3:
{
uint64_t v_hashCode_1159_; 
v_hashCode_1159_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*3);
return v_hashCode_1159_;
}
case 4:
{
uint64_t v_hashCode_1160_; 
v_hashCode_1160_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*3);
return v_hashCode_1160_;
}
case 5:
{
uint64_t v_hashCode_1161_; 
v_hashCode_1161_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*5);
return v_hashCode_1161_;
}
default: 
{
uint64_t v_hashCode_1162_; 
v_hashCode_1162_ = lean_ctor_get_uint64(v_expr_1156_, sizeof(void*)*4);
return v_hashCode_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object* v_expr_1163_){
_start:
{
uint64_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(v_expr_1163_);
lean_dec_ref(v_expr_1163_);
v_r_1165_ = lean_box_uint64(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1167_){
_start:
{
lean_object* v___f_1168_; 
v___f_1168_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0));
return v___f_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* v_w_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_1169_);
lean_dec(v_w_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1171_, lean_object* v_r_1172_){
_start:
{
size_t v___x_1173_; size_t v___x_1174_; uint8_t v___x_1175_; uint64_t v___y_1177_; uint64_t v___y_1178_; uint64_t v___y_1259_; 
v___x_1173_ = lean_ptr_addr(v_l_1171_);
v___x_1174_ = lean_ptr_addr(v_r_1172_);
v___x_1175_ = lean_usize_dec_eq(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
switch(lean_obj_tag(v_l_1171_))
{
case 0:
{
uint64_t v_hashCode_1266_; 
v_hashCode_1266_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*2);
v___y_1259_ = v_hashCode_1266_;
goto v___jp_1258_;
}
case 1:
{
uint64_t v_hashCode_1267_; 
v_hashCode_1267_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*2);
v___y_1259_ = v_hashCode_1267_;
goto v___jp_1258_;
}
case 3:
{
uint64_t v_hashCode_1268_; 
v_hashCode_1268_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*3);
v___y_1259_ = v_hashCode_1268_;
goto v___jp_1258_;
}
case 4:
{
uint64_t v_hashCode_1269_; 
v_hashCode_1269_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*3);
v___y_1259_ = v_hashCode_1269_;
goto v___jp_1258_;
}
case 5:
{
uint64_t v_hashCode_1270_; 
v_hashCode_1270_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*5);
v___y_1259_ = v_hashCode_1270_;
goto v___jp_1258_;
}
default: 
{
uint64_t v_hashCode_1271_; 
v_hashCode_1271_ = lean_ctor_get_uint64(v_l_1171_, sizeof(void*)*4);
v___y_1259_ = v_hashCode_1271_;
goto v___jp_1258_;
}
}
}
else
{
return v___x_1175_;
}
v___jp_1176_:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_uint64_dec_eq(v___y_1177_, v___y_1178_);
if (v___x_1179_ == 0)
{
return v___x_1175_;
}
else
{
if (v___x_1175_ == 0)
{
switch(lean_obj_tag(v_l_1171_))
{
case 0:
{
if (lean_obj_tag(v_r_1172_) == 0)
{
lean_object* v_idx_1180_; lean_object* v_idx_1181_; uint8_t v___x_1182_; 
v_idx_1180_ = lean_ctor_get(v_l_1171_, 1);
v_idx_1181_ = lean_ctor_get(v_r_1172_, 1);
v___x_1182_ = lean_nat_dec_eq(v_idx_1180_, v_idx_1181_);
return v___x_1182_;
}
else
{
return v___x_1175_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1172_) == 1)
{
lean_object* v_val_1183_; lean_object* v_val_1184_; uint8_t v___x_1185_; 
v_val_1183_ = lean_ctor_get(v_l_1171_, 1);
v_val_1184_ = lean_ctor_get(v_r_1172_, 1);
v___x_1185_ = lean_nat_dec_eq(v_val_1183_, v_val_1184_);
return v___x_1185_;
}
else
{
return v___x_1175_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1172_) == 2)
{
lean_object* v_w_1186_; lean_object* v_start_1187_; lean_object* v_expr_1188_; lean_object* v_w_1189_; lean_object* v_start_1190_; lean_object* v_expr_1191_; uint8_t v___x_1192_; 
v_w_1186_ = lean_ctor_get(v_l_1171_, 0);
v_start_1187_ = lean_ctor_get(v_l_1171_, 1);
v_expr_1188_ = lean_ctor_get(v_l_1171_, 3);
v_w_1189_ = lean_ctor_get(v_r_1172_, 0);
v_start_1190_ = lean_ctor_get(v_r_1172_, 1);
v_expr_1191_ = lean_ctor_get(v_r_1172_, 3);
v___x_1192_ = lean_nat_dec_eq(v_w_1186_, v_w_1189_);
if (v___x_1192_ == 0)
{
return v___x_1192_;
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_eq(v_start_1187_, v_start_1190_);
if (v___x_1193_ == 0)
{
return v___x_1193_;
}
else
{
v_l_1171_ = v_expr_1188_;
v_r_1172_ = v_expr_1191_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1172_) == 3)
{
lean_object* v_lhs_1195_; uint8_t v_op_1196_; lean_object* v_rhs_1197_; lean_object* v_lhs_1198_; uint8_t v_op_1199_; lean_object* v_rhs_1200_; uint8_t v___x_1201_; 
v_lhs_1195_ = lean_ctor_get(v_l_1171_, 1);
v_op_1196_ = lean_ctor_get_uint8(v_l_1171_, sizeof(void*)*3 + 8);
v_rhs_1197_ = lean_ctor_get(v_l_1171_, 2);
v_lhs_1198_ = lean_ctor_get(v_r_1172_, 1);
v_op_1199_ = lean_ctor_get_uint8(v_r_1172_, sizeof(void*)*3 + 8);
v_rhs_1200_ = lean_ctor_get(v_r_1172_, 2);
v___x_1201_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_op_1196_, v_op_1199_);
if (v___x_1201_ == 0)
{
return v___x_1201_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1195_, v_lhs_1198_);
if (v___x_1202_ == 0)
{
return v___x_1202_;
}
else
{
v_l_1171_ = v_rhs_1197_;
v_r_1172_ = v_rhs_1200_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1172_) == 4)
{
lean_object* v_op_1204_; lean_object* v_operand_1205_; lean_object* v_op_1206_; lean_object* v_operand_1207_; uint8_t v___x_1208_; 
v_op_1204_ = lean_ctor_get(v_l_1171_, 1);
v_operand_1205_ = lean_ctor_get(v_l_1171_, 2);
v_op_1206_ = lean_ctor_get(v_r_1172_, 1);
v_operand_1207_ = lean_ctor_get(v_r_1172_, 2);
v___x_1208_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1204_, v_op_1206_);
if (v___x_1208_ == 0)
{
return v___x_1208_;
}
else
{
v_l_1171_ = v_operand_1205_;
v_r_1172_ = v_operand_1207_;
goto _start;
}
}
else
{
return v___x_1175_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1172_) == 5)
{
lean_object* v_l_1210_; lean_object* v_r_1211_; lean_object* v_lhs_1212_; lean_object* v_rhs_1213_; lean_object* v_l_1214_; lean_object* v_r_1215_; lean_object* v_lhs_1216_; lean_object* v_rhs_1217_; uint8_t v___x_1218_; 
v_l_1210_ = lean_ctor_get(v_l_1171_, 0);
v_r_1211_ = lean_ctor_get(v_l_1171_, 1);
v_lhs_1212_ = lean_ctor_get(v_l_1171_, 3);
v_rhs_1213_ = lean_ctor_get(v_l_1171_, 4);
v_l_1214_ = lean_ctor_get(v_r_1172_, 0);
v_r_1215_ = lean_ctor_get(v_r_1172_, 1);
v_lhs_1216_ = lean_ctor_get(v_r_1172_, 3);
v_rhs_1217_ = lean_ctor_get(v_r_1172_, 4);
v___x_1218_ = lean_nat_dec_eq(v_l_1210_, v_l_1214_);
if (v___x_1218_ == 0)
{
return v___x_1218_;
}
else
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_nat_dec_eq(v_r_1211_, v_r_1215_);
if (v___x_1219_ == 0)
{
return v___x_1219_;
}
else
{
uint8_t v___x_1220_; 
v___x_1220_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1212_, v_lhs_1216_);
if (v___x_1220_ == 0)
{
return v___x_1220_;
}
else
{
v_l_1171_ = v_rhs_1213_;
v_r_1172_ = v_rhs_1217_;
goto _start;
}
}
}
}
else
{
return v___x_1175_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1172_) == 6)
{
lean_object* v_w_1222_; lean_object* v_n_1223_; lean_object* v_expr_1224_; lean_object* v_w_1225_; lean_object* v_n_1226_; lean_object* v_expr_1227_; uint8_t v___x_1228_; 
v_w_1222_ = lean_ctor_get(v_l_1171_, 0);
v_n_1223_ = lean_ctor_get(v_l_1171_, 2);
v_expr_1224_ = lean_ctor_get(v_l_1171_, 3);
v_w_1225_ = lean_ctor_get(v_r_1172_, 0);
v_n_1226_ = lean_ctor_get(v_r_1172_, 2);
v_expr_1227_ = lean_ctor_get(v_r_1172_, 3);
v___x_1228_ = lean_nat_dec_eq(v_n_1223_, v_n_1226_);
if (v___x_1228_ == 0)
{
return v___x_1228_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_nat_dec_eq(v_w_1222_, v_w_1225_);
if (v___x_1229_ == 0)
{
return v___x_1229_;
}
else
{
v_l_1171_ = v_expr_1224_;
v_r_1172_ = v_expr_1227_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1172_) == 7)
{
lean_object* v_n_1231_; lean_object* v_lhs_1232_; lean_object* v_rhs_1233_; lean_object* v_n_1234_; lean_object* v_lhs_1235_; lean_object* v_rhs_1236_; uint8_t v___x_1237_; 
v_n_1231_ = lean_ctor_get(v_l_1171_, 1);
v_lhs_1232_ = lean_ctor_get(v_l_1171_, 2);
v_rhs_1233_ = lean_ctor_get(v_l_1171_, 3);
v_n_1234_ = lean_ctor_get(v_r_1172_, 1);
v_lhs_1235_ = lean_ctor_get(v_r_1172_, 2);
v_rhs_1236_ = lean_ctor_get(v_r_1172_, 3);
v___x_1237_ = lean_nat_dec_eq(v_n_1231_, v_n_1234_);
if (v___x_1237_ == 0)
{
return v___x_1237_;
}
else
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1232_, v_lhs_1235_);
if (v___x_1238_ == 0)
{
return v___x_1238_;
}
else
{
v_l_1171_ = v_rhs_1233_;
v_r_1172_ = v_rhs_1236_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1172_) == 8)
{
lean_object* v_n_1240_; lean_object* v_lhs_1241_; lean_object* v_rhs_1242_; lean_object* v_n_1243_; lean_object* v_lhs_1244_; lean_object* v_rhs_1245_; uint8_t v___x_1246_; 
v_n_1240_ = lean_ctor_get(v_l_1171_, 1);
v_lhs_1241_ = lean_ctor_get(v_l_1171_, 2);
v_rhs_1242_ = lean_ctor_get(v_l_1171_, 3);
v_n_1243_ = lean_ctor_get(v_r_1172_, 1);
v_lhs_1244_ = lean_ctor_get(v_r_1172_, 2);
v_rhs_1245_ = lean_ctor_get(v_r_1172_, 3);
v___x_1246_ = lean_nat_dec_eq(v_n_1240_, v_n_1243_);
if (v___x_1246_ == 0)
{
return v___x_1246_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1241_, v_lhs_1244_);
if (v___x_1247_ == 0)
{
return v___x_1247_;
}
else
{
v_l_1171_ = v_rhs_1242_;
v_r_1172_ = v_rhs_1245_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
default: 
{
if (lean_obj_tag(v_r_1172_) == 9)
{
lean_object* v_n_1249_; lean_object* v_lhs_1250_; lean_object* v_rhs_1251_; lean_object* v_n_1252_; lean_object* v_lhs_1253_; lean_object* v_rhs_1254_; uint8_t v___x_1255_; 
v_n_1249_ = lean_ctor_get(v_l_1171_, 1);
v_lhs_1250_ = lean_ctor_get(v_l_1171_, 2);
v_rhs_1251_ = lean_ctor_get(v_l_1171_, 3);
v_n_1252_ = lean_ctor_get(v_r_1172_, 1);
v_lhs_1253_ = lean_ctor_get(v_r_1172_, 2);
v_rhs_1254_ = lean_ctor_get(v_r_1172_, 3);
v___x_1255_ = lean_nat_dec_eq(v_n_1249_, v_n_1252_);
if (v___x_1255_ == 0)
{
return v___x_1255_;
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1250_, v_lhs_1253_);
if (v___x_1256_ == 0)
{
return v___x_1256_;
}
else
{
v_l_1171_ = v_rhs_1251_;
v_r_1172_ = v_rhs_1254_;
goto _start;
}
}
}
else
{
return v___x_1175_;
}
}
}
}
else
{
return v___x_1175_;
}
}
}
v___jp_1258_:
{
switch(lean_obj_tag(v_r_1172_))
{
case 0:
{
uint64_t v_hashCode_1260_; 
v_hashCode_1260_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*2);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1260_;
goto v___jp_1176_;
}
case 1:
{
uint64_t v_hashCode_1261_; 
v_hashCode_1261_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*2);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1261_;
goto v___jp_1176_;
}
case 3:
{
uint64_t v_hashCode_1262_; 
v_hashCode_1262_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*3);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1262_;
goto v___jp_1176_;
}
case 4:
{
uint64_t v_hashCode_1263_; 
v_hashCode_1263_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*3);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1263_;
goto v___jp_1176_;
}
case 5:
{
uint64_t v_hashCode_1264_; 
v_hashCode_1264_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*5);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1264_;
goto v___jp_1176_;
}
default: 
{
uint64_t v_hashCode_1265_; 
v_hashCode_1265_ = lean_ctor_get_uint64(v_r_1172_, sizeof(void*)*4);
v___y_1177_ = v___y_1259_;
v___y_1178_ = v_hashCode_1265_;
goto v___jp_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1272_, lean_object* v_r_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1272_, v_r_1273_);
lean_dec_ref(v_r_1273_);
lean_dec_ref(v_l_1272_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1276_, lean_object* v_l_1277_, lean_object* v_r_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1277_, v_r_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1280_, lean_object* v_l_1281_, lean_object* v_r_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1280_, v_l_1281_, v_r_1282_);
lean_dec_ref(v_r_1282_);
lean_dec_ref(v_l_1281_);
lean_dec(v_w_1280_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1294_, lean_object* v_x_1295_){
_start:
{
switch(lean_obj_tag(v_x_1295_))
{
case 0:
{
lean_object* v_idx_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_w_1294_);
v_idx_1296_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_idx_1296_);
lean_dec_ref_known(v_x_1295_, 2);
v___x_1297_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1298_ = l_Nat_reprFast(v_idx_1296_);
v___x_1299_ = lean_string_append(v___x_1297_, v___x_1298_);
lean_dec_ref(v___x_1298_);
return v___x_1299_;
}
case 1:
{
lean_object* v_val_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_val_1300_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_val_1300_);
lean_dec_ref_known(v_x_1295_, 2);
v___x_1301_ = l_BitVec_repr(v_w_1294_, v_val_1300_);
v___x_1302_ = l_Std_Format_defWidth;
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = l_Std_Format_pretty(v___x_1301_, v___x_1302_, v___x_1303_, v___x_1303_);
return v___x_1304_;
}
case 2:
{
lean_object* v_w_1305_; lean_object* v_start_1306_; lean_object* v_expr_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_w_1305_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_w_1305_);
v_start_1306_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_start_1306_);
v_expr_1307_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_expr_1307_);
lean_dec_ref_known(v_x_1295_, 4);
v___x_1308_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1305_, v_expr_1307_);
v___x_1309_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1310_ = lean_string_append(v___x_1308_, v___x_1309_);
v___x_1311_ = l_Nat_reprFast(v_start_1306_);
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
v___x_1315_ = l_Nat_reprFast(v_w_1294_);
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
return v___x_1318_;
}
case 3:
{
lean_object* v_lhs_1319_; uint8_t v_op_1320_; lean_object* v_rhs_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_lhs_1319_ = lean_ctor_get(v_x_1295_, 1);
lean_inc_ref(v_lhs_1319_);
v_op_1320_ = lean_ctor_get_uint8(v_x_1295_, sizeof(void*)*3 + 8);
v_rhs_1321_ = lean_ctor_get(v_x_1295_, 2);
lean_inc_ref(v_rhs_1321_);
lean_dec_ref_known(v_x_1295_, 3);
v___x_1322_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1294_);
v___x_1323_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_lhs_1319_);
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
v___x_1327_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1320_);
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = lean_string_append(v___x_1328_, v___x_1325_);
v___x_1330_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_rhs_1321_);
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
return v___x_1333_;
}
case 4:
{
lean_object* v_op_1334_; lean_object* v_operand_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_op_1334_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_op_1334_);
v_operand_1335_ = lean_ctor_get(v_x_1295_, 2);
lean_inc_ref(v_operand_1335_);
lean_dec_ref_known(v_x_1295_, 3);
v___x_1336_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1337_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1334_);
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
v___x_1341_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_operand_1335_);
v___x_1342_ = lean_string_append(v___x_1340_, v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
return v___x_1344_;
}
case 5:
{
lean_object* v_l_1345_; lean_object* v_r_1346_; lean_object* v_lhs_1347_; lean_object* v_rhs_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_w_1294_);
v_l_1345_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_l_1345_);
v_r_1346_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_r_1346_);
v_lhs_1347_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_lhs_1347_);
v_rhs_1348_ = lean_ctor_get(v_x_1295_, 4);
lean_inc_ref(v_rhs_1348_);
lean_dec_ref_known(v_x_1295_, 5);
v___x_1349_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1350_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1345_, v_lhs_1347_);
v___x_1351_ = lean_string_append(v___x_1349_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
v___x_1354_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1346_, v_rhs_1348_);
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
return v___x_1357_;
}
case 6:
{
lean_object* v_w_1358_; lean_object* v_n_1359_; lean_object* v_expr_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_w_1294_);
v_w_1358_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_w_1358_);
v_n_1359_ = lean_ctor_get(v_x_1295_, 2);
lean_inc(v_n_1359_);
v_expr_1360_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_expr_1360_);
lean_dec_ref_known(v_x_1295_, 4);
v___x_1361_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1362_ = l_Nat_reprFast(v_n_1359_);
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
v___x_1366_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1358_, v_expr_1360_);
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
lean_dec_ref(v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
return v___x_1369_;
}
case 7:
{
lean_object* v_n_1370_; lean_object* v_lhs_1371_; lean_object* v_rhs_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_n_1370_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_n_1370_);
v_lhs_1371_ = lean_ctor_get(v_x_1295_, 2);
lean_inc_ref(v_lhs_1371_);
v_rhs_1372_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_rhs_1372_);
lean_dec_ref_known(v_x_1295_, 4);
v___x_1373_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1374_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_lhs_1371_);
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1370_, v_rhs_1372_);
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
return v___x_1381_;
}
case 8:
{
lean_object* v_n_1382_; lean_object* v_lhs_1383_; lean_object* v_rhs_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_n_1382_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_n_1382_);
v_lhs_1383_ = lean_ctor_get(v_x_1295_, 2);
lean_inc_ref(v_lhs_1383_);
v_rhs_1384_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_rhs_1384_);
lean_dec_ref_known(v_x_1295_, 4);
v___x_1385_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1386_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_lhs_1383_);
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
lean_dec_ref(v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
v___x_1390_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1382_, v_rhs_1384_);
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
return v___x_1393_;
}
default: 
{
lean_object* v_n_1394_; lean_object* v_lhs_1395_; lean_object* v_rhs_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_n_1394_ = lean_ctor_get(v_x_1295_, 1);
lean_inc(v_n_1394_);
v_lhs_1395_ = lean_ctor_get(v_x_1295_, 2);
lean_inc_ref(v_lhs_1395_);
v_rhs_1396_ = lean_ctor_get(v_x_1295_, 3);
lean_inc_ref(v_rhs_1396_);
lean_dec_ref_known(v_x_1295_, 4);
v___x_1397_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1398_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1294_, v_lhs_1395_);
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
v___x_1402_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1394_, v_rhs_1396_);
v___x_1403_ = lean_string_append(v___x_1401_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1407_, 0, v_w_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1408_, lean_object* v_idx_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_RArray_getImpl___redArg(v_assign_1408_, v_idx_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1411_, lean_object* v_idx_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1411_, v_idx_1412_);
lean_dec(v_idx_1412_);
lean_dec_ref(v_assign_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1414_, lean_object* v_assign_1415_, lean_object* v_x_1416_){
_start:
{
switch(lean_obj_tag(v_x_1416_))
{
case 0:
{
lean_object* v_idx_1417_; lean_object* v_packedBv_1418_; lean_object* v_w_1419_; lean_object* v_bv_1420_; uint8_t v___x_1421_; 
v_idx_1417_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_idx_1417_);
lean_dec_ref_known(v_x_1416_, 2);
v_packedBv_1418_ = l_Lean_RArray_getImpl___redArg(v_assign_1415_, v_idx_1417_);
lean_dec(v_idx_1417_);
v_w_1419_ = lean_ctor_get(v_packedBv_1418_, 0);
lean_inc(v_w_1419_);
v_bv_1420_ = lean_ctor_get(v_packedBv_1418_, 1);
lean_inc(v_bv_1420_);
lean_dec(v_packedBv_1418_);
v___x_1421_ = lean_nat_dec_eq(v_w_1419_, v_w_1414_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = l_BitVec_setWidth(v_w_1419_, v_w_1414_, v_bv_1420_);
lean_dec(v_bv_1420_);
lean_dec(v_w_1414_);
lean_dec(v_w_1419_);
return v___x_1422_;
}
else
{
lean_dec(v_w_1419_);
lean_dec(v_w_1414_);
return v_bv_1420_;
}
}
case 1:
{
lean_object* v_val_1423_; 
lean_dec(v_w_1414_);
v_val_1423_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_x_1416_, 2);
return v_val_1423_;
}
case 2:
{
lean_object* v_w_1424_; lean_object* v_start_1425_; lean_object* v_expr_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_w_1424_ = lean_ctor_get(v_x_1416_, 0);
lean_inc(v_w_1424_);
v_start_1425_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_start_1425_);
v_expr_1426_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_expr_1426_);
lean_dec_ref_known(v_x_1416_, 4);
v___x_1427_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1424_, v_assign_1415_, v_expr_1426_);
v___x_1428_ = l_BitVec_extractLsb_x27___redArg(v_start_1425_, v_w_1414_, v___x_1427_);
lean_dec(v___x_1427_);
lean_dec(v_w_1414_);
lean_dec(v_start_1425_);
return v___x_1428_;
}
case 3:
{
lean_object* v_lhs_1429_; uint8_t v_op_1430_; lean_object* v_rhs_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_lhs_1429_ = lean_ctor_get(v_x_1416_, 1);
lean_inc_ref(v_lhs_1429_);
v_op_1430_ = lean_ctor_get_uint8(v_x_1416_, sizeof(void*)*3 + 8);
v_rhs_1431_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_rhs_1431_);
lean_dec_ref_known(v_x_1416_, 3);
lean_inc_n(v_w_1414_, 2);
v___x_1432_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_lhs_1429_);
v___x_1433_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_rhs_1431_);
v___x_1434_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1414_, v_op_1430_, v___x_1432_, v___x_1433_);
lean_dec(v___x_1433_);
lean_dec(v___x_1432_);
lean_dec(v_w_1414_);
return v___x_1434_;
}
case 4:
{
lean_object* v_op_1435_; lean_object* v_operand_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_op_1435_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_op_1435_);
v_operand_1436_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_operand_1436_);
lean_dec_ref_known(v_x_1416_, 3);
lean_inc(v_w_1414_);
v___x_1437_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_operand_1436_);
v___x_1438_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1414_, v_op_1435_, v___x_1437_);
lean_dec(v_op_1435_);
return v___x_1438_;
}
case 5:
{
lean_object* v_l_1439_; lean_object* v_r_1440_; lean_object* v_lhs_1441_; lean_object* v_rhs_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v_w_1414_);
v_l_1439_ = lean_ctor_get(v_x_1416_, 0);
lean_inc(v_l_1439_);
v_r_1440_ = lean_ctor_get(v_x_1416_, 1);
lean_inc_n(v_r_1440_, 2);
v_lhs_1441_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_lhs_1441_);
v_rhs_1442_ = lean_ctor_get(v_x_1416_, 4);
lean_inc_ref(v_rhs_1442_);
lean_dec_ref_known(v_x_1416_, 5);
v___x_1443_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1439_, v_assign_1415_, v_lhs_1441_);
v___x_1444_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1440_, v_assign_1415_, v_rhs_1442_);
v___x_1445_ = l_BitVec_append___redArg(v_r_1440_, v___x_1443_, v___x_1444_);
lean_dec(v___x_1444_);
lean_dec(v___x_1443_);
lean_dec(v_r_1440_);
return v___x_1445_;
}
case 6:
{
lean_object* v_w_1446_; lean_object* v_n_1447_; lean_object* v_expr_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_w_1414_);
v_w_1446_ = lean_ctor_get(v_x_1416_, 0);
lean_inc_n(v_w_1446_, 2);
v_n_1447_ = lean_ctor_get(v_x_1416_, 2);
lean_inc(v_n_1447_);
v_expr_1448_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_expr_1448_);
lean_dec_ref_known(v_x_1416_, 4);
v___x_1449_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1446_, v_assign_1415_, v_expr_1448_);
v___x_1450_ = l_BitVec_replicate(v_w_1446_, v_n_1447_, v___x_1449_);
lean_dec(v___x_1449_);
lean_dec(v_n_1447_);
lean_dec(v_w_1446_);
return v___x_1450_;
}
case 7:
{
lean_object* v_n_1451_; lean_object* v_lhs_1452_; lean_object* v_rhs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_n_1451_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_n_1451_);
v_lhs_1452_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_lhs_1452_);
v_rhs_1453_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_rhs_1453_);
lean_dec_ref_known(v_x_1416_, 4);
lean_inc(v_w_1414_);
v___x_1454_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_lhs_1452_);
v___x_1455_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1451_, v_assign_1415_, v_rhs_1453_);
v___x_1456_ = l_BitVec_shiftLeft(v_w_1414_, v___x_1454_, v___x_1455_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v_w_1414_);
return v___x_1456_;
}
case 8:
{
lean_object* v_n_1457_; lean_object* v_lhs_1458_; lean_object* v_rhs_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_n_1457_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_n_1457_);
v_lhs_1458_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_lhs_1458_);
v_rhs_1459_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_rhs_1459_);
lean_dec_ref_known(v_x_1416_, 4);
v___x_1460_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_lhs_1458_);
v___x_1461_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1457_, v_assign_1415_, v_rhs_1459_);
v___x_1462_ = lean_nat_shiftr(v___x_1460_, v___x_1461_);
lean_dec(v___x_1461_);
lean_dec(v___x_1460_);
return v___x_1462_;
}
default: 
{
lean_object* v_n_1463_; lean_object* v_lhs_1464_; lean_object* v_rhs_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_n_1463_ = lean_ctor_get(v_x_1416_, 1);
lean_inc(v_n_1463_);
v_lhs_1464_ = lean_ctor_get(v_x_1416_, 2);
lean_inc_ref(v_lhs_1464_);
v_rhs_1465_ = lean_ctor_get(v_x_1416_, 3);
lean_inc_ref(v_rhs_1465_);
lean_dec_ref_known(v_x_1416_, 4);
lean_inc(v_w_1414_);
v___x_1466_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1414_, v_assign_1415_, v_lhs_1464_);
v___x_1467_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1463_, v_assign_1415_, v_rhs_1465_);
v___x_1468_ = l_BitVec_sshiftRight(v_w_1414_, v___x_1466_, v___x_1467_);
lean_dec(v___x_1467_);
lean_dec(v_w_1414_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1469_, lean_object* v_assign_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1469_, v_assign_1470_, v_x_1471_);
lean_dec_ref(v_assign_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* v_w_1473_, lean_object* v_x_1474_, lean_object* v_h__1_1475_, lean_object* v_h__2_1476_, lean_object* v_h__3_1477_, lean_object* v_h__4_1478_, lean_object* v_h__5_1479_, lean_object* v_h__6_1480_, lean_object* v_h__7_1481_, lean_object* v_h__8_1482_, lean_object* v_h__9_1483_, lean_object* v_h__10_1484_){
_start:
{
switch(lean_obj_tag(v_x_1474_))
{
case 0:
{
lean_object* v_idx_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
v_idx_1485_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_idx_1485_);
lean_dec_ref_known(v_x_1474_, 2);
v___x_1486_ = lean_apply_2(v_h__1_1475_, v_w_1473_, v_idx_1485_);
return v___x_1486_;
}
case 1:
{
lean_object* v_val_1487_; lean_object* v___x_1488_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__1_1475_);
v_val_1487_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_x_1474_, 2);
v___x_1488_ = lean_apply_2(v_h__2_1476_, v_w_1473_, v_val_1487_);
return v___x_1488_;
}
case 2:
{
lean_object* v_w_1489_; lean_object* v_start_1490_; lean_object* v_expr_1491_; lean_object* v___x_1492_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_w_1489_ = lean_ctor_get(v_x_1474_, 0);
lean_inc(v_w_1489_);
v_start_1490_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_start_1490_);
v_expr_1491_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_expr_1491_);
lean_dec_ref_known(v_x_1474_, 4);
v___x_1492_ = lean_apply_4(v_h__3_1477_, v_w_1473_, v_w_1489_, v_start_1490_, v_expr_1491_);
return v___x_1492_;
}
case 3:
{
lean_object* v_lhs_1493_; uint8_t v_op_1494_; lean_object* v_rhs_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_lhs_1493_ = lean_ctor_get(v_x_1474_, 1);
lean_inc_ref(v_lhs_1493_);
v_op_1494_ = lean_ctor_get_uint8(v_x_1474_, sizeof(void*)*3 + 8);
v_rhs_1495_ = lean_ctor_get(v_x_1474_, 2);
lean_inc_ref(v_rhs_1495_);
lean_dec_ref_known(v_x_1474_, 3);
v___x_1496_ = lean_box(v_op_1494_);
v___x_1497_ = lean_apply_4(v_h__4_1478_, v_w_1473_, v_lhs_1493_, v___x_1496_, v_rhs_1495_);
return v___x_1497_;
}
case 4:
{
lean_object* v_op_1498_; lean_object* v_operand_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_op_1498_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_op_1498_);
v_operand_1499_ = lean_ctor_get(v_x_1474_, 2);
lean_inc_ref(v_operand_1499_);
lean_dec_ref_known(v_x_1474_, 3);
v___x_1500_ = lean_apply_3(v_h__5_1479_, v_w_1473_, v_op_1498_, v_operand_1499_);
return v___x_1500_;
}
case 5:
{
lean_object* v_l_1501_; lean_object* v_r_1502_; lean_object* v_lhs_1503_; lean_object* v_rhs_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_l_1501_ = lean_ctor_get(v_x_1474_, 0);
lean_inc(v_l_1501_);
v_r_1502_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_r_1502_);
v_lhs_1503_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_lhs_1503_);
v_rhs_1504_ = lean_ctor_get(v_x_1474_, 4);
lean_inc_ref(v_rhs_1504_);
lean_dec_ref_known(v_x_1474_, 5);
v___x_1505_ = lean_apply_6(v_h__6_1480_, v_w_1473_, v_l_1501_, v_r_1502_, v_lhs_1503_, v_rhs_1504_, lean_box(0));
return v___x_1505_;
}
case 6:
{
lean_object* v_w_1506_; lean_object* v_n_1507_; lean_object* v_expr_1508_; lean_object* v___x_1509_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_w_1506_ = lean_ctor_get(v_x_1474_, 0);
lean_inc(v_w_1506_);
v_n_1507_ = lean_ctor_get(v_x_1474_, 2);
lean_inc(v_n_1507_);
v_expr_1508_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_expr_1508_);
lean_dec_ref_known(v_x_1474_, 4);
v___x_1509_ = lean_apply_5(v_h__7_1481_, v_w_1473_, v_w_1506_, v_n_1507_, v_expr_1508_, lean_box(0));
return v___x_1509_;
}
case 7:
{
lean_object* v_n_1510_; lean_object* v_lhs_1511_; lean_object* v_rhs_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__9_1483_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_n_1510_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_n_1510_);
v_lhs_1511_ = lean_ctor_get(v_x_1474_, 2);
lean_inc_ref(v_lhs_1511_);
v_rhs_1512_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_rhs_1512_);
lean_dec_ref_known(v_x_1474_, 4);
v___x_1513_ = lean_apply_4(v_h__8_1482_, v_w_1473_, v_n_1510_, v_lhs_1511_, v_rhs_1512_);
return v___x_1513_;
}
case 8:
{
lean_object* v_n_1514_; lean_object* v_lhs_1515_; lean_object* v_rhs_1516_; lean_object* v___x_1517_; 
lean_dec(v_h__10_1484_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_n_1514_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_n_1514_);
v_lhs_1515_ = lean_ctor_get(v_x_1474_, 2);
lean_inc_ref(v_lhs_1515_);
v_rhs_1516_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_rhs_1516_);
lean_dec_ref_known(v_x_1474_, 4);
v___x_1517_ = lean_apply_4(v_h__9_1483_, v_w_1473_, v_n_1514_, v_lhs_1515_, v_rhs_1516_);
return v___x_1517_;
}
default: 
{
lean_object* v_n_1518_; lean_object* v_lhs_1519_; lean_object* v_rhs_1520_; lean_object* v___x_1521_; 
lean_dec(v_h__9_1483_);
lean_dec(v_h__8_1482_);
lean_dec(v_h__7_1481_);
lean_dec(v_h__6_1480_);
lean_dec(v_h__5_1479_);
lean_dec(v_h__4_1478_);
lean_dec(v_h__3_1477_);
lean_dec(v_h__2_1476_);
lean_dec(v_h__1_1475_);
v_n_1518_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_n_1518_);
v_lhs_1519_ = lean_ctor_get(v_x_1474_, 2);
lean_inc_ref(v_lhs_1519_);
v_rhs_1520_ = lean_ctor_get(v_x_1474_, 3);
lean_inc_ref(v_rhs_1520_);
lean_dec_ref_known(v_x_1474_, 4);
v___x_1521_ = lean_apply_4(v_h__10_1484_, v_w_1473_, v_n_1518_, v_lhs_1519_, v_rhs_1520_);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* v_motive_1522_, lean_object* v_w_1523_, lean_object* v_x_1524_, lean_object* v_h__1_1525_, lean_object* v_h__2_1526_, lean_object* v_h__3_1527_, lean_object* v_h__4_1528_, lean_object* v_h__5_1529_, lean_object* v_h__6_1530_, lean_object* v_h__7_1531_, lean_object* v_h__8_1532_, lean_object* v_h__9_1533_, lean_object* v_h__10_1534_){
_start:
{
switch(lean_obj_tag(v_x_1524_))
{
case 0:
{
lean_object* v_idx_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
v_idx_1535_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_idx_1535_);
lean_dec_ref_known(v_x_1524_, 2);
v___x_1536_ = lean_apply_2(v_h__1_1525_, v_w_1523_, v_idx_1535_);
return v___x_1536_;
}
case 1:
{
lean_object* v_val_1537_; lean_object* v___x_1538_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__1_1525_);
v_val_1537_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_x_1524_, 2);
v___x_1538_ = lean_apply_2(v_h__2_1526_, v_w_1523_, v_val_1537_);
return v___x_1538_;
}
case 2:
{
lean_object* v_w_1539_; lean_object* v_start_1540_; lean_object* v_expr_1541_; lean_object* v___x_1542_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_w_1539_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_w_1539_);
v_start_1540_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_start_1540_);
v_expr_1541_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_expr_1541_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1542_ = lean_apply_4(v_h__3_1527_, v_w_1523_, v_w_1539_, v_start_1540_, v_expr_1541_);
return v___x_1542_;
}
case 3:
{
lean_object* v_lhs_1543_; uint8_t v_op_1544_; lean_object* v_rhs_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_lhs_1543_ = lean_ctor_get(v_x_1524_, 1);
lean_inc_ref(v_lhs_1543_);
v_op_1544_ = lean_ctor_get_uint8(v_x_1524_, sizeof(void*)*3 + 8);
v_rhs_1545_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_rhs_1545_);
lean_dec_ref_known(v_x_1524_, 3);
v___x_1546_ = lean_box(v_op_1544_);
v___x_1547_ = lean_apply_4(v_h__4_1528_, v_w_1523_, v_lhs_1543_, v___x_1546_, v_rhs_1545_);
return v___x_1547_;
}
case 4:
{
lean_object* v_op_1548_; lean_object* v_operand_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_op_1548_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_op_1548_);
v_operand_1549_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_operand_1549_);
lean_dec_ref_known(v_x_1524_, 3);
v___x_1550_ = lean_apply_3(v_h__5_1529_, v_w_1523_, v_op_1548_, v_operand_1549_);
return v___x_1550_;
}
case 5:
{
lean_object* v_l_1551_; lean_object* v_r_1552_; lean_object* v_lhs_1553_; lean_object* v_rhs_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_l_1551_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_l_1551_);
v_r_1552_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_r_1552_);
v_lhs_1553_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_lhs_1553_);
v_rhs_1554_ = lean_ctor_get(v_x_1524_, 4);
lean_inc_ref(v_rhs_1554_);
lean_dec_ref_known(v_x_1524_, 5);
v___x_1555_ = lean_apply_6(v_h__6_1530_, v_w_1523_, v_l_1551_, v_r_1552_, v_lhs_1553_, v_rhs_1554_, lean_box(0));
return v___x_1555_;
}
case 6:
{
lean_object* v_w_1556_; lean_object* v_n_1557_; lean_object* v_expr_1558_; lean_object* v___x_1559_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_w_1556_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_w_1556_);
v_n_1557_ = lean_ctor_get(v_x_1524_, 2);
lean_inc(v_n_1557_);
v_expr_1558_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_expr_1558_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1559_ = lean_apply_5(v_h__7_1531_, v_w_1523_, v_w_1556_, v_n_1557_, v_expr_1558_, lean_box(0));
return v___x_1559_;
}
case 7:
{
lean_object* v_n_1560_; lean_object* v_lhs_1561_; lean_object* v_rhs_1562_; lean_object* v___x_1563_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__9_1533_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_n_1560_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_n_1560_);
v_lhs_1561_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_lhs_1561_);
v_rhs_1562_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_rhs_1562_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1563_ = lean_apply_4(v_h__8_1532_, v_w_1523_, v_n_1560_, v_lhs_1561_, v_rhs_1562_);
return v___x_1563_;
}
case 8:
{
lean_object* v_n_1564_; lean_object* v_lhs_1565_; lean_object* v_rhs_1566_; lean_object* v___x_1567_; 
lean_dec(v_h__10_1534_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_n_1564_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_n_1564_);
v_lhs_1565_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_lhs_1565_);
v_rhs_1566_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_rhs_1566_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1567_ = lean_apply_4(v_h__9_1533_, v_w_1523_, v_n_1564_, v_lhs_1565_, v_rhs_1566_);
return v___x_1567_;
}
default: 
{
lean_object* v_n_1568_; lean_object* v_lhs_1569_; lean_object* v_rhs_1570_; lean_object* v___x_1571_; 
lean_dec(v_h__9_1533_);
lean_dec(v_h__8_1532_);
lean_dec(v_h__7_1531_);
lean_dec(v_h__6_1530_);
lean_dec(v_h__5_1529_);
lean_dec(v_h__4_1528_);
lean_dec(v_h__3_1527_);
lean_dec(v_h__2_1526_);
lean_dec(v_h__1_1525_);
v_n_1568_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_n_1568_);
v_lhs_1569_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_lhs_1569_);
v_rhs_1570_ = lean_ctor_get(v_x_1524_, 3);
lean_inc_ref(v_rhs_1570_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1571_ = lean_apply_4(v_h__10_1534_, v_w_1523_, v_n_1568_, v_lhs_1569_, v_rhs_1570_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t v_x_1572_){
_start:
{
if (v_x_1572_ == 0)
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object* v_x_1575_){
_start:
{
uint8_t v_x_boxed_1576_; lean_object* v_res_1577_; 
v_x_boxed_1576_ = lean_unbox(v_x_1575_);
v_res_1577_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_boxed_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1578_){
_start:
{
lean_inc(v_k_1578_);
return v_k_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1579_);
lean_dec(v_k_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1581_, lean_object* v_ctorIdx_1582_, uint8_t v_t_1583_, lean_object* v_h_1584_, lean_object* v_k_1585_){
_start:
{
lean_inc(v_k_1585_);
return v_k_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1586_, lean_object* v_ctorIdx_1587_, lean_object* v_t_1588_, lean_object* v_h_1589_, lean_object* v_k_1590_){
_start:
{
uint8_t v_t_boxed_1591_; lean_object* v_res_1592_; 
v_t_boxed_1591_ = lean_unbox(v_t_1588_);
v_res_1592_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1586_, v_ctorIdx_1587_, v_t_boxed_1591_, v_h_1589_, v_k_1590_);
lean_dec(v_k_1590_);
lean_dec(v_ctorIdx_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1593_){
_start:
{
lean_inc(v_eq_1593_);
return v_eq_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1594_);
lean_dec(v_eq_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1596_, uint8_t v_t_1597_, lean_object* v_h_1598_, lean_object* v_eq_1599_){
_start:
{
lean_inc(v_eq_1599_);
return v_eq_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1600_, lean_object* v_t_1601_, lean_object* v_h_1602_, lean_object* v_eq_1603_){
_start:
{
uint8_t v_t_boxed_1604_; lean_object* v_res_1605_; 
v_t_boxed_1604_ = lean_unbox(v_t_1601_);
v_res_1605_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1600_, v_t_boxed_1604_, v_h_1602_, v_eq_1603_);
lean_dec(v_eq_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1606_){
_start:
{
lean_inc(v_ult_1606_);
return v_ult_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1607_);
lean_dec(v_ult_1607_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1609_, uint8_t v_t_1610_, lean_object* v_h_1611_, lean_object* v_ult_1612_){
_start:
{
lean_inc(v_ult_1612_);
return v_ult_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_ult_1616_){
_start:
{
uint8_t v_t_boxed_1617_; lean_object* v_res_1618_; 
v_t_boxed_1617_ = lean_unbox(v_t_1614_);
v_res_1618_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1613_, v_t_boxed_1617_, v_h_1615_, v_ult_1616_);
lean_dec(v_ult_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1621_){
_start:
{
if (v_x_1621_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1624_){
_start:
{
uint8_t v_x_22__boxed_1625_; lean_object* v_res_1626_; 
v_x_22__boxed_1625_ = lean_unbox(v_x_1624_);
v_res_1626_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
if (v_x_1629_ == 0)
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_eq(v_a_1630_, v_a_1631_);
return v___x_1632_;
}
else
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_nat_dec_lt(v_a_1630_, v_a_1631_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
uint8_t v_x_96__boxed_1637_; uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_x_96__boxed_1637_ = lean_unbox(v_x_1634_);
v_res_1638_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_96__boxed_1637_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec(v_a_1635_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1640_, uint8_t v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1641_, v_a_1642_, v_a_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1645_, lean_object* v_x_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
uint8_t v_x_109__boxed_1649_; uint8_t v_res_1650_; lean_object* v_r_1651_; 
v_x_109__boxed_1649_ = lean_unbox(v_x_1646_);
v_res_1650_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1645_, v_x_109__boxed_1649_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec(v_w_1645_);
v_r_1651_ = lean_box(v_res_1650_);
return v_r_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_unsigned_to_nat(0u);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object* v_x_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx(v_x_1655_);
lean_dec_ref(v_x_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1657_, lean_object* v_k_1658_){
_start:
{
if (lean_obj_tag(v_t_1657_) == 0)
{
lean_object* v_w_1659_; lean_object* v_lhs_1660_; uint8_t v_op_1661_; lean_object* v_rhs_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_w_1659_ = lean_ctor_get(v_t_1657_, 0);
lean_inc(v_w_1659_);
v_lhs_1660_ = lean_ctor_get(v_t_1657_, 1);
lean_inc_ref(v_lhs_1660_);
v_op_1661_ = lean_ctor_get_uint8(v_t_1657_, sizeof(void*)*3);
v_rhs_1662_ = lean_ctor_get(v_t_1657_, 2);
lean_inc_ref(v_rhs_1662_);
lean_dec_ref_known(v_t_1657_, 3);
v___x_1663_ = lean_box(v_op_1661_);
v___x_1664_ = lean_apply_4(v_k_1658_, v_w_1659_, v_lhs_1660_, v___x_1663_, v_rhs_1662_);
return v___x_1664_;
}
else
{
lean_object* v_w_1665_; lean_object* v_expr_1666_; lean_object* v_idx_1667_; lean_object* v___x_1668_; 
v_w_1665_ = lean_ctor_get(v_t_1657_, 0);
lean_inc(v_w_1665_);
v_expr_1666_ = lean_ctor_get(v_t_1657_, 1);
lean_inc_ref(v_expr_1666_);
v_idx_1667_ = lean_ctor_get(v_t_1657_, 2);
lean_inc(v_idx_1667_);
lean_dec_ref_known(v_t_1657_, 3);
v___x_1668_ = lean_apply_3(v_k_1658_, v_w_1665_, v_expr_1666_, v_idx_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1669_, lean_object* v_ctorIdx_1670_, lean_object* v_t_1671_, lean_object* v_h_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1671_, v_k_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1675_, lean_object* v_ctorIdx_1676_, lean_object* v_t_1677_, lean_object* v_h_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1675_, v_ctorIdx_1676_, v_t_1677_, v_h_1678_, v_k_1679_);
lean_dec(v_ctorIdx_1676_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1681_, lean_object* v_bin_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1681_, v_bin_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1684_, lean_object* v_t_1685_, lean_object* v_h_1686_, lean_object* v_bin_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1685_, v_bin_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1689_, lean_object* v_getLsbD_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1689_, v_getLsbD_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1692_, lean_object* v_t_1693_, lean_object* v_h_1694_, lean_object* v_getLsbD_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1693_, v_getLsbD_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v_w_1698_; lean_object* v_lhs_1699_; uint8_t v_op_1700_; lean_object* v_rhs_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_w_1698_ = lean_ctor_get(v_x_1697_, 0);
lean_inc_n(v_w_1698_, 2);
v_lhs_1699_ = lean_ctor_get(v_x_1697_, 1);
lean_inc_ref(v_lhs_1699_);
v_op_1700_ = lean_ctor_get_uint8(v_x_1697_, sizeof(void*)*3);
v_rhs_1701_ = lean_ctor_get(v_x_1697_, 2);
lean_inc_ref(v_rhs_1701_);
lean_dec_ref_known(v_x_1697_, 3);
v___x_1702_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1703_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1698_, v_lhs_1699_);
v___x_1704_ = lean_string_append(v___x_1702_, v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1706_ = lean_string_append(v___x_1704_, v___x_1705_);
v___x_1707_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1700_);
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = lean_string_append(v___x_1708_, v___x_1705_);
v___x_1710_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1698_, v_rhs_1701_);
v___x_1711_ = lean_string_append(v___x_1709_, v___x_1710_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1713_ = lean_string_append(v___x_1711_, v___x_1712_);
return v___x_1713_;
}
else
{
lean_object* v_w_1714_; lean_object* v_expr_1715_; lean_object* v_idx_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_w_1714_ = lean_ctor_get(v_x_1697_, 0);
lean_inc(v_w_1714_);
v_expr_1715_ = lean_ctor_get(v_x_1697_, 1);
lean_inc_ref(v_expr_1715_);
v_idx_1716_ = lean_ctor_get(v_x_1697_, 2);
lean_inc(v_idx_1716_);
lean_dec_ref_known(v_x_1697_, 3);
v___x_1717_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1714_, v_expr_1715_);
v___x_1718_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
v___x_1720_ = l_Nat_reprFast(v_idx_1716_);
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
return v___x_1723_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1726_, lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 0)
{
lean_object* v_w_1728_; lean_object* v_lhs_1729_; uint8_t v_op_1730_; lean_object* v_rhs_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_w_1728_ = lean_ctor_get(v_x_1727_, 0);
lean_inc_n(v_w_1728_, 2);
v_lhs_1729_ = lean_ctor_get(v_x_1727_, 1);
lean_inc_ref(v_lhs_1729_);
v_op_1730_ = lean_ctor_get_uint8(v_x_1727_, sizeof(void*)*3);
v_rhs_1731_ = lean_ctor_get(v_x_1727_, 2);
lean_inc_ref(v_rhs_1731_);
lean_dec_ref_known(v_x_1727_, 3);
v___x_1732_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1728_, v_assign_1726_, v_lhs_1729_);
v___x_1733_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1728_, v_assign_1726_, v_rhs_1731_);
v___x_1734_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1730_, v___x_1732_, v___x_1733_);
lean_dec(v___x_1733_);
lean_dec(v___x_1732_);
return v___x_1734_;
}
else
{
lean_object* v_w_1735_; lean_object* v_expr_1736_; lean_object* v_idx_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_w_1735_ = lean_ctor_get(v_x_1727_, 0);
lean_inc(v_w_1735_);
v_expr_1736_ = lean_ctor_get(v_x_1727_, 1);
lean_inc_ref(v_expr_1736_);
v_idx_1737_ = lean_ctor_get(v_x_1727_, 2);
lean_inc(v_idx_1737_);
lean_dec_ref_known(v_x_1727_, 3);
v___x_1738_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1735_, v_assign_1726_, v_expr_1736_);
v___x_1739_ = l_Nat_testBit(v___x_1738_, v_idx_1737_);
lean_dec(v_idx_1737_);
lean_dec(v___x_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1740_, lean_object* v_x_1741_){
_start:
{
uint8_t v_res_1742_; lean_object* v_r_1743_; 
v_res_1742_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1740_, v_x_1741_);
lean_dec_ref(v_assign_1740_);
v_r_1743_ = lean_box(v_res_1742_);
return v_r_1743_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1744_, v_x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1747_, lean_object* v_x_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1747_, v_x_1748_);
lean_dec_ref(v_assign_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1751_, lean_object* v_expr_1752_){
_start:
{
lean_object* v___f_1753_; uint8_t v___x_1754_; 
v___f_1753_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1753_, 0, v_assign_1751_);
v___x_1754_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1753_, v_expr_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1755_, lean_object* v_expr_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1755_, v_expr_1756_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
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
