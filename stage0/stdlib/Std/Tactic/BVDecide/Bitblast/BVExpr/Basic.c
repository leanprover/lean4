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
uint8_t v_x_20__boxed_313_; uint8_t v_y_21__boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_x_20__boxed_313_ = lean_unbox(v_x_311_);
v_y_21__boxed_314_ = lean_unbox(v_y_312_);
v_res_315_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_20__boxed_313_, v_y_21__boxed_314_);
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
if (lean_obj_tag(v_x_463_) == 0)
{
uint8_t v___x_464_; 
v___x_464_ = 1;
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
}
case 1:
{
lean_object* v_n_466_; uint8_t v___x_467_; 
v_n_466_ = lean_ctor_get(v_x_462_, 0);
v___x_467_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_467_;
}
case 1:
{
lean_object* v_n_468_; uint8_t v___x_469_; 
v_n_468_ = lean_ctor_get(v_x_463_, 0);
v___x_469_ = lean_nat_dec_eq(v_n_466_, v_n_468_);
return v___x_469_;
}
case 4:
{
return v___x_467_;
}
case 5:
{
return v___x_467_;
}
case 6:
{
return v___x_467_;
}
default: 
{
return v___x_467_;
}
}
}
case 2:
{
lean_object* v_n_470_; uint8_t v___x_471_; 
v_n_470_ = lean_ctor_get(v_x_462_, 0);
v___x_471_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_471_;
}
case 2:
{
lean_object* v_n_472_; uint8_t v___x_473_; 
v_n_472_ = lean_ctor_get(v_x_463_, 0);
v___x_473_ = lean_nat_dec_eq(v_n_470_, v_n_472_);
return v___x_473_;
}
case 4:
{
return v___x_471_;
}
case 5:
{
return v___x_471_;
}
case 6:
{
return v___x_471_;
}
default: 
{
return v___x_471_;
}
}
}
case 3:
{
lean_object* v_n_474_; uint8_t v___x_475_; 
v_n_474_ = lean_ctor_get(v_x_462_, 0);
v___x_475_ = 0;
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
return v___x_475_;
}
case 3:
{
lean_object* v_n_476_; uint8_t v___x_477_; 
v_n_476_ = lean_ctor_get(v_x_463_, 0);
v___x_477_ = lean_nat_dec_eq(v_n_474_, v_n_476_);
return v___x_477_;
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
case 4:
{
if (lean_obj_tag(v_x_463_) == 4)
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
case 5:
{
if (lean_obj_tag(v_x_463_) == 5)
{
uint8_t v___x_480_; 
v___x_480_ = 1;
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
default: 
{
if (lean_obj_tag(v_x_463_) == 6)
{
uint8_t v___x_482_; 
v___x_482_ = 1;
return v___x_482_;
}
else
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_484_, v_x_485_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_491_, v_x_492_);
lean_dec(v_x_492_);
lean_dec(v_x_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_502_){
_start:
{
switch(lean_obj_tag(v_x_502_))
{
case 0:
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_503_;
}
case 1:
{
lean_object* v_n_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_n_504_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_n_504_);
lean_dec_ref_known(v_x_502_, 1);
v___x_505_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_506_ = l_Nat_reprFast(v_n_504_);
v___x_507_ = lean_string_append(v___x_505_, v___x_506_);
lean_dec_ref(v___x_506_);
return v___x_507_;
}
case 2:
{
lean_object* v_n_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_n_508_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_n_508_);
lean_dec_ref_known(v_x_502_, 1);
v___x_509_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_510_ = l_Nat_reprFast(v_n_508_);
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
return v___x_511_;
}
case 3:
{
lean_object* v_n_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_n_512_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_n_512_);
lean_dec_ref_known(v_x_502_, 1);
v___x_513_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_514_ = l_Nat_reprFast(v_n_512_);
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
return v___x_515_;
}
case 4:
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_516_;
}
case 5:
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_517_;
}
default: 
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_521_, lean_object* v_x_522_, lean_object* v_a_523_){
_start:
{
switch(lean_obj_tag(v_x_522_))
{
case 0:
{
lean_object* v___x_524_; 
v___x_524_ = l_BitVec_not(v_w_521_, v_a_523_);
lean_dec(v_a_523_);
lean_dec(v_w_521_);
return v___x_524_;
}
case 1:
{
lean_object* v_n_525_; lean_object* v___x_526_; 
v_n_525_ = lean_ctor_get(v_x_522_, 0);
v___x_526_ = l_BitVec_rotateLeft(v_w_521_, v_a_523_, v_n_525_);
lean_dec(v_a_523_);
lean_dec(v_w_521_);
return v___x_526_;
}
case 2:
{
lean_object* v_n_527_; lean_object* v___x_528_; 
v_n_527_ = lean_ctor_get(v_x_522_, 0);
v___x_528_ = l_BitVec_rotateRight(v_w_521_, v_a_523_, v_n_527_);
lean_dec(v_a_523_);
lean_dec(v_w_521_);
return v___x_528_;
}
case 3:
{
lean_object* v_n_529_; lean_object* v___x_530_; 
v_n_529_ = lean_ctor_get(v_x_522_, 0);
v___x_530_ = l_BitVec_sshiftRight(v_w_521_, v_a_523_, v_n_529_);
lean_dec(v_w_521_);
return v___x_530_;
}
case 4:
{
lean_object* v___x_531_; 
v___x_531_ = l_BitVec_reverse(v_w_521_, v_a_523_);
lean_dec(v_a_523_);
lean_dec(v_w_521_);
return v___x_531_;
}
case 5:
{
lean_object* v___x_532_; 
v___x_532_ = l_BitVec_clz(v_w_521_, v_a_523_);
lean_dec(v_a_523_);
lean_dec(v_w_521_);
return v___x_532_;
}
default: 
{
lean_object* v___x_533_; 
v___x_533_ = l_BitVec_cpop(v_w_521_, v_a_523_);
lean_dec(v_a_523_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_534_, lean_object* v_x_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_534_, v_x_535_, v_a_536_);
lean_dec(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(lean_object* v_x_538_){
_start:
{
switch(lean_obj_tag(v_x_538_))
{
case 0:
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
return v___x_539_;
}
case 1:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(1u);
return v___x_540_;
}
case 2:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(2u);
return v___x_541_;
}
case 3:
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(3u);
return v___x_542_;
}
case 4:
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(4u);
return v___x_543_;
}
case 5:
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(5u);
return v___x_544_;
}
case 6:
{
lean_object* v___x_545_; 
v___x_545_ = lean_unsigned_to_nat(6u);
return v___x_545_;
}
case 7:
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(7u);
return v___x_546_;
}
case 8:
{
lean_object* v___x_547_; 
v___x_547_ = lean_unsigned_to_nat(8u);
return v___x_547_;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(9u);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(lean_object* v_x_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_549_);
lean_dec_ref(v_x_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx(lean_object* v_a_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(lean_object* v_a_554_, lean_object* v_x_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(v_a_554_, v_x_555_);
lean_dec_ref(v_x_555_);
lean_dec(v_a_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_557_, lean_object* v_k_558_){
_start:
{
switch(lean_obj_tag(v_t_557_))
{
case 0:
{
lean_object* v_w_559_; lean_object* v_idx_560_; lean_object* v___x_561_; 
v_w_559_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_559_);
v_idx_560_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_idx_560_);
lean_dec_ref_known(v_t_557_, 2);
v___x_561_ = lean_apply_2(v_k_558_, v_w_559_, v_idx_560_);
return v___x_561_;
}
case 1:
{
lean_object* v_w_562_; lean_object* v_val_563_; lean_object* v___x_564_; 
v_w_562_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_562_);
v_val_563_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_val_563_);
lean_dec_ref_known(v_t_557_, 2);
v___x_564_ = lean_apply_2(v_k_558_, v_w_562_, v_val_563_);
return v___x_564_;
}
case 2:
{
lean_object* v_w_565_; lean_object* v_start_566_; lean_object* v_len_567_; lean_object* v_expr_568_; lean_object* v___x_569_; 
v_w_565_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_565_);
v_start_566_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_start_566_);
v_len_567_ = lean_ctor_get(v_t_557_, 2);
lean_inc(v_len_567_);
v_expr_568_ = lean_ctor_get(v_t_557_, 3);
lean_inc_ref(v_expr_568_);
lean_dec_ref_known(v_t_557_, 4);
v___x_569_ = lean_apply_4(v_k_558_, v_w_565_, v_start_566_, v_len_567_, v_expr_568_);
return v___x_569_;
}
case 3:
{
lean_object* v_w_570_; lean_object* v_lhs_571_; uint8_t v_op_572_; lean_object* v_rhs_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_w_570_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_570_);
v_lhs_571_ = lean_ctor_get(v_t_557_, 1);
lean_inc_ref(v_lhs_571_);
v_op_572_ = lean_ctor_get_uint8(v_t_557_, sizeof(void*)*3);
v_rhs_573_ = lean_ctor_get(v_t_557_, 2);
lean_inc_ref(v_rhs_573_);
lean_dec_ref_known(v_t_557_, 3);
v___x_574_ = lean_box(v_op_572_);
v___x_575_ = lean_apply_4(v_k_558_, v_w_570_, v_lhs_571_, v___x_574_, v_rhs_573_);
return v___x_575_;
}
case 4:
{
lean_object* v_w_576_; lean_object* v_op_577_; lean_object* v_operand_578_; lean_object* v___x_579_; 
v_w_576_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_576_);
v_op_577_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_op_577_);
v_operand_578_ = lean_ctor_get(v_t_557_, 2);
lean_inc_ref(v_operand_578_);
lean_dec_ref_known(v_t_557_, 3);
v___x_579_ = lean_apply_3(v_k_558_, v_w_576_, v_op_577_, v_operand_578_);
return v___x_579_;
}
case 5:
{
lean_object* v_l_580_; lean_object* v_r_581_; lean_object* v_w_582_; lean_object* v_lhs_583_; lean_object* v_rhs_584_; lean_object* v___x_585_; 
v_l_580_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_l_580_);
v_r_581_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_r_581_);
v_w_582_ = lean_ctor_get(v_t_557_, 2);
lean_inc(v_w_582_);
v_lhs_583_ = lean_ctor_get(v_t_557_, 3);
lean_inc_ref(v_lhs_583_);
v_rhs_584_ = lean_ctor_get(v_t_557_, 4);
lean_inc_ref(v_rhs_584_);
lean_dec_ref_known(v_t_557_, 5);
v___x_585_ = lean_apply_6(v_k_558_, v_l_580_, v_r_581_, v_w_582_, v_lhs_583_, v_rhs_584_, lean_box(0));
return v___x_585_;
}
case 6:
{
lean_object* v_w_586_; lean_object* v_w_x27_587_; lean_object* v_n_588_; lean_object* v_expr_589_; lean_object* v___x_590_; 
v_w_586_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_w_586_);
v_w_x27_587_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_w_x27_587_);
v_n_588_ = lean_ctor_get(v_t_557_, 2);
lean_inc(v_n_588_);
v_expr_589_ = lean_ctor_get(v_t_557_, 3);
lean_inc_ref(v_expr_589_);
lean_dec_ref_known(v_t_557_, 4);
v___x_590_ = lean_apply_5(v_k_558_, v_w_586_, v_w_x27_587_, v_n_588_, v_expr_589_, lean_box(0));
return v___x_590_;
}
default: 
{
lean_object* v_m_591_; lean_object* v_n_592_; lean_object* v_lhs_593_; lean_object* v_rhs_594_; lean_object* v___x_595_; 
v_m_591_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_m_591_);
v_n_592_ = lean_ctor_get(v_t_557_, 1);
lean_inc(v_n_592_);
v_lhs_593_ = lean_ctor_get(v_t_557_, 2);
lean_inc_ref(v_lhs_593_);
v_rhs_594_ = lean_ctor_get(v_t_557_, 3);
lean_inc_ref(v_rhs_594_);
lean_dec_ref(v_t_557_);
v___x_595_ = lean_apply_4(v_k_558_, v_m_591_, v_n_592_, v_lhs_593_, v_rhs_594_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_596_, lean_object* v_ctorIdx_597_, lean_object* v_a_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_k_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_599_, v_k_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_603_, lean_object* v_ctorIdx_604_, lean_object* v_a_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_k_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_603_, v_ctorIdx_604_, v_a_605_, v_t_606_, v_h_607_, v_k_608_);
lean_dec(v_a_605_);
lean_dec(v_ctorIdx_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_610_, lean_object* v_var_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_610_, v_var_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_613_, lean_object* v_a_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_var_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_615_, v_var_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_619_, lean_object* v_a_620_, lean_object* v_t_621_, lean_object* v_h_622_, lean_object* v_var_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_619_, v_a_620_, v_t_621_, v_h_622_, v_var_623_);
lean_dec(v_a_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_625_, lean_object* v_const_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_625_, v_const_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_628_, lean_object* v_a_629_, lean_object* v_t_630_, lean_object* v_h_631_, lean_object* v_const_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_630_, v_const_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_634_, lean_object* v_a_635_, lean_object* v_t_636_, lean_object* v_h_637_, lean_object* v_const_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_634_, v_a_635_, v_t_636_, v_h_637_, v_const_638_);
lean_dec(v_a_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_640_, lean_object* v_extract_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_640_, v_extract_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_643_, lean_object* v_a_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_extract_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_645_, v_extract_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_649_, lean_object* v_a_650_, lean_object* v_t_651_, lean_object* v_h_652_, lean_object* v_extract_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_649_, v_a_650_, v_t_651_, v_h_652_, v_extract_653_);
lean_dec(v_a_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_655_, lean_object* v_bin_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_655_, v_bin_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_658_, lean_object* v_a_659_, lean_object* v_t_660_, lean_object* v_h_661_, lean_object* v_bin_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_660_, v_bin_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_664_, lean_object* v_a_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_bin_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_664_, v_a_665_, v_t_666_, v_h_667_, v_bin_668_);
lean_dec(v_a_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_670_, lean_object* v_un_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_670_, v_un_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_673_, lean_object* v_a_674_, lean_object* v_t_675_, lean_object* v_h_676_, lean_object* v_un_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_675_, v_un_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_679_, lean_object* v_a_680_, lean_object* v_t_681_, lean_object* v_h_682_, lean_object* v_un_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_679_, v_a_680_, v_t_681_, v_h_682_, v_un_683_);
lean_dec(v_a_680_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_685_, lean_object* v_append_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_685_, v_append_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_688_, lean_object* v_a_689_, lean_object* v_t_690_, lean_object* v_h_691_, lean_object* v_append_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_690_, v_append_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_694_, lean_object* v_a_695_, lean_object* v_t_696_, lean_object* v_h_697_, lean_object* v_append_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_694_, v_a_695_, v_t_696_, v_h_697_, v_append_698_);
lean_dec(v_a_695_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_700_, lean_object* v_replicate_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_700_, v_replicate_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_703_, lean_object* v_a_704_, lean_object* v_t_705_, lean_object* v_h_706_, lean_object* v_replicate_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_705_, v_replicate_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_709_, lean_object* v_a_710_, lean_object* v_t_711_, lean_object* v_h_712_, lean_object* v_replicate_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_709_, v_a_710_, v_t_711_, v_h_712_, v_replicate_713_);
lean_dec(v_a_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_715_, lean_object* v_shiftLeft_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_715_, v_shiftLeft_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_718_, lean_object* v_a_719_, lean_object* v_t_720_, lean_object* v_h_721_, lean_object* v_shiftLeft_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_720_, v_shiftLeft_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_724_, lean_object* v_a_725_, lean_object* v_t_726_, lean_object* v_h_727_, lean_object* v_shiftLeft_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_724_, v_a_725_, v_t_726_, v_h_727_, v_shiftLeft_728_);
lean_dec(v_a_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_730_, lean_object* v_shiftRight_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_730_, v_shiftRight_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_733_, lean_object* v_a_734_, lean_object* v_t_735_, lean_object* v_h_736_, lean_object* v_shiftRight_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_735_, v_shiftRight_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_739_, lean_object* v_a_740_, lean_object* v_t_741_, lean_object* v_h_742_, lean_object* v_shiftRight_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_739_, v_a_740_, v_t_741_, v_h_742_, v_shiftRight_743_);
lean_dec(v_a_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_745_, lean_object* v_arithShiftRight_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_745_, v_arithShiftRight_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_748_, lean_object* v_a_749_, lean_object* v_t_750_, lean_object* v_h_751_, lean_object* v_arithShiftRight_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_750_, v_arithShiftRight_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_754_, lean_object* v_a_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_arithShiftRight_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_754_, v_a_755_, v_t_756_, v_h_757_, v_arithShiftRight_758_);
lean_dec(v_a_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_760_, lean_object* v_var_761_, lean_object* v_const_762_, lean_object* v_extract_763_, lean_object* v_bin_764_, lean_object* v_un_765_, lean_object* v_append_766_, lean_object* v_replicate_767_, lean_object* v_shiftLeft_768_, lean_object* v_shiftRight_769_, lean_object* v_arithShiftRight_770_){
_start:
{
switch(lean_obj_tag(v_t_760_))
{
case 0:
{
lean_object* v_w_771_; lean_object* v_idx_772_; lean_object* v___x_773_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
v_w_771_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_771_);
v_idx_772_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_idx_772_);
lean_dec_ref_known(v_t_760_, 2);
v___x_773_ = lean_apply_2(v_var_761_, v_w_771_, v_idx_772_);
return v___x_773_;
}
case 1:
{
lean_object* v_w_774_; lean_object* v_val_775_; lean_object* v___x_776_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_var_761_);
v_w_774_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_774_);
v_val_775_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_val_775_);
lean_dec_ref_known(v_t_760_, 2);
v___x_776_ = lean_apply_2(v_const_762_, v_w_774_, v_val_775_);
return v___x_776_;
}
case 2:
{
lean_object* v_w_777_; lean_object* v_start_778_; lean_object* v_len_779_; lean_object* v_expr_780_; lean_object* v___x_781_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_w_777_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_777_);
v_start_778_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_start_778_);
v_len_779_ = lean_ctor_get(v_t_760_, 2);
lean_inc(v_len_779_);
v_expr_780_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_expr_780_);
lean_dec_ref_known(v_t_760_, 4);
v___x_781_ = lean_apply_4(v_extract_763_, v_w_777_, v_start_778_, v_len_779_, v_expr_780_);
return v___x_781_;
}
case 3:
{
lean_object* v_w_782_; lean_object* v_lhs_783_; uint8_t v_op_784_; lean_object* v_rhs_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_w_782_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_782_);
v_lhs_783_ = lean_ctor_get(v_t_760_, 1);
lean_inc_ref(v_lhs_783_);
v_op_784_ = lean_ctor_get_uint8(v_t_760_, sizeof(void*)*3 + 8);
v_rhs_785_ = lean_ctor_get(v_t_760_, 2);
lean_inc_ref(v_rhs_785_);
lean_dec_ref_known(v_t_760_, 3);
v___x_786_ = lean_box(v_op_784_);
v___x_787_ = lean_apply_4(v_bin_764_, v_w_782_, v_lhs_783_, v___x_786_, v_rhs_785_);
return v___x_787_;
}
case 4:
{
lean_object* v_w_788_; lean_object* v_op_789_; lean_object* v_operand_790_; lean_object* v___x_791_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_w_788_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_788_);
v_op_789_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_op_789_);
v_operand_790_ = lean_ctor_get(v_t_760_, 2);
lean_inc_ref(v_operand_790_);
lean_dec_ref_known(v_t_760_, 3);
v___x_791_ = lean_apply_3(v_un_765_, v_w_788_, v_op_789_, v_operand_790_);
return v___x_791_;
}
case 5:
{
lean_object* v_l_792_; lean_object* v_r_793_; lean_object* v_w_794_; lean_object* v_lhs_795_; lean_object* v_rhs_796_; lean_object* v___x_797_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_l_792_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_l_792_);
v_r_793_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_r_793_);
v_w_794_ = lean_ctor_get(v_t_760_, 2);
lean_inc(v_w_794_);
v_lhs_795_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_lhs_795_);
v_rhs_796_ = lean_ctor_get(v_t_760_, 4);
lean_inc_ref(v_rhs_796_);
lean_dec_ref_known(v_t_760_, 5);
v___x_797_ = lean_apply_6(v_append_766_, v_l_792_, v_r_793_, v_w_794_, v_lhs_795_, v_rhs_796_, lean_box(0));
return v___x_797_;
}
case 6:
{
lean_object* v_w_798_; lean_object* v_w_x27_799_; lean_object* v_n_800_; lean_object* v_expr_801_; lean_object* v___x_802_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_w_798_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_w_798_);
v_w_x27_799_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_w_x27_799_);
v_n_800_ = lean_ctor_get(v_t_760_, 2);
lean_inc(v_n_800_);
v_expr_801_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_expr_801_);
lean_dec_ref_known(v_t_760_, 4);
v___x_802_ = lean_apply_5(v_replicate_767_, v_w_798_, v_w_x27_799_, v_n_800_, v_expr_801_, lean_box(0));
return v___x_802_;
}
case 7:
{
lean_object* v_m_803_; lean_object* v_n_804_; lean_object* v_lhs_805_; lean_object* v_rhs_806_; lean_object* v___x_807_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftRight_769_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_m_803_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_m_803_);
v_n_804_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_n_804_);
v_lhs_805_ = lean_ctor_get(v_t_760_, 2);
lean_inc_ref(v_lhs_805_);
v_rhs_806_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_rhs_806_);
lean_dec_ref_known(v_t_760_, 4);
v___x_807_ = lean_apply_4(v_shiftLeft_768_, v_m_803_, v_n_804_, v_lhs_805_, v_rhs_806_);
return v___x_807_;
}
case 8:
{
lean_object* v_m_808_; lean_object* v_n_809_; lean_object* v_lhs_810_; lean_object* v_rhs_811_; lean_object* v___x_812_; 
lean_dec(v_arithShiftRight_770_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_m_808_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_m_808_);
v_n_809_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_n_809_);
v_lhs_810_ = lean_ctor_get(v_t_760_, 2);
lean_inc_ref(v_lhs_810_);
v_rhs_811_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_rhs_811_);
lean_dec_ref_known(v_t_760_, 4);
v___x_812_ = lean_apply_4(v_shiftRight_769_, v_m_808_, v_n_809_, v_lhs_810_, v_rhs_811_);
return v___x_812_;
}
default: 
{
lean_object* v_m_813_; lean_object* v_n_814_; lean_object* v_lhs_815_; lean_object* v_rhs_816_; lean_object* v___x_817_; 
lean_dec(v_shiftRight_769_);
lean_dec(v_shiftLeft_768_);
lean_dec(v_replicate_767_);
lean_dec(v_append_766_);
lean_dec(v_un_765_);
lean_dec(v_bin_764_);
lean_dec(v_extract_763_);
lean_dec(v_const_762_);
lean_dec(v_var_761_);
v_m_813_ = lean_ctor_get(v_t_760_, 0);
lean_inc(v_m_813_);
v_n_814_ = lean_ctor_get(v_t_760_, 1);
lean_inc(v_n_814_);
v_lhs_815_ = lean_ctor_get(v_t_760_, 2);
lean_inc_ref(v_lhs_815_);
v_rhs_816_ = lean_ctor_get(v_t_760_, 3);
lean_inc_ref(v_rhs_816_);
lean_dec_ref_known(v_t_760_, 4);
v___x_817_ = lean_apply_4(v_arithShiftRight_770_, v_m_813_, v_n_814_, v_lhs_815_, v_rhs_816_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_818_, lean_object* v_a_819_, lean_object* v_t_820_, lean_object* v_var_821_, lean_object* v_const_822_, lean_object* v_extract_823_, lean_object* v_bin_824_, lean_object* v_un_825_, lean_object* v_append_826_, lean_object* v_replicate_827_, lean_object* v_shiftLeft_828_, lean_object* v_shiftRight_829_, lean_object* v_arithShiftRight_830_){
_start:
{
switch(lean_obj_tag(v_t_820_))
{
case 0:
{
lean_object* v_w_831_; lean_object* v_idx_832_; lean_object* v___x_833_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
v_w_831_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_831_);
v_idx_832_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_idx_832_);
lean_dec_ref_known(v_t_820_, 2);
v___x_833_ = lean_apply_2(v_var_821_, v_w_831_, v_idx_832_);
return v___x_833_;
}
case 1:
{
lean_object* v_w_834_; lean_object* v_val_835_; lean_object* v___x_836_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_var_821_);
v_w_834_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_834_);
v_val_835_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_val_835_);
lean_dec_ref_known(v_t_820_, 2);
v___x_836_ = lean_apply_2(v_const_822_, v_w_834_, v_val_835_);
return v___x_836_;
}
case 2:
{
lean_object* v_w_837_; lean_object* v_start_838_; lean_object* v_len_839_; lean_object* v_expr_840_; lean_object* v___x_841_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_w_837_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_837_);
v_start_838_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_start_838_);
v_len_839_ = lean_ctor_get(v_t_820_, 2);
lean_inc(v_len_839_);
v_expr_840_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_expr_840_);
lean_dec_ref_known(v_t_820_, 4);
v___x_841_ = lean_apply_4(v_extract_823_, v_w_837_, v_start_838_, v_len_839_, v_expr_840_);
return v___x_841_;
}
case 3:
{
lean_object* v_w_842_; lean_object* v_lhs_843_; uint8_t v_op_844_; lean_object* v_rhs_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_w_842_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_842_);
v_lhs_843_ = lean_ctor_get(v_t_820_, 1);
lean_inc_ref(v_lhs_843_);
v_op_844_ = lean_ctor_get_uint8(v_t_820_, sizeof(void*)*3 + 8);
v_rhs_845_ = lean_ctor_get(v_t_820_, 2);
lean_inc_ref(v_rhs_845_);
lean_dec_ref_known(v_t_820_, 3);
v___x_846_ = lean_box(v_op_844_);
v___x_847_ = lean_apply_4(v_bin_824_, v_w_842_, v_lhs_843_, v___x_846_, v_rhs_845_);
return v___x_847_;
}
case 4:
{
lean_object* v_w_848_; lean_object* v_op_849_; lean_object* v_operand_850_; lean_object* v___x_851_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_w_848_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_848_);
v_op_849_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_op_849_);
v_operand_850_ = lean_ctor_get(v_t_820_, 2);
lean_inc_ref(v_operand_850_);
lean_dec_ref_known(v_t_820_, 3);
v___x_851_ = lean_apply_3(v_un_825_, v_w_848_, v_op_849_, v_operand_850_);
return v___x_851_;
}
case 5:
{
lean_object* v_l_852_; lean_object* v_r_853_; lean_object* v_w_854_; lean_object* v_lhs_855_; lean_object* v_rhs_856_; lean_object* v___x_857_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_l_852_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_l_852_);
v_r_853_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_r_853_);
v_w_854_ = lean_ctor_get(v_t_820_, 2);
lean_inc(v_w_854_);
v_lhs_855_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_lhs_855_);
v_rhs_856_ = lean_ctor_get(v_t_820_, 4);
lean_inc_ref(v_rhs_856_);
lean_dec_ref_known(v_t_820_, 5);
v___x_857_ = lean_apply_6(v_append_826_, v_l_852_, v_r_853_, v_w_854_, v_lhs_855_, v_rhs_856_, lean_box(0));
return v___x_857_;
}
case 6:
{
lean_object* v_w_858_; lean_object* v_w_x27_859_; lean_object* v_n_860_; lean_object* v_expr_861_; lean_object* v___x_862_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_w_858_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_w_858_);
v_w_x27_859_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_w_x27_859_);
v_n_860_ = lean_ctor_get(v_t_820_, 2);
lean_inc(v_n_860_);
v_expr_861_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_expr_861_);
lean_dec_ref_known(v_t_820_, 4);
v___x_862_ = lean_apply_5(v_replicate_827_, v_w_858_, v_w_x27_859_, v_n_860_, v_expr_861_, lean_box(0));
return v___x_862_;
}
case 7:
{
lean_object* v_m_863_; lean_object* v_n_864_; lean_object* v_lhs_865_; lean_object* v_rhs_866_; lean_object* v___x_867_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftRight_829_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_m_863_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_m_863_);
v_n_864_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_n_864_);
v_lhs_865_ = lean_ctor_get(v_t_820_, 2);
lean_inc_ref(v_lhs_865_);
v_rhs_866_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_rhs_866_);
lean_dec_ref_known(v_t_820_, 4);
v___x_867_ = lean_apply_4(v_shiftLeft_828_, v_m_863_, v_n_864_, v_lhs_865_, v_rhs_866_);
return v___x_867_;
}
case 8:
{
lean_object* v_m_868_; lean_object* v_n_869_; lean_object* v_lhs_870_; lean_object* v_rhs_871_; lean_object* v___x_872_; 
lean_dec(v_arithShiftRight_830_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_m_868_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_m_868_);
v_n_869_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_n_869_);
v_lhs_870_ = lean_ctor_get(v_t_820_, 2);
lean_inc_ref(v_lhs_870_);
v_rhs_871_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_rhs_871_);
lean_dec_ref_known(v_t_820_, 4);
v___x_872_ = lean_apply_4(v_shiftRight_829_, v_m_868_, v_n_869_, v_lhs_870_, v_rhs_871_);
return v___x_872_;
}
default: 
{
lean_object* v_m_873_; lean_object* v_n_874_; lean_object* v_lhs_875_; lean_object* v_rhs_876_; lean_object* v___x_877_; 
lean_dec(v_shiftRight_829_);
lean_dec(v_shiftLeft_828_);
lean_dec(v_replicate_827_);
lean_dec(v_append_826_);
lean_dec(v_un_825_);
lean_dec(v_bin_824_);
lean_dec(v_extract_823_);
lean_dec(v_const_822_);
lean_dec(v_var_821_);
v_m_873_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_m_873_);
v_n_874_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_n_874_);
v_lhs_875_ = lean_ctor_get(v_t_820_, 2);
lean_inc_ref(v_lhs_875_);
v_rhs_876_ = lean_ctor_get(v_t_820_, 3);
lean_inc_ref(v_rhs_876_);
lean_dec_ref_known(v_t_820_, 4);
v___x_877_ = lean_apply_4(v_arithShiftRight_830_, v_m_873_, v_n_874_, v_lhs_875_, v_rhs_876_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_878_, lean_object* v_a_879_, lean_object* v_t_880_, lean_object* v_var_881_, lean_object* v_const_882_, lean_object* v_extract_883_, lean_object* v_bin_884_, lean_object* v_un_885_, lean_object* v_append_886_, lean_object* v_replicate_887_, lean_object* v_shiftLeft_888_, lean_object* v_shiftRight_889_, lean_object* v_arithShiftRight_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_878_, v_a_879_, v_t_880_, v_var_881_, v_const_882_, v_extract_883_, v_bin_884_, v_un_885_, v_append_886_, v_replicate_887_, v_shiftLeft_888_, v_shiftRight_889_, v_arithShiftRight_890_);
lean_dec(v_a_879_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_892_, lean_object* v_idx_893_){
_start:
{
uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; lean_object* v___x_899_; 
v___x_894_ = 5ULL;
v___x_895_ = lean_uint64_of_nat(v_w_892_);
v___x_896_ = lean_uint64_of_nat(v_idx_893_);
v___x_897_ = lean_uint64_mix_hash(v___x_895_, v___x_896_);
v___x_898_ = lean_uint64_mix_hash(v___x_894_, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_899_, 0, v_w_892_);
lean_ctor_set(v___x_899_, 1, v_idx_893_);
lean_ctor_set_uint64(v___x_899_, sizeof(void*)*2, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_900_, lean_object* v_val_901_){
_start:
{
uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; lean_object* v___x_907_; 
v___x_902_ = 7ULL;
v___x_903_ = lean_uint64_of_nat(v_w_900_);
v___x_904_ = l_BitVec_hash(v_w_900_, v_val_901_);
v___x_905_ = lean_uint64_mix_hash(v___x_903_, v___x_904_);
v___x_906_ = lean_uint64_mix_hash(v___x_902_, v___x_905_);
v___x_907_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_907_, 0, v_w_900_);
lean_ctor_set(v___x_907_, 1, v_val_901_);
lean_ctor_set_uint64(v___x_907_, sizeof(void*)*2, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_908_, lean_object* v_start_909_, lean_object* v_len_910_, lean_object* v_expr_911_){
_start:
{
uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___y_916_; 
v___x_912_ = 11ULL;
v___x_913_ = lean_uint64_of_nat(v_start_909_);
v___x_914_ = lean_uint64_of_nat(v_len_910_);
switch(lean_obj_tag(v_expr_911_))
{
case 0:
{
uint64_t v_hashCode_921_; 
v_hashCode_921_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*2);
v___y_916_ = v_hashCode_921_;
goto v___jp_915_;
}
case 1:
{
uint64_t v_hashCode_922_; 
v_hashCode_922_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*2);
v___y_916_ = v_hashCode_922_;
goto v___jp_915_;
}
case 3:
{
uint64_t v_hashCode_923_; 
v_hashCode_923_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*3);
v___y_916_ = v_hashCode_923_;
goto v___jp_915_;
}
case 4:
{
uint64_t v_hashCode_924_; 
v_hashCode_924_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*3);
v___y_916_ = v_hashCode_924_;
goto v___jp_915_;
}
case 5:
{
uint64_t v_hashCode_925_; 
v_hashCode_925_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*5);
v___y_916_ = v_hashCode_925_;
goto v___jp_915_;
}
default: 
{
uint64_t v_hashCode_926_; 
v_hashCode_926_ = lean_ctor_get_uint64(v_expr_911_, sizeof(void*)*4);
v___y_916_ = v_hashCode_926_;
goto v___jp_915_;
}
}
v___jp_915_:
{
uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; lean_object* v___x_920_; 
v___x_917_ = lean_uint64_mix_hash(v___x_914_, v___y_916_);
v___x_918_ = lean_uint64_mix_hash(v___x_913_, v___x_917_);
v___x_919_ = lean_uint64_mix_hash(v___x_912_, v___x_918_);
v___x_920_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_920_, 0, v_w_908_);
lean_ctor_set(v___x_920_, 1, v_start_909_);
lean_ctor_set(v___x_920_, 2, v_len_910_);
lean_ctor_set(v___x_920_, 3, v_expr_911_);
lean_ctor_set_uint64(v___x_920_, sizeof(void*)*4, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_927_, lean_object* v_lhs_928_, uint8_t v_op_929_, lean_object* v_rhs_930_){
_start:
{
uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v___y_934_; uint64_t v___y_935_; uint64_t v___y_936_; uint64_t v___y_943_; 
v___x_931_ = 13ULL;
v___x_932_ = lean_uint64_of_nat(v_w_927_);
switch(lean_obj_tag(v_lhs_928_))
{
case 0:
{
uint64_t v_hashCode_951_; 
v_hashCode_951_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*2);
v___y_943_ = v_hashCode_951_;
goto v___jp_942_;
}
case 1:
{
uint64_t v_hashCode_952_; 
v_hashCode_952_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*2);
v___y_943_ = v_hashCode_952_;
goto v___jp_942_;
}
case 3:
{
uint64_t v_hashCode_953_; 
v_hashCode_953_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*3);
v___y_943_ = v_hashCode_953_;
goto v___jp_942_;
}
case 4:
{
uint64_t v_hashCode_954_; 
v_hashCode_954_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*3);
v___y_943_ = v_hashCode_954_;
goto v___jp_942_;
}
case 5:
{
uint64_t v_hashCode_955_; 
v_hashCode_955_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*5);
v___y_943_ = v_hashCode_955_;
goto v___jp_942_;
}
default: 
{
uint64_t v_hashCode_956_; 
v_hashCode_956_ = lean_ctor_get_uint64(v_lhs_928_, sizeof(void*)*4);
v___y_943_ = v_hashCode_956_;
goto v___jp_942_;
}
}
v___jp_933_:
{
uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; lean_object* v___x_941_; 
v___x_937_ = lean_uint64_mix_hash(v___y_935_, v___y_936_);
v___x_938_ = lean_uint64_mix_hash(v___y_934_, v___x_937_);
v___x_939_ = lean_uint64_mix_hash(v___x_932_, v___x_938_);
v___x_940_ = lean_uint64_mix_hash(v___x_931_, v___x_939_);
v___x_941_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_941_, 0, v_w_927_);
lean_ctor_set(v___x_941_, 1, v_lhs_928_);
lean_ctor_set(v___x_941_, 2, v_rhs_930_);
lean_ctor_set_uint64(v___x_941_, sizeof(void*)*3, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*3 + 8, v_op_929_);
return v___x_941_;
}
v___jp_942_:
{
uint64_t v___x_944_; 
v___x_944_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_929_);
switch(lean_obj_tag(v_rhs_930_))
{
case 0:
{
uint64_t v_hashCode_945_; 
v_hashCode_945_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*2);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_945_;
goto v___jp_933_;
}
case 1:
{
uint64_t v_hashCode_946_; 
v_hashCode_946_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*2);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_946_;
goto v___jp_933_;
}
case 3:
{
uint64_t v_hashCode_947_; 
v_hashCode_947_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*3);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_947_;
goto v___jp_933_;
}
case 4:
{
uint64_t v_hashCode_948_; 
v_hashCode_948_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*3);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_948_;
goto v___jp_933_;
}
case 5:
{
uint64_t v_hashCode_949_; 
v_hashCode_949_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*5);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_949_;
goto v___jp_933_;
}
default: 
{
uint64_t v_hashCode_950_; 
v_hashCode_950_ = lean_ctor_get_uint64(v_rhs_930_, sizeof(void*)*4);
v___y_934_ = v___y_943_;
v___y_935_ = v___x_944_;
v___y_936_ = v_hashCode_950_;
goto v___jp_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_957_, lean_object* v_lhs_958_, lean_object* v_op_959_, lean_object* v_rhs_960_){
_start:
{
uint8_t v_op_boxed_961_; lean_object* v_res_962_; 
v_op_boxed_961_ = lean_unbox(v_op_959_);
v_res_962_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_957_, v_lhs_958_, v_op_boxed_961_, v_rhs_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_963_, lean_object* v_op_964_, lean_object* v_operand_965_){
_start:
{
uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___y_970_; 
v___x_966_ = 17ULL;
v___x_967_ = lean_uint64_of_nat(v_w_963_);
v___x_968_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_964_);
switch(lean_obj_tag(v_operand_965_))
{
case 0:
{
uint64_t v_hashCode_975_; 
v_hashCode_975_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*2);
v___y_970_ = v_hashCode_975_;
goto v___jp_969_;
}
case 1:
{
uint64_t v_hashCode_976_; 
v_hashCode_976_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*2);
v___y_970_ = v_hashCode_976_;
goto v___jp_969_;
}
case 3:
{
uint64_t v_hashCode_977_; 
v_hashCode_977_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*3);
v___y_970_ = v_hashCode_977_;
goto v___jp_969_;
}
case 4:
{
uint64_t v_hashCode_978_; 
v_hashCode_978_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*3);
v___y_970_ = v_hashCode_978_;
goto v___jp_969_;
}
case 5:
{
uint64_t v_hashCode_979_; 
v_hashCode_979_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*5);
v___y_970_ = v_hashCode_979_;
goto v___jp_969_;
}
default: 
{
uint64_t v_hashCode_980_; 
v_hashCode_980_ = lean_ctor_get_uint64(v_operand_965_, sizeof(void*)*4);
v___y_970_ = v_hashCode_980_;
goto v___jp_969_;
}
}
v___jp_969_:
{
uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; lean_object* v___x_974_; 
v___x_971_ = lean_uint64_mix_hash(v___x_968_, v___y_970_);
v___x_972_ = lean_uint64_mix_hash(v___x_967_, v___x_971_);
v___x_973_ = lean_uint64_mix_hash(v___x_966_, v___x_972_);
v___x_974_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_974_, 0, v_w_963_);
lean_ctor_set(v___x_974_, 1, v_op_964_);
lean_ctor_set(v___x_974_, 2, v_operand_965_);
lean_ctor_set_uint64(v___x_974_, sizeof(void*)*3, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_981_, lean_object* v_r_982_, lean_object* v_w_983_, lean_object* v_lhs_984_, lean_object* v_rhs_985_){
_start:
{
uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___y_989_; uint64_t v___y_990_; uint64_t v___y_996_; 
v___x_986_ = 19ULL;
v___x_987_ = lean_uint64_of_nat(v_w_983_);
switch(lean_obj_tag(v_lhs_984_))
{
case 0:
{
uint64_t v_hashCode_1003_; 
v_hashCode_1003_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*2);
v___y_996_ = v_hashCode_1003_;
goto v___jp_995_;
}
case 1:
{
uint64_t v_hashCode_1004_; 
v_hashCode_1004_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*2);
v___y_996_ = v_hashCode_1004_;
goto v___jp_995_;
}
case 3:
{
uint64_t v_hashCode_1005_; 
v_hashCode_1005_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*3);
v___y_996_ = v_hashCode_1005_;
goto v___jp_995_;
}
case 4:
{
uint64_t v_hashCode_1006_; 
v_hashCode_1006_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*3);
v___y_996_ = v_hashCode_1006_;
goto v___jp_995_;
}
case 5:
{
uint64_t v_hashCode_1007_; 
v_hashCode_1007_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*5);
v___y_996_ = v_hashCode_1007_;
goto v___jp_995_;
}
default: 
{
uint64_t v_hashCode_1008_; 
v_hashCode_1008_ = lean_ctor_get_uint64(v_lhs_984_, sizeof(void*)*4);
v___y_996_ = v_hashCode_1008_;
goto v___jp_995_;
}
}
v___jp_988_:
{
uint64_t v___x_991_; uint64_t v___x_992_; uint64_t v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_uint64_mix_hash(v___y_989_, v___y_990_);
v___x_992_ = lean_uint64_mix_hash(v___x_987_, v___x_991_);
v___x_993_ = lean_uint64_mix_hash(v___x_986_, v___x_992_);
v___x_994_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_994_, 0, v_l_981_);
lean_ctor_set(v___x_994_, 1, v_r_982_);
lean_ctor_set(v___x_994_, 2, v_w_983_);
lean_ctor_set(v___x_994_, 3, v_lhs_984_);
lean_ctor_set(v___x_994_, 4, v_rhs_985_);
lean_ctor_set_uint64(v___x_994_, sizeof(void*)*5, v___x_993_);
return v___x_994_;
}
v___jp_995_:
{
switch(lean_obj_tag(v_rhs_985_))
{
case 0:
{
uint64_t v_hashCode_997_; 
v_hashCode_997_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*2);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_997_;
goto v___jp_988_;
}
case 1:
{
uint64_t v_hashCode_998_; 
v_hashCode_998_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*2);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_998_;
goto v___jp_988_;
}
case 3:
{
uint64_t v_hashCode_999_; 
v_hashCode_999_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*3);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_999_;
goto v___jp_988_;
}
case 4:
{
uint64_t v_hashCode_1000_; 
v_hashCode_1000_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*3);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_1000_;
goto v___jp_988_;
}
case 5:
{
uint64_t v_hashCode_1001_; 
v_hashCode_1001_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*5);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_1001_;
goto v___jp_988_;
}
default: 
{
uint64_t v_hashCode_1002_; 
v_hashCode_1002_ = lean_ctor_get_uint64(v_rhs_985_, sizeof(void*)*4);
v___y_989_ = v___y_996_;
v___y_990_ = v_hashCode_1002_;
goto v___jp_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_1009_, lean_object* v_r_1010_, lean_object* v_w_1011_, lean_object* v_lhs_1012_, lean_object* v_rhs_1013_, lean_object* v_h_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_1009_, v_r_1010_, v_w_1011_, v_lhs_1012_, v_rhs_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_1016_, lean_object* v_w_x27_1017_, lean_object* v_n_1018_, lean_object* v_expr_1019_){
_start:
{
uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___y_1024_; 
v___x_1020_ = 23ULL;
v___x_1021_ = lean_uint64_of_nat(v_w_x27_1017_);
v___x_1022_ = lean_uint64_of_nat(v_n_1018_);
switch(lean_obj_tag(v_expr_1019_))
{
case 0:
{
uint64_t v_hashCode_1029_; 
v_hashCode_1029_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*2);
v___y_1024_ = v_hashCode_1029_;
goto v___jp_1023_;
}
case 1:
{
uint64_t v_hashCode_1030_; 
v_hashCode_1030_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*2);
v___y_1024_ = v_hashCode_1030_;
goto v___jp_1023_;
}
case 3:
{
uint64_t v_hashCode_1031_; 
v_hashCode_1031_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*3);
v___y_1024_ = v_hashCode_1031_;
goto v___jp_1023_;
}
case 4:
{
uint64_t v_hashCode_1032_; 
v_hashCode_1032_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*3);
v___y_1024_ = v_hashCode_1032_;
goto v___jp_1023_;
}
case 5:
{
uint64_t v_hashCode_1033_; 
v_hashCode_1033_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*5);
v___y_1024_ = v_hashCode_1033_;
goto v___jp_1023_;
}
default: 
{
uint64_t v_hashCode_1034_; 
v_hashCode_1034_ = lean_ctor_get_uint64(v_expr_1019_, sizeof(void*)*4);
v___y_1024_ = v_hashCode_1034_;
goto v___jp_1023_;
}
}
v___jp_1023_:
{
uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_uint64_mix_hash(v___x_1022_, v___y_1024_);
v___x_1026_ = lean_uint64_mix_hash(v___x_1021_, v___x_1025_);
v___x_1027_ = lean_uint64_mix_hash(v___x_1020_, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1028_, 0, v_w_1016_);
lean_ctor_set(v___x_1028_, 1, v_w_x27_1017_);
lean_ctor_set(v___x_1028_, 2, v_n_1018_);
lean_ctor_set(v___x_1028_, 3, v_expr_1019_);
lean_ctor_set_uint64(v___x_1028_, sizeof(void*)*4, v___x_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1035_, lean_object* v_w_x27_1036_, lean_object* v_n_1037_, lean_object* v_expr_1038_, lean_object* v_h_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1035_, v_w_x27_1036_, v_n_1037_, v_expr_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1041_, lean_object* v_n_1042_, lean_object* v_lhs_1043_, lean_object* v_rhs_1044_){
_start:
{
uint64_t v___x_1045_; uint64_t v___x_1046_; uint64_t v___y_1048_; uint64_t v___y_1049_; uint64_t v___y_1055_; 
v___x_1045_ = 29ULL;
v___x_1046_ = lean_uint64_of_nat(v_m_1041_);
switch(lean_obj_tag(v_lhs_1043_))
{
case 0:
{
uint64_t v_hashCode_1062_; 
v_hashCode_1062_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*2);
v___y_1055_ = v_hashCode_1062_;
goto v___jp_1054_;
}
case 1:
{
uint64_t v_hashCode_1063_; 
v_hashCode_1063_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*2);
v___y_1055_ = v_hashCode_1063_;
goto v___jp_1054_;
}
case 3:
{
uint64_t v_hashCode_1064_; 
v_hashCode_1064_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*3);
v___y_1055_ = v_hashCode_1064_;
goto v___jp_1054_;
}
case 4:
{
uint64_t v_hashCode_1065_; 
v_hashCode_1065_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*3);
v___y_1055_ = v_hashCode_1065_;
goto v___jp_1054_;
}
case 5:
{
uint64_t v_hashCode_1066_; 
v_hashCode_1066_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*5);
v___y_1055_ = v_hashCode_1066_;
goto v___jp_1054_;
}
default: 
{
uint64_t v_hashCode_1067_; 
v_hashCode_1067_ = lean_ctor_get_uint64(v_lhs_1043_, sizeof(void*)*4);
v___y_1055_ = v_hashCode_1067_;
goto v___jp_1054_;
}
}
v___jp_1047_:
{
uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1050_ = lean_uint64_mix_hash(v___y_1048_, v___y_1049_);
v___x_1051_ = lean_uint64_mix_hash(v___x_1046_, v___x_1050_);
v___x_1052_ = lean_uint64_mix_hash(v___x_1045_, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1053_, 0, v_m_1041_);
lean_ctor_set(v___x_1053_, 1, v_n_1042_);
lean_ctor_set(v___x_1053_, 2, v_lhs_1043_);
lean_ctor_set(v___x_1053_, 3, v_rhs_1044_);
lean_ctor_set_uint64(v___x_1053_, sizeof(void*)*4, v___x_1052_);
return v___x_1053_;
}
v___jp_1054_:
{
switch(lean_obj_tag(v_rhs_1044_))
{
case 0:
{
uint64_t v_hashCode_1056_; 
v_hashCode_1056_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*2);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1056_;
goto v___jp_1047_;
}
case 1:
{
uint64_t v_hashCode_1057_; 
v_hashCode_1057_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*2);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1057_;
goto v___jp_1047_;
}
case 3:
{
uint64_t v_hashCode_1058_; 
v_hashCode_1058_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*3);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1058_;
goto v___jp_1047_;
}
case 4:
{
uint64_t v_hashCode_1059_; 
v_hashCode_1059_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*3);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1059_;
goto v___jp_1047_;
}
case 5:
{
uint64_t v_hashCode_1060_; 
v_hashCode_1060_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*5);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1060_;
goto v___jp_1047_;
}
default: 
{
uint64_t v_hashCode_1061_; 
v_hashCode_1061_ = lean_ctor_get_uint64(v_rhs_1044_, sizeof(void*)*4);
v___y_1048_ = v___y_1055_;
v___y_1049_ = v_hashCode_1061_;
goto v___jp_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1068_, lean_object* v_n_1069_, lean_object* v_lhs_1070_, lean_object* v_rhs_1071_){
_start:
{
uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v___y_1075_; uint64_t v___y_1076_; uint64_t v___y_1082_; 
v___x_1072_ = 31ULL;
v___x_1073_ = lean_uint64_of_nat(v_m_1068_);
switch(lean_obj_tag(v_lhs_1070_))
{
case 0:
{
uint64_t v_hashCode_1089_; 
v_hashCode_1089_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*2);
v___y_1082_ = v_hashCode_1089_;
goto v___jp_1081_;
}
case 1:
{
uint64_t v_hashCode_1090_; 
v_hashCode_1090_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*2);
v___y_1082_ = v_hashCode_1090_;
goto v___jp_1081_;
}
case 3:
{
uint64_t v_hashCode_1091_; 
v_hashCode_1091_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*3);
v___y_1082_ = v_hashCode_1091_;
goto v___jp_1081_;
}
case 4:
{
uint64_t v_hashCode_1092_; 
v_hashCode_1092_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*3);
v___y_1082_ = v_hashCode_1092_;
goto v___jp_1081_;
}
case 5:
{
uint64_t v_hashCode_1093_; 
v_hashCode_1093_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*5);
v___y_1082_ = v_hashCode_1093_;
goto v___jp_1081_;
}
default: 
{
uint64_t v_hashCode_1094_; 
v_hashCode_1094_ = lean_ctor_get_uint64(v_lhs_1070_, sizeof(void*)*4);
v___y_1082_ = v_hashCode_1094_;
goto v___jp_1081_;
}
}
v___jp_1074_:
{
uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = lean_uint64_mix_hash(v___y_1075_, v___y_1076_);
v___x_1078_ = lean_uint64_mix_hash(v___x_1073_, v___x_1077_);
v___x_1079_ = lean_uint64_mix_hash(v___x_1072_, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1080_, 0, v_m_1068_);
lean_ctor_set(v___x_1080_, 1, v_n_1069_);
lean_ctor_set(v___x_1080_, 2, v_lhs_1070_);
lean_ctor_set(v___x_1080_, 3, v_rhs_1071_);
lean_ctor_set_uint64(v___x_1080_, sizeof(void*)*4, v___x_1079_);
return v___x_1080_;
}
v___jp_1081_:
{
switch(lean_obj_tag(v_rhs_1071_))
{
case 0:
{
uint64_t v_hashCode_1083_; 
v_hashCode_1083_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*2);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1083_;
goto v___jp_1074_;
}
case 1:
{
uint64_t v_hashCode_1084_; 
v_hashCode_1084_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*2);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1084_;
goto v___jp_1074_;
}
case 3:
{
uint64_t v_hashCode_1085_; 
v_hashCode_1085_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*3);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1085_;
goto v___jp_1074_;
}
case 4:
{
uint64_t v_hashCode_1086_; 
v_hashCode_1086_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*3);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1086_;
goto v___jp_1074_;
}
case 5:
{
uint64_t v_hashCode_1087_; 
v_hashCode_1087_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*5);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1087_;
goto v___jp_1074_;
}
default: 
{
uint64_t v_hashCode_1088_; 
v_hashCode_1088_ = lean_ctor_get_uint64(v_rhs_1071_, sizeof(void*)*4);
v___y_1075_ = v___y_1082_;
v___y_1076_ = v_hashCode_1088_;
goto v___jp_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1095_, lean_object* v_n_1096_, lean_object* v_lhs_1097_, lean_object* v_rhs_1098_){
_start:
{
uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___y_1102_; uint64_t v___y_1103_; uint64_t v___y_1109_; 
v___x_1099_ = 37ULL;
v___x_1100_ = lean_uint64_of_nat(v_m_1095_);
switch(lean_obj_tag(v_lhs_1097_))
{
case 0:
{
uint64_t v_hashCode_1116_; 
v_hashCode_1116_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*2);
v___y_1109_ = v_hashCode_1116_;
goto v___jp_1108_;
}
case 1:
{
uint64_t v_hashCode_1117_; 
v_hashCode_1117_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*2);
v___y_1109_ = v_hashCode_1117_;
goto v___jp_1108_;
}
case 3:
{
uint64_t v_hashCode_1118_; 
v_hashCode_1118_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*3);
v___y_1109_ = v_hashCode_1118_;
goto v___jp_1108_;
}
case 4:
{
uint64_t v_hashCode_1119_; 
v_hashCode_1119_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*3);
v___y_1109_ = v_hashCode_1119_;
goto v___jp_1108_;
}
case 5:
{
uint64_t v_hashCode_1120_; 
v_hashCode_1120_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*5);
v___y_1109_ = v_hashCode_1120_;
goto v___jp_1108_;
}
default: 
{
uint64_t v_hashCode_1121_; 
v_hashCode_1121_ = lean_ctor_get_uint64(v_lhs_1097_, sizeof(void*)*4);
v___y_1109_ = v_hashCode_1121_;
goto v___jp_1108_;
}
}
v___jp_1101_:
{
uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = lean_uint64_mix_hash(v___y_1102_, v___y_1103_);
v___x_1105_ = lean_uint64_mix_hash(v___x_1100_, v___x_1104_);
v___x_1106_ = lean_uint64_mix_hash(v___x_1099_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1107_, 0, v_m_1095_);
lean_ctor_set(v___x_1107_, 1, v_n_1096_);
lean_ctor_set(v___x_1107_, 2, v_lhs_1097_);
lean_ctor_set(v___x_1107_, 3, v_rhs_1098_);
lean_ctor_set_uint64(v___x_1107_, sizeof(void*)*4, v___x_1106_);
return v___x_1107_;
}
v___jp_1108_:
{
switch(lean_obj_tag(v_rhs_1098_))
{
case 0:
{
uint64_t v_hashCode_1110_; 
v_hashCode_1110_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*2);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1110_;
goto v___jp_1101_;
}
case 1:
{
uint64_t v_hashCode_1111_; 
v_hashCode_1111_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*2);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1111_;
goto v___jp_1101_;
}
case 3:
{
uint64_t v_hashCode_1112_; 
v_hashCode_1112_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*3);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1112_;
goto v___jp_1101_;
}
case 4:
{
uint64_t v_hashCode_1113_; 
v_hashCode_1113_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*3);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1113_;
goto v___jp_1101_;
}
case 5:
{
uint64_t v_hashCode_1114_; 
v_hashCode_1114_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*5);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1114_;
goto v___jp_1101_;
}
default: 
{
uint64_t v_hashCode_1115_; 
v_hashCode_1115_ = lean_ctor_get_uint64(v_rhs_1098_, sizeof(void*)*4);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v_hashCode_1115_;
goto v___jp_1101_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1122_){
_start:
{
switch(lean_obj_tag(v_x_1122_))
{
case 0:
{
uint64_t v_hashCode_1123_; 
v_hashCode_1123_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*2);
return v_hashCode_1123_;
}
case 1:
{
uint64_t v_hashCode_1124_; 
v_hashCode_1124_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*2);
return v_hashCode_1124_;
}
case 3:
{
uint64_t v_hashCode_1125_; 
v_hashCode_1125_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*3);
return v_hashCode_1125_;
}
case 4:
{
uint64_t v_hashCode_1126_; 
v_hashCode_1126_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*3);
return v_hashCode_1126_;
}
case 5:
{
uint64_t v_hashCode_1127_; 
v_hashCode_1127_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*5);
return v_hashCode_1127_;
}
default: 
{
uint64_t v_hashCode_1128_; 
v_hashCode_1128_ = lean_ctor_get_uint64(v_x_1122_, sizeof(void*)*4);
return v_hashCode_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* v_x_1129_){
_start:
{
uint64_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1129_);
lean_dec_ref(v_x_1129_);
v_r_1131_ = lean_box_uint64(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1132_, lean_object* v_x_1133_){
_start:
{
switch(lean_obj_tag(v_x_1133_))
{
case 0:
{
uint64_t v_hashCode_1134_; 
v_hashCode_1134_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*2);
return v_hashCode_1134_;
}
case 1:
{
uint64_t v_hashCode_1135_; 
v_hashCode_1135_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*2);
return v_hashCode_1135_;
}
case 3:
{
uint64_t v_hashCode_1136_; 
v_hashCode_1136_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*3);
return v_hashCode_1136_;
}
case 4:
{
uint64_t v_hashCode_1137_; 
v_hashCode_1137_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*3);
return v_hashCode_1137_;
}
case 5:
{
uint64_t v_hashCode_1138_; 
v_hashCode_1138_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*5);
return v_hashCode_1138_;
}
default: 
{
uint64_t v_hashCode_1139_; 
v_hashCode_1139_ = lean_ctor_get_uint64(v_x_1133_, sizeof(void*)*4);
return v_hashCode_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1140_, lean_object* v_x_1141_){
_start:
{
uint64_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1140_, v_x_1141_);
lean_dec_ref(v_x_1141_);
lean_dec(v_a_1140_);
v_r_1143_ = lean_box_uint64(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object* v_expr_1144_){
_start:
{
switch(lean_obj_tag(v_expr_1144_))
{
case 0:
{
uint64_t v_hashCode_1145_; 
v_hashCode_1145_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*2);
return v_hashCode_1145_;
}
case 1:
{
uint64_t v_hashCode_1146_; 
v_hashCode_1146_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*2);
return v_hashCode_1146_;
}
case 3:
{
uint64_t v_hashCode_1147_; 
v_hashCode_1147_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*3);
return v_hashCode_1147_;
}
case 4:
{
uint64_t v_hashCode_1148_; 
v_hashCode_1148_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*3);
return v_hashCode_1148_;
}
case 5:
{
uint64_t v_hashCode_1149_; 
v_hashCode_1149_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*5);
return v_hashCode_1149_;
}
default: 
{
uint64_t v_hashCode_1150_; 
v_hashCode_1150_ = lean_ctor_get_uint64(v_expr_1144_, sizeof(void*)*4);
return v_hashCode_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object* v_expr_1151_){
_start:
{
uint64_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(v_expr_1151_);
lean_dec_ref(v_expr_1151_);
v_r_1153_ = lean_box_uint64(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1155_){
_start:
{
lean_object* v___f_1156_; 
v___f_1156_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0));
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
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1159_, lean_object* v_r_1160_){
_start:
{
size_t v___x_1161_; size_t v___x_1162_; uint8_t v___x_1163_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; uint64_t v___y_1187_; uint64_t v___y_1188_; uint64_t v___y_1267_; 
v___x_1161_ = lean_ptr_addr(v_l_1159_);
v___x_1162_ = lean_ptr_addr(v_r_1160_);
v___x_1163_ = lean_usize_dec_eq(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
switch(lean_obj_tag(v_l_1159_))
{
case 0:
{
uint64_t v_hashCode_1274_; 
v_hashCode_1274_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*2);
v___y_1267_ = v_hashCode_1274_;
goto v___jp_1266_;
}
case 1:
{
uint64_t v_hashCode_1275_; 
v_hashCode_1275_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*2);
v___y_1267_ = v_hashCode_1275_;
goto v___jp_1266_;
}
case 3:
{
uint64_t v_hashCode_1276_; 
v_hashCode_1276_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*3);
v___y_1267_ = v_hashCode_1276_;
goto v___jp_1266_;
}
case 4:
{
uint64_t v_hashCode_1277_; 
v_hashCode_1277_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*3);
v___y_1267_ = v_hashCode_1277_;
goto v___jp_1266_;
}
case 5:
{
uint64_t v_hashCode_1278_; 
v_hashCode_1278_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*5);
v___y_1267_ = v_hashCode_1278_;
goto v___jp_1266_;
}
default: 
{
uint64_t v_hashCode_1279_; 
v_hashCode_1279_ = lean_ctor_get_uint64(v_l_1159_, sizeof(void*)*4);
v___y_1267_ = v_hashCode_1279_;
goto v___jp_1266_;
}
}
}
else
{
return v___x_1163_;
}
v___jp_1164_:
{
if (v___y_1168_ == 0)
{
return v___y_1168_;
}
else
{
uint8_t v_decide_1169_; 
v_decide_1169_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1166_, v___y_1165_);
if (v_decide_1169_ == 0)
{
return v___x_1163_;
}
else
{
return v___y_1168_;
}
}
}
v___jp_1170_:
{
if (v___y_1177_ == 0)
{
return v___y_1177_;
}
else
{
uint8_t v_decide_1178_; 
v_decide_1178_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1176_, v___y_1173_);
if (v_decide_1178_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v_decide_1179_; 
v_decide_1179_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1172_, v___y_1171_);
if (v_decide_1179_ == 0)
{
return v___x_1163_;
}
else
{
return v___y_1177_;
}
}
}
}
v___jp_1180_:
{
if (v___y_1184_ == 0)
{
return v___y_1184_;
}
else
{
uint8_t v_decide_1185_; 
v_decide_1185_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v___y_1181_, v___y_1183_);
if (v_decide_1185_ == 0)
{
return v___x_1163_;
}
else
{
return v___y_1184_;
}
}
}
v___jp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_uint64_dec_eq(v___y_1187_, v___y_1188_);
if (v___x_1189_ == 0)
{
return v___x_1163_;
}
else
{
if (v___x_1163_ == 0)
{
switch(lean_obj_tag(v_l_1159_))
{
case 0:
{
if (lean_obj_tag(v_r_1160_) == 0)
{
lean_object* v_idx_1190_; lean_object* v_idx_1191_; uint8_t v___x_1192_; 
v_idx_1190_ = lean_ctor_get(v_l_1159_, 1);
v_idx_1191_ = lean_ctor_get(v_r_1160_, 1);
v___x_1192_ = lean_nat_dec_eq(v_idx_1190_, v_idx_1191_);
return v___x_1192_;
}
else
{
return v___x_1163_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1160_) == 1)
{
lean_object* v_val_1193_; lean_object* v_val_1194_; uint8_t v___x_1195_; 
v_val_1193_ = lean_ctor_get(v_l_1159_, 1);
v_val_1194_ = lean_ctor_get(v_r_1160_, 1);
v___x_1195_ = lean_nat_dec_eq(v_val_1193_, v_val_1194_);
return v___x_1195_;
}
else
{
return v___x_1163_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1160_) == 2)
{
lean_object* v_w_1196_; lean_object* v_start_1197_; lean_object* v_expr_1198_; lean_object* v_w_1199_; lean_object* v_start_1200_; lean_object* v_expr_1201_; uint8_t v___x_1202_; 
v_w_1196_ = lean_ctor_get(v_l_1159_, 0);
v_start_1197_ = lean_ctor_get(v_l_1159_, 1);
v_expr_1198_ = lean_ctor_get(v_l_1159_, 3);
v_w_1199_ = lean_ctor_get(v_r_1160_, 0);
v_start_1200_ = lean_ctor_get(v_r_1160_, 1);
v_expr_1201_ = lean_ctor_get(v_r_1160_, 3);
v___x_1202_ = lean_nat_dec_eq(v_w_1196_, v_w_1199_);
if (v___x_1202_ == 0)
{
v___y_1165_ = v_expr_1201_;
v___y_1166_ = v_expr_1198_;
v___y_1167_ = v_w_1199_;
v___y_1168_ = v___x_1202_;
goto v___jp_1164_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_eq(v_start_1197_, v_start_1200_);
v___y_1165_ = v_expr_1201_;
v___y_1166_ = v_expr_1198_;
v___y_1167_ = v_w_1199_;
v___y_1168_ = v___x_1203_;
goto v___jp_1164_;
}
}
else
{
return v___x_1163_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1160_) == 3)
{
lean_object* v_lhs_1204_; uint8_t v_op_1205_; lean_object* v_rhs_1206_; lean_object* v_lhs_1207_; uint8_t v_op_1208_; lean_object* v_rhs_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_lhs_1204_ = lean_ctor_get(v_l_1159_, 1);
v_op_1205_ = lean_ctor_get_uint8(v_l_1159_, sizeof(void*)*3 + 8);
v_rhs_1206_ = lean_ctor_get(v_l_1159_, 2);
v_lhs_1207_ = lean_ctor_get(v_r_1160_, 1);
v_op_1208_ = lean_ctor_get_uint8(v_r_1160_, sizeof(void*)*3 + 8);
v_rhs_1209_ = lean_ctor_get(v_r_1160_, 2);
v___x_1210_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_op_1205_);
v___x_1211_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_op_1208_);
v___x_1212_ = lean_nat_dec_eq(v___x_1210_, v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1210_);
if (v___x_1212_ == 0)
{
return v___x_1212_;
}
else
{
uint8_t v_decide_1213_; 
v_decide_1213_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1204_, v_lhs_1207_);
if (v_decide_1213_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v_decide_1214_; 
v_decide_1214_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1206_, v_rhs_1209_);
if (v_decide_1214_ == 0)
{
return v___x_1163_;
}
else
{
return v___x_1212_;
}
}
}
}
else
{
return v___x_1163_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1160_) == 4)
{
lean_object* v_op_1215_; lean_object* v_operand_1216_; lean_object* v_op_1217_; lean_object* v_operand_1218_; uint8_t v___x_1219_; 
v_op_1215_ = lean_ctor_get(v_l_1159_, 1);
v_operand_1216_ = lean_ctor_get(v_l_1159_, 2);
v_op_1217_ = lean_ctor_get(v_r_1160_, 1);
v_operand_1218_ = lean_ctor_get(v_r_1160_, 2);
v___x_1219_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1215_, v_op_1217_);
if (v___x_1219_ == 0)
{
return v___x_1219_;
}
else
{
uint8_t v_decide_1220_; 
v_decide_1220_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_operand_1216_, v_operand_1218_);
if (v_decide_1220_ == 0)
{
return v___x_1163_;
}
else
{
return v___x_1219_;
}
}
}
else
{
return v___x_1163_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1160_) == 5)
{
lean_object* v_l_1221_; lean_object* v_r_1222_; lean_object* v_lhs_1223_; lean_object* v_rhs_1224_; lean_object* v_l_1225_; lean_object* v_r_1226_; lean_object* v_lhs_1227_; lean_object* v_rhs_1228_; uint8_t v___x_1229_; 
v_l_1221_ = lean_ctor_get(v_l_1159_, 0);
v_r_1222_ = lean_ctor_get(v_l_1159_, 1);
v_lhs_1223_ = lean_ctor_get(v_l_1159_, 3);
v_rhs_1224_ = lean_ctor_get(v_l_1159_, 4);
v_l_1225_ = lean_ctor_get(v_r_1160_, 0);
v_r_1226_ = lean_ctor_get(v_r_1160_, 1);
v_lhs_1227_ = lean_ctor_get(v_r_1160_, 3);
v_rhs_1228_ = lean_ctor_get(v_r_1160_, 4);
v___x_1229_ = lean_nat_dec_eq(v_l_1221_, v_l_1225_);
if (v___x_1229_ == 0)
{
v___y_1171_ = v_rhs_1228_;
v___y_1172_ = v_rhs_1224_;
v___y_1173_ = v_lhs_1227_;
v___y_1174_ = v_l_1225_;
v___y_1175_ = v_r_1226_;
v___y_1176_ = v_lhs_1223_;
v___y_1177_ = v___x_1229_;
goto v___jp_1170_;
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_eq(v_r_1222_, v_r_1226_);
v___y_1171_ = v_rhs_1228_;
v___y_1172_ = v_rhs_1224_;
v___y_1173_ = v_lhs_1227_;
v___y_1174_ = v_l_1225_;
v___y_1175_ = v_r_1226_;
v___y_1176_ = v_lhs_1223_;
v___y_1177_ = v___x_1230_;
goto v___jp_1170_;
}
}
else
{
return v___x_1163_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1160_) == 6)
{
lean_object* v_w_1231_; lean_object* v_n_1232_; lean_object* v_expr_1233_; lean_object* v_w_1234_; lean_object* v_n_1235_; lean_object* v_expr_1236_; uint8_t v___x_1237_; 
v_w_1231_ = lean_ctor_get(v_l_1159_, 0);
v_n_1232_ = lean_ctor_get(v_l_1159_, 2);
v_expr_1233_ = lean_ctor_get(v_l_1159_, 3);
v_w_1234_ = lean_ctor_get(v_r_1160_, 0);
v_n_1235_ = lean_ctor_get(v_r_1160_, 2);
v_expr_1236_ = lean_ctor_get(v_r_1160_, 3);
v___x_1237_ = lean_nat_dec_eq(v_n_1232_, v_n_1235_);
if (v___x_1237_ == 0)
{
v___y_1181_ = v_expr_1233_;
v___y_1182_ = v_w_1234_;
v___y_1183_ = v_expr_1236_;
v___y_1184_ = v___x_1237_;
goto v___jp_1180_;
}
else
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_nat_dec_eq(v_w_1231_, v_w_1234_);
v___y_1181_ = v_expr_1233_;
v___y_1182_ = v_w_1234_;
v___y_1183_ = v_expr_1236_;
v___y_1184_ = v___x_1238_;
goto v___jp_1180_;
}
}
else
{
return v___x_1163_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1160_) == 7)
{
lean_object* v_n_1239_; lean_object* v_lhs_1240_; lean_object* v_rhs_1241_; lean_object* v_n_1242_; lean_object* v_lhs_1243_; lean_object* v_rhs_1244_; uint8_t v___x_1245_; 
v_n_1239_ = lean_ctor_get(v_l_1159_, 1);
v_lhs_1240_ = lean_ctor_get(v_l_1159_, 2);
v_rhs_1241_ = lean_ctor_get(v_l_1159_, 3);
v_n_1242_ = lean_ctor_get(v_r_1160_, 1);
v_lhs_1243_ = lean_ctor_get(v_r_1160_, 2);
v_rhs_1244_ = lean_ctor_get(v_r_1160_, 3);
v___x_1245_ = lean_nat_dec_eq(v_n_1239_, v_n_1242_);
if (v___x_1245_ == 0)
{
return v___x_1245_;
}
else
{
uint8_t v_decide_1246_; 
v_decide_1246_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1240_, v_lhs_1243_);
if (v_decide_1246_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v_decide_1247_; 
v_decide_1247_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1241_, v_rhs_1244_);
if (v_decide_1247_ == 0)
{
return v___x_1163_;
}
else
{
return v___x_1245_;
}
}
}
}
else
{
return v___x_1163_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1160_) == 8)
{
lean_object* v_n_1248_; lean_object* v_lhs_1249_; lean_object* v_rhs_1250_; lean_object* v_n_1251_; lean_object* v_lhs_1252_; lean_object* v_rhs_1253_; uint8_t v___x_1254_; 
v_n_1248_ = lean_ctor_get(v_l_1159_, 1);
v_lhs_1249_ = lean_ctor_get(v_l_1159_, 2);
v_rhs_1250_ = lean_ctor_get(v_l_1159_, 3);
v_n_1251_ = lean_ctor_get(v_r_1160_, 1);
v_lhs_1252_ = lean_ctor_get(v_r_1160_, 2);
v_rhs_1253_ = lean_ctor_get(v_r_1160_, 3);
v___x_1254_ = lean_nat_dec_eq(v_n_1248_, v_n_1251_);
if (v___x_1254_ == 0)
{
return v___x_1254_;
}
else
{
uint8_t v_decide_1255_; 
v_decide_1255_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1249_, v_lhs_1252_);
if (v_decide_1255_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v_decide_1256_; 
v_decide_1256_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1250_, v_rhs_1253_);
if (v_decide_1256_ == 0)
{
return v___x_1163_;
}
else
{
return v___x_1254_;
}
}
}
}
else
{
return v___x_1163_;
}
}
default: 
{
if (lean_obj_tag(v_r_1160_) == 9)
{
lean_object* v_n_1257_; lean_object* v_lhs_1258_; lean_object* v_rhs_1259_; lean_object* v_n_1260_; lean_object* v_lhs_1261_; lean_object* v_rhs_1262_; uint8_t v___x_1263_; 
v_n_1257_ = lean_ctor_get(v_l_1159_, 1);
v_lhs_1258_ = lean_ctor_get(v_l_1159_, 2);
v_rhs_1259_ = lean_ctor_get(v_l_1159_, 3);
v_n_1260_ = lean_ctor_get(v_r_1160_, 1);
v_lhs_1261_ = lean_ctor_get(v_r_1160_, 2);
v_rhs_1262_ = lean_ctor_get(v_r_1160_, 3);
v___x_1263_ = lean_nat_dec_eq(v_n_1257_, v_n_1260_);
if (v___x_1263_ == 0)
{
return v___x_1263_;
}
else
{
uint8_t v_decide_1264_; 
v_decide_1264_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1258_, v_lhs_1261_);
if (v_decide_1264_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v_decide_1265_; 
v_decide_1265_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1259_, v_rhs_1262_);
if (v_decide_1265_ == 0)
{
return v___x_1163_;
}
else
{
return v___x_1263_;
}
}
}
}
else
{
return v___x_1163_;
}
}
}
}
else
{
return v___x_1163_;
}
}
}
v___jp_1266_:
{
switch(lean_obj_tag(v_r_1160_))
{
case 0:
{
uint64_t v_hashCode_1268_; 
v_hashCode_1268_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*2);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1268_;
goto v___jp_1186_;
}
case 1:
{
uint64_t v_hashCode_1269_; 
v_hashCode_1269_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*2);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1269_;
goto v___jp_1186_;
}
case 3:
{
uint64_t v_hashCode_1270_; 
v_hashCode_1270_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*3);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1270_;
goto v___jp_1186_;
}
case 4:
{
uint64_t v_hashCode_1271_; 
v_hashCode_1271_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*3);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1271_;
goto v___jp_1186_;
}
case 5:
{
uint64_t v_hashCode_1272_; 
v_hashCode_1272_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*5);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1272_;
goto v___jp_1186_;
}
default: 
{
uint64_t v_hashCode_1273_; 
v_hashCode_1273_ = lean_ctor_get_uint64(v_r_1160_, sizeof(void*)*4);
v___y_1187_ = v___y_1267_;
v___y_1188_ = v_hashCode_1273_;
goto v___jp_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1280_, lean_object* v_r_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1280_, v_r_1281_);
lean_dec_ref(v_r_1281_);
lean_dec_ref(v_l_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1284_, lean_object* v_l_1285_, lean_object* v_r_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1285_, v_r_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1288_, lean_object* v_l_1289_, lean_object* v_r_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1288_, v_l_1289_, v_r_1290_);
lean_dec_ref(v_r_1290_);
lean_dec_ref(v_l_1289_);
lean_dec(v_w_1288_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1302_, lean_object* v_x_1303_){
_start:
{
switch(lean_obj_tag(v_x_1303_))
{
case 0:
{
lean_object* v_idx_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v_w_1302_);
v_idx_1304_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_idx_1304_);
lean_dec_ref_known(v_x_1303_, 2);
v___x_1305_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1306_ = l_Nat_reprFast(v_idx_1304_);
v___x_1307_ = lean_string_append(v___x_1305_, v___x_1306_);
lean_dec_ref(v___x_1306_);
return v___x_1307_;
}
case 1:
{
lean_object* v_val_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_val_1308_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_val_1308_);
lean_dec_ref_known(v_x_1303_, 2);
v___x_1309_ = l_BitVec_repr(v_w_1302_, v_val_1308_);
v___x_1310_ = l_Std_Format_defWidth;
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = l_Std_Format_pretty(v___x_1309_, v___x_1310_, v___x_1311_, v___x_1311_);
return v___x_1312_;
}
case 2:
{
lean_object* v_w_1313_; lean_object* v_start_1314_; lean_object* v_expr_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_w_1313_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_w_1313_);
v_start_1314_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_start_1314_);
v_expr_1315_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_expr_1315_);
lean_dec_ref_known(v_x_1303_, 4);
v___x_1316_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1313_, v_expr_1315_);
v___x_1317_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = l_Nat_reprFast(v_start_1314_);
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
v___x_1323_ = l_Nat_reprFast(v_w_1302_);
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
return v___x_1326_;
}
case 3:
{
lean_object* v_lhs_1327_; uint8_t v_op_1328_; lean_object* v_rhs_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_lhs_1327_ = lean_ctor_get(v_x_1303_, 1);
lean_inc_ref(v_lhs_1327_);
v_op_1328_ = lean_ctor_get_uint8(v_x_1303_, sizeof(void*)*3 + 8);
v_rhs_1329_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_rhs_1329_);
lean_dec_ref_known(v_x_1303_, 3);
v___x_1330_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1302_);
v___x_1331_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_lhs_1327_);
v___x_1332_ = lean_string_append(v___x_1330_, v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
v___x_1335_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1328_);
v___x_1336_ = lean_string_append(v___x_1334_, v___x_1335_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_string_append(v___x_1336_, v___x_1333_);
v___x_1338_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_rhs_1329_);
v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1341_ = lean_string_append(v___x_1339_, v___x_1340_);
return v___x_1341_;
}
case 4:
{
lean_object* v_op_1342_; lean_object* v_operand_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_op_1342_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_op_1342_);
v_operand_1343_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_operand_1343_);
lean_dec_ref_known(v_x_1303_, 3);
v___x_1344_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1345_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1342_);
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_operand_1343_);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
return v___x_1352_;
}
case 5:
{
lean_object* v_l_1353_; lean_object* v_r_1354_; lean_object* v_lhs_1355_; lean_object* v_rhs_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_w_1302_);
v_l_1353_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_l_1353_);
v_r_1354_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_r_1354_);
v_lhs_1355_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_lhs_1355_);
v_rhs_1356_ = lean_ctor_get(v_x_1303_, 4);
lean_inc_ref(v_rhs_1356_);
lean_dec_ref_known(v_x_1303_, 5);
v___x_1357_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1358_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1353_, v_lhs_1355_);
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
v___x_1362_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1354_, v_rhs_1356_);
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
return v___x_1365_;
}
case 6:
{
lean_object* v_w_1366_; lean_object* v_n_1367_; lean_object* v_expr_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_w_1302_);
v_w_1366_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_w_1366_);
v_n_1367_ = lean_ctor_get(v_x_1303_, 2);
lean_inc(v_n_1367_);
v_expr_1368_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_expr_1368_);
lean_dec_ref_known(v_x_1303_, 4);
v___x_1369_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1370_ = l_Nat_reprFast(v_n_1367_);
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
v___x_1374_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1366_, v_expr_1368_);
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
return v___x_1377_;
}
case 7:
{
lean_object* v_n_1378_; lean_object* v_lhs_1379_; lean_object* v_rhs_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_n_1378_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_n_1378_);
v_lhs_1379_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_lhs_1379_);
v_rhs_1380_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_rhs_1380_);
lean_dec_ref_known(v_x_1303_, 4);
v___x_1381_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1382_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_lhs_1379_);
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
v___x_1386_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1378_, v_rhs_1380_);
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
lean_dec_ref(v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
return v___x_1389_;
}
case 8:
{
lean_object* v_n_1390_; lean_object* v_lhs_1391_; lean_object* v_rhs_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_n_1390_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_n_1390_);
v_lhs_1391_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_lhs_1391_);
v_rhs_1392_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_rhs_1392_);
lean_dec_ref_known(v_x_1303_, 4);
v___x_1393_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1394_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_lhs_1391_);
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
v___x_1398_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1390_, v_rhs_1392_);
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
return v___x_1401_;
}
default: 
{
lean_object* v_n_1402_; lean_object* v_lhs_1403_; lean_object* v_rhs_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_n_1402_ = lean_ctor_get(v_x_1303_, 1);
lean_inc(v_n_1402_);
v_lhs_1403_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_lhs_1403_);
v_rhs_1404_ = lean_ctor_get(v_x_1303_, 3);
lean_inc_ref(v_rhs_1404_);
lean_dec_ref_known(v_x_1303_, 4);
v___x_1405_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1406_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1302_, v_lhs_1403_);
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1402_, v_rhs_1404_);
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1415_, 0, v_w_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1416_, lean_object* v_idx_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_RArray_getImpl___redArg(v_assign_1416_, v_idx_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1419_, lean_object* v_idx_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1419_, v_idx_1420_);
lean_dec(v_idx_1420_);
lean_dec_ref(v_assign_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1422_, lean_object* v_assign_1423_, lean_object* v_x_1424_){
_start:
{
switch(lean_obj_tag(v_x_1424_))
{
case 0:
{
lean_object* v_idx_1425_; lean_object* v_packedBv_1426_; lean_object* v_w_1427_; lean_object* v_bv_1428_; uint8_t v___x_1429_; 
v_idx_1425_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_idx_1425_);
lean_dec_ref_known(v_x_1424_, 2);
v_packedBv_1426_ = l_Lean_RArray_getImpl___redArg(v_assign_1423_, v_idx_1425_);
lean_dec(v_idx_1425_);
v_w_1427_ = lean_ctor_get(v_packedBv_1426_, 0);
lean_inc(v_w_1427_);
v_bv_1428_ = lean_ctor_get(v_packedBv_1426_, 1);
lean_inc(v_bv_1428_);
lean_dec(v_packedBv_1426_);
v___x_1429_ = lean_nat_dec_eq(v_w_1427_, v_w_1422_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = l_BitVec_setWidth(v_w_1427_, v_w_1422_, v_bv_1428_);
lean_dec(v_bv_1428_);
lean_dec(v_w_1422_);
lean_dec(v_w_1427_);
return v___x_1430_;
}
else
{
lean_dec(v_w_1427_);
lean_dec(v_w_1422_);
return v_bv_1428_;
}
}
case 1:
{
lean_object* v_val_1431_; 
lean_dec(v_w_1422_);
v_val_1431_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_val_1431_);
lean_dec_ref_known(v_x_1424_, 2);
return v_val_1431_;
}
case 2:
{
lean_object* v_w_1432_; lean_object* v_start_1433_; lean_object* v_expr_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_w_1432_ = lean_ctor_get(v_x_1424_, 0);
lean_inc(v_w_1432_);
v_start_1433_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_start_1433_);
v_expr_1434_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_expr_1434_);
lean_dec_ref_known(v_x_1424_, 4);
v___x_1435_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1432_, v_assign_1423_, v_expr_1434_);
v___x_1436_ = l_BitVec_extractLsb_x27___redArg(v_start_1433_, v_w_1422_, v___x_1435_);
lean_dec(v___x_1435_);
lean_dec(v_w_1422_);
lean_dec(v_start_1433_);
return v___x_1436_;
}
case 3:
{
lean_object* v_lhs_1437_; uint8_t v_op_1438_; lean_object* v_rhs_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_lhs_1437_ = lean_ctor_get(v_x_1424_, 1);
lean_inc_ref(v_lhs_1437_);
v_op_1438_ = lean_ctor_get_uint8(v_x_1424_, sizeof(void*)*3 + 8);
v_rhs_1439_ = lean_ctor_get(v_x_1424_, 2);
lean_inc_ref(v_rhs_1439_);
lean_dec_ref_known(v_x_1424_, 3);
lean_inc_n(v_w_1422_, 2);
v___x_1440_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_lhs_1437_);
v___x_1441_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_rhs_1439_);
v___x_1442_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1422_, v_op_1438_, v___x_1440_, v___x_1441_);
lean_dec(v___x_1441_);
lean_dec(v___x_1440_);
lean_dec(v_w_1422_);
return v___x_1442_;
}
case 4:
{
lean_object* v_op_1443_; lean_object* v_operand_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_op_1443_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_op_1443_);
v_operand_1444_ = lean_ctor_get(v_x_1424_, 2);
lean_inc_ref(v_operand_1444_);
lean_dec_ref_known(v_x_1424_, 3);
lean_inc(v_w_1422_);
v___x_1445_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_operand_1444_);
v___x_1446_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1422_, v_op_1443_, v___x_1445_);
lean_dec(v_op_1443_);
return v___x_1446_;
}
case 5:
{
lean_object* v_l_1447_; lean_object* v_r_1448_; lean_object* v_lhs_1449_; lean_object* v_rhs_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_w_1422_);
v_l_1447_ = lean_ctor_get(v_x_1424_, 0);
lean_inc(v_l_1447_);
v_r_1448_ = lean_ctor_get(v_x_1424_, 1);
lean_inc_n(v_r_1448_, 2);
v_lhs_1449_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_lhs_1449_);
v_rhs_1450_ = lean_ctor_get(v_x_1424_, 4);
lean_inc_ref(v_rhs_1450_);
lean_dec_ref_known(v_x_1424_, 5);
v___x_1451_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1447_, v_assign_1423_, v_lhs_1449_);
v___x_1452_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1448_, v_assign_1423_, v_rhs_1450_);
v___x_1453_ = l_BitVec_append___redArg(v_r_1448_, v___x_1451_, v___x_1452_);
lean_dec(v___x_1452_);
lean_dec(v___x_1451_);
lean_dec(v_r_1448_);
return v___x_1453_;
}
case 6:
{
lean_object* v_w_1454_; lean_object* v_n_1455_; lean_object* v_expr_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_w_1422_);
v_w_1454_ = lean_ctor_get(v_x_1424_, 0);
lean_inc_n(v_w_1454_, 2);
v_n_1455_ = lean_ctor_get(v_x_1424_, 2);
lean_inc(v_n_1455_);
v_expr_1456_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_expr_1456_);
lean_dec_ref_known(v_x_1424_, 4);
v___x_1457_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1454_, v_assign_1423_, v_expr_1456_);
v___x_1458_ = l_BitVec_replicate(v_w_1454_, v_n_1455_, v___x_1457_);
lean_dec(v___x_1457_);
lean_dec(v_n_1455_);
lean_dec(v_w_1454_);
return v___x_1458_;
}
case 7:
{
lean_object* v_n_1459_; lean_object* v_lhs_1460_; lean_object* v_rhs_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_n_1459_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_n_1459_);
v_lhs_1460_ = lean_ctor_get(v_x_1424_, 2);
lean_inc_ref(v_lhs_1460_);
v_rhs_1461_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_rhs_1461_);
lean_dec_ref_known(v_x_1424_, 4);
lean_inc(v_w_1422_);
v___x_1462_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_lhs_1460_);
v___x_1463_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1459_, v_assign_1423_, v_rhs_1461_);
v___x_1464_ = l_BitVec_shiftLeft(v_w_1422_, v___x_1462_, v___x_1463_);
lean_dec(v___x_1463_);
lean_dec(v___x_1462_);
lean_dec(v_w_1422_);
return v___x_1464_;
}
case 8:
{
lean_object* v_n_1465_; lean_object* v_lhs_1466_; lean_object* v_rhs_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_n_1465_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_n_1465_);
v_lhs_1466_ = lean_ctor_get(v_x_1424_, 2);
lean_inc_ref(v_lhs_1466_);
v_rhs_1467_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_rhs_1467_);
lean_dec_ref_known(v_x_1424_, 4);
v___x_1468_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_lhs_1466_);
v___x_1469_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1465_, v_assign_1423_, v_rhs_1467_);
v___x_1470_ = lean_nat_shiftr(v___x_1468_, v___x_1469_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
return v___x_1470_;
}
default: 
{
lean_object* v_n_1471_; lean_object* v_lhs_1472_; lean_object* v_rhs_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_n_1471_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_n_1471_);
v_lhs_1472_ = lean_ctor_get(v_x_1424_, 2);
lean_inc_ref(v_lhs_1472_);
v_rhs_1473_ = lean_ctor_get(v_x_1424_, 3);
lean_inc_ref(v_rhs_1473_);
lean_dec_ref_known(v_x_1424_, 4);
lean_inc(v_w_1422_);
v___x_1474_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1422_, v_assign_1423_, v_lhs_1472_);
v___x_1475_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1471_, v_assign_1423_, v_rhs_1473_);
v___x_1476_ = l_BitVec_sshiftRight(v_w_1422_, v___x_1474_, v___x_1475_);
lean_dec(v___x_1475_);
lean_dec(v_w_1422_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1477_, lean_object* v_assign_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1477_, v_assign_1478_, v_x_1479_);
lean_dec_ref(v_assign_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* v_w_1481_, lean_object* v_x_1482_, lean_object* v_h__1_1483_, lean_object* v_h__2_1484_, lean_object* v_h__3_1485_, lean_object* v_h__4_1486_, lean_object* v_h__5_1487_, lean_object* v_h__6_1488_, lean_object* v_h__7_1489_, lean_object* v_h__8_1490_, lean_object* v_h__9_1491_, lean_object* v_h__10_1492_){
_start:
{
switch(lean_obj_tag(v_x_1482_))
{
case 0:
{
lean_object* v_idx_1493_; lean_object* v___x_1494_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
v_idx_1493_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_idx_1493_);
lean_dec_ref_known(v_x_1482_, 2);
v___x_1494_ = lean_apply_2(v_h__1_1483_, v_w_1481_, v_idx_1493_);
return v___x_1494_;
}
case 1:
{
lean_object* v_val_1495_; lean_object* v___x_1496_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__1_1483_);
v_val_1495_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_x_1482_, 2);
v___x_1496_ = lean_apply_2(v_h__2_1484_, v_w_1481_, v_val_1495_);
return v___x_1496_;
}
case 2:
{
lean_object* v_w_1497_; lean_object* v_start_1498_; lean_object* v_expr_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_w_1497_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_w_1497_);
v_start_1498_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_start_1498_);
v_expr_1499_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_expr_1499_);
lean_dec_ref_known(v_x_1482_, 4);
v___x_1500_ = lean_apply_4(v_h__3_1485_, v_w_1481_, v_w_1497_, v_start_1498_, v_expr_1499_);
return v___x_1500_;
}
case 3:
{
lean_object* v_lhs_1501_; uint8_t v_op_1502_; lean_object* v_rhs_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_lhs_1501_ = lean_ctor_get(v_x_1482_, 1);
lean_inc_ref(v_lhs_1501_);
v_op_1502_ = lean_ctor_get_uint8(v_x_1482_, sizeof(void*)*3 + 8);
v_rhs_1503_ = lean_ctor_get(v_x_1482_, 2);
lean_inc_ref(v_rhs_1503_);
lean_dec_ref_known(v_x_1482_, 3);
v___x_1504_ = lean_box(v_op_1502_);
v___x_1505_ = lean_apply_4(v_h__4_1486_, v_w_1481_, v_lhs_1501_, v___x_1504_, v_rhs_1503_);
return v___x_1505_;
}
case 4:
{
lean_object* v_op_1506_; lean_object* v_operand_1507_; lean_object* v___x_1508_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_op_1506_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_op_1506_);
v_operand_1507_ = lean_ctor_get(v_x_1482_, 2);
lean_inc_ref(v_operand_1507_);
lean_dec_ref_known(v_x_1482_, 3);
v___x_1508_ = lean_apply_3(v_h__5_1487_, v_w_1481_, v_op_1506_, v_operand_1507_);
return v___x_1508_;
}
case 5:
{
lean_object* v_l_1509_; lean_object* v_r_1510_; lean_object* v_lhs_1511_; lean_object* v_rhs_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_l_1509_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_l_1509_);
v_r_1510_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_r_1510_);
v_lhs_1511_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_lhs_1511_);
v_rhs_1512_ = lean_ctor_get(v_x_1482_, 4);
lean_inc_ref(v_rhs_1512_);
lean_dec_ref_known(v_x_1482_, 5);
v___x_1513_ = lean_apply_6(v_h__6_1488_, v_w_1481_, v_l_1509_, v_r_1510_, v_lhs_1511_, v_rhs_1512_, lean_box(0));
return v___x_1513_;
}
case 6:
{
lean_object* v_w_1514_; lean_object* v_n_1515_; lean_object* v_expr_1516_; lean_object* v___x_1517_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_w_1514_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_w_1514_);
v_n_1515_ = lean_ctor_get(v_x_1482_, 2);
lean_inc(v_n_1515_);
v_expr_1516_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_expr_1516_);
lean_dec_ref_known(v_x_1482_, 4);
v___x_1517_ = lean_apply_5(v_h__7_1489_, v_w_1481_, v_w_1514_, v_n_1515_, v_expr_1516_, lean_box(0));
return v___x_1517_;
}
case 7:
{
lean_object* v_n_1518_; lean_object* v_lhs_1519_; lean_object* v_rhs_1520_; lean_object* v___x_1521_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__9_1491_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_n_1518_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_n_1518_);
v_lhs_1519_ = lean_ctor_get(v_x_1482_, 2);
lean_inc_ref(v_lhs_1519_);
v_rhs_1520_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_rhs_1520_);
lean_dec_ref_known(v_x_1482_, 4);
v___x_1521_ = lean_apply_4(v_h__8_1490_, v_w_1481_, v_n_1518_, v_lhs_1519_, v_rhs_1520_);
return v___x_1521_;
}
case 8:
{
lean_object* v_n_1522_; lean_object* v_lhs_1523_; lean_object* v_rhs_1524_; lean_object* v___x_1525_; 
lean_dec(v_h__10_1492_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_n_1522_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_n_1522_);
v_lhs_1523_ = lean_ctor_get(v_x_1482_, 2);
lean_inc_ref(v_lhs_1523_);
v_rhs_1524_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_rhs_1524_);
lean_dec_ref_known(v_x_1482_, 4);
v___x_1525_ = lean_apply_4(v_h__9_1491_, v_w_1481_, v_n_1522_, v_lhs_1523_, v_rhs_1524_);
return v___x_1525_;
}
default: 
{
lean_object* v_n_1526_; lean_object* v_lhs_1527_; lean_object* v_rhs_1528_; lean_object* v___x_1529_; 
lean_dec(v_h__9_1491_);
lean_dec(v_h__8_1490_);
lean_dec(v_h__7_1489_);
lean_dec(v_h__6_1488_);
lean_dec(v_h__5_1487_);
lean_dec(v_h__4_1486_);
lean_dec(v_h__3_1485_);
lean_dec(v_h__2_1484_);
lean_dec(v_h__1_1483_);
v_n_1526_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_n_1526_);
v_lhs_1527_ = lean_ctor_get(v_x_1482_, 2);
lean_inc_ref(v_lhs_1527_);
v_rhs_1528_ = lean_ctor_get(v_x_1482_, 3);
lean_inc_ref(v_rhs_1528_);
lean_dec_ref_known(v_x_1482_, 4);
v___x_1529_ = lean_apply_4(v_h__10_1492_, v_w_1481_, v_n_1526_, v_lhs_1527_, v_rhs_1528_);
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* v_motive_1530_, lean_object* v_w_1531_, lean_object* v_x_1532_, lean_object* v_h__1_1533_, lean_object* v_h__2_1534_, lean_object* v_h__3_1535_, lean_object* v_h__4_1536_, lean_object* v_h__5_1537_, lean_object* v_h__6_1538_, lean_object* v_h__7_1539_, lean_object* v_h__8_1540_, lean_object* v_h__9_1541_, lean_object* v_h__10_1542_){
_start:
{
switch(lean_obj_tag(v_x_1532_))
{
case 0:
{
lean_object* v_idx_1543_; lean_object* v___x_1544_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
v_idx_1543_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_idx_1543_);
lean_dec_ref_known(v_x_1532_, 2);
v___x_1544_ = lean_apply_2(v_h__1_1533_, v_w_1531_, v_idx_1543_);
return v___x_1544_;
}
case 1:
{
lean_object* v_val_1545_; lean_object* v___x_1546_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__1_1533_);
v_val_1545_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_val_1545_);
lean_dec_ref_known(v_x_1532_, 2);
v___x_1546_ = lean_apply_2(v_h__2_1534_, v_w_1531_, v_val_1545_);
return v___x_1546_;
}
case 2:
{
lean_object* v_w_1547_; lean_object* v_start_1548_; lean_object* v_expr_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_w_1547_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_w_1547_);
v_start_1548_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_start_1548_);
v_expr_1549_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_expr_1549_);
lean_dec_ref_known(v_x_1532_, 4);
v___x_1550_ = lean_apply_4(v_h__3_1535_, v_w_1531_, v_w_1547_, v_start_1548_, v_expr_1549_);
return v___x_1550_;
}
case 3:
{
lean_object* v_lhs_1551_; uint8_t v_op_1552_; lean_object* v_rhs_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_lhs_1551_ = lean_ctor_get(v_x_1532_, 1);
lean_inc_ref(v_lhs_1551_);
v_op_1552_ = lean_ctor_get_uint8(v_x_1532_, sizeof(void*)*3 + 8);
v_rhs_1553_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_rhs_1553_);
lean_dec_ref_known(v_x_1532_, 3);
v___x_1554_ = lean_box(v_op_1552_);
v___x_1555_ = lean_apply_4(v_h__4_1536_, v_w_1531_, v_lhs_1551_, v___x_1554_, v_rhs_1553_);
return v___x_1555_;
}
case 4:
{
lean_object* v_op_1556_; lean_object* v_operand_1557_; lean_object* v___x_1558_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_op_1556_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_op_1556_);
v_operand_1557_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_operand_1557_);
lean_dec_ref_known(v_x_1532_, 3);
v___x_1558_ = lean_apply_3(v_h__5_1537_, v_w_1531_, v_op_1556_, v_operand_1557_);
return v___x_1558_;
}
case 5:
{
lean_object* v_l_1559_; lean_object* v_r_1560_; lean_object* v_lhs_1561_; lean_object* v_rhs_1562_; lean_object* v___x_1563_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_l_1559_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_l_1559_);
v_r_1560_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_r_1560_);
v_lhs_1561_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_lhs_1561_);
v_rhs_1562_ = lean_ctor_get(v_x_1532_, 4);
lean_inc_ref(v_rhs_1562_);
lean_dec_ref_known(v_x_1532_, 5);
v___x_1563_ = lean_apply_6(v_h__6_1538_, v_w_1531_, v_l_1559_, v_r_1560_, v_lhs_1561_, v_rhs_1562_, lean_box(0));
return v___x_1563_;
}
case 6:
{
lean_object* v_w_1564_; lean_object* v_n_1565_; lean_object* v_expr_1566_; lean_object* v___x_1567_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_w_1564_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_w_1564_);
v_n_1565_ = lean_ctor_get(v_x_1532_, 2);
lean_inc(v_n_1565_);
v_expr_1566_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_expr_1566_);
lean_dec_ref_known(v_x_1532_, 4);
v___x_1567_ = lean_apply_5(v_h__7_1539_, v_w_1531_, v_w_1564_, v_n_1565_, v_expr_1566_, lean_box(0));
return v___x_1567_;
}
case 7:
{
lean_object* v_n_1568_; lean_object* v_lhs_1569_; lean_object* v_rhs_1570_; lean_object* v___x_1571_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__9_1541_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_n_1568_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_n_1568_);
v_lhs_1569_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_lhs_1569_);
v_rhs_1570_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_rhs_1570_);
lean_dec_ref_known(v_x_1532_, 4);
v___x_1571_ = lean_apply_4(v_h__8_1540_, v_w_1531_, v_n_1568_, v_lhs_1569_, v_rhs_1570_);
return v___x_1571_;
}
case 8:
{
lean_object* v_n_1572_; lean_object* v_lhs_1573_; lean_object* v_rhs_1574_; lean_object* v___x_1575_; 
lean_dec(v_h__10_1542_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_n_1572_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_n_1572_);
v_lhs_1573_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_lhs_1573_);
v_rhs_1574_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_rhs_1574_);
lean_dec_ref_known(v_x_1532_, 4);
v___x_1575_ = lean_apply_4(v_h__9_1541_, v_w_1531_, v_n_1572_, v_lhs_1573_, v_rhs_1574_);
return v___x_1575_;
}
default: 
{
lean_object* v_n_1576_; lean_object* v_lhs_1577_; lean_object* v_rhs_1578_; lean_object* v___x_1579_; 
lean_dec(v_h__9_1541_);
lean_dec(v_h__8_1540_);
lean_dec(v_h__7_1539_);
lean_dec(v_h__6_1538_);
lean_dec(v_h__5_1537_);
lean_dec(v_h__4_1536_);
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
lean_dec(v_h__1_1533_);
v_n_1576_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_n_1576_);
v_lhs_1577_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_lhs_1577_);
v_rhs_1578_ = lean_ctor_get(v_x_1532_, 3);
lean_inc_ref(v_rhs_1578_);
lean_dec_ref_known(v_x_1532_, 4);
v___x_1579_ = lean_apply_4(v_h__10_1542_, v_w_1531_, v_n_1576_, v_lhs_1577_, v_rhs_1578_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(uint8_t v_x_1580_){
_start:
{
if (v_x_1580_ == 0)
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(0u);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(1u);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(lean_object* v_x_1583_){
_start:
{
uint8_t v_x_boxed_1584_; lean_object* v_res_1585_; 
v_x_boxed_1584_ = lean_unbox(v_x_1583_);
v_res_1585_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_boxed_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1586_){
_start:
{
lean_inc(v_k_1586_);
return v_k_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1587_);
lean_dec(v_k_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1589_, lean_object* v_ctorIdx_1590_, uint8_t v_t_1591_, lean_object* v_h_1592_, lean_object* v_k_1593_){
_start:
{
lean_inc(v_k_1593_);
return v_k_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1594_, lean_object* v_ctorIdx_1595_, lean_object* v_t_1596_, lean_object* v_h_1597_, lean_object* v_k_1598_){
_start:
{
uint8_t v_t_boxed_1599_; lean_object* v_res_1600_; 
v_t_boxed_1599_ = lean_unbox(v_t_1596_);
v_res_1600_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1594_, v_ctorIdx_1595_, v_t_boxed_1599_, v_h_1597_, v_k_1598_);
lean_dec(v_k_1598_);
lean_dec(v_ctorIdx_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1601_){
_start:
{
lean_inc(v_eq_1601_);
return v_eq_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1602_);
lean_dec(v_eq_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1604_, uint8_t v_t_1605_, lean_object* v_h_1606_, lean_object* v_eq_1607_){
_start:
{
lean_inc(v_eq_1607_);
return v_eq_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1608_, lean_object* v_t_1609_, lean_object* v_h_1610_, lean_object* v_eq_1611_){
_start:
{
uint8_t v_t_boxed_1612_; lean_object* v_res_1613_; 
v_t_boxed_1612_ = lean_unbox(v_t_1609_);
v_res_1613_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1608_, v_t_boxed_1612_, v_h_1610_, v_eq_1611_);
lean_dec(v_eq_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1614_){
_start:
{
lean_inc(v_ult_1614_);
return v_ult_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1615_);
lean_dec(v_ult_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1617_, uint8_t v_t_1618_, lean_object* v_h_1619_, lean_object* v_ult_1620_){
_start:
{
lean_inc(v_ult_1620_);
return v_ult_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_ult_1624_){
_start:
{
uint8_t v_t_boxed_1625_; lean_object* v_res_1626_; 
v_t_boxed_1625_ = lean_unbox(v_t_1622_);
v_res_1626_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1621_, v_t_boxed_1625_, v_h_1623_, v_ult_1624_);
lean_dec(v_ult_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1629_){
_start:
{
if (v_x_1629_ == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1632_){
_start:
{
uint8_t v_x_22__boxed_1633_; lean_object* v_res_1634_; 
v_x_22__boxed_1633_ = lean_unbox(v_x_1632_);
v_res_1634_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1633_);
return v_res_1634_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
if (v_x_1637_ == 0)
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_eq(v_a_1638_, v_a_1639_);
return v___x_1640_;
}
else
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_lt(v_a_1638_, v_a_1639_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
uint8_t v_x_101__boxed_1645_; uint8_t v_res_1646_; lean_object* v_r_1647_; 
v_x_101__boxed_1645_ = lean_unbox(v_x_1642_);
v_res_1646_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_101__boxed_1645_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec(v_a_1643_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1648_, uint8_t v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1649_, v_a_1650_, v_a_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1653_, lean_object* v_x_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
uint8_t v_x_114__boxed_1657_; uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_x_114__boxed_1657_ = lean_unbox(v_x_1654_);
v_res_1658_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1653_, v_x_114__boxed_1657_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec(v_w_1653_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx(lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_unsigned_to_nat(1u);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(lean_object* v_x_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx(v_x_1663_);
lean_dec_ref(v_x_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1665_, lean_object* v_k_1666_){
_start:
{
if (lean_obj_tag(v_t_1665_) == 0)
{
lean_object* v_w_1667_; lean_object* v_lhs_1668_; uint8_t v_op_1669_; lean_object* v_rhs_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_w_1667_ = lean_ctor_get(v_t_1665_, 0);
lean_inc(v_w_1667_);
v_lhs_1668_ = lean_ctor_get(v_t_1665_, 1);
lean_inc_ref(v_lhs_1668_);
v_op_1669_ = lean_ctor_get_uint8(v_t_1665_, sizeof(void*)*3);
v_rhs_1670_ = lean_ctor_get(v_t_1665_, 2);
lean_inc_ref(v_rhs_1670_);
lean_dec_ref_known(v_t_1665_, 3);
v___x_1671_ = lean_box(v_op_1669_);
v___x_1672_ = lean_apply_4(v_k_1666_, v_w_1667_, v_lhs_1668_, v___x_1671_, v_rhs_1670_);
return v___x_1672_;
}
else
{
lean_object* v_w_1673_; lean_object* v_expr_1674_; lean_object* v_idx_1675_; lean_object* v___x_1676_; 
v_w_1673_ = lean_ctor_get(v_t_1665_, 0);
lean_inc(v_w_1673_);
v_expr_1674_ = lean_ctor_get(v_t_1665_, 1);
lean_inc_ref(v_expr_1674_);
v_idx_1675_ = lean_ctor_get(v_t_1665_, 2);
lean_inc(v_idx_1675_);
lean_dec_ref_known(v_t_1665_, 3);
v___x_1676_ = lean_apply_3(v_k_1666_, v_w_1673_, v_expr_1674_, v_idx_1675_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1677_, lean_object* v_ctorIdx_1678_, lean_object* v_t_1679_, lean_object* v_h_1680_, lean_object* v_k_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1679_, v_k_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1683_, lean_object* v_ctorIdx_1684_, lean_object* v_t_1685_, lean_object* v_h_1686_, lean_object* v_k_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1683_, v_ctorIdx_1684_, v_t_1685_, v_h_1686_, v_k_1687_);
lean_dec(v_ctorIdx_1684_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1689_, lean_object* v_bin_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1689_, v_bin_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1692_, lean_object* v_t_1693_, lean_object* v_h_1694_, lean_object* v_bin_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1693_, v_bin_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1697_, lean_object* v_getLsbD_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1697_, v_getLsbD_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1700_, lean_object* v_t_1701_, lean_object* v_h_1702_, lean_object* v_getLsbD_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1701_, v_getLsbD_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_w_1706_; lean_object* v_lhs_1707_; uint8_t v_op_1708_; lean_object* v_rhs_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_w_1706_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_n(v_w_1706_, 2);
v_lhs_1707_ = lean_ctor_get(v_x_1705_, 1);
lean_inc_ref(v_lhs_1707_);
v_op_1708_ = lean_ctor_get_uint8(v_x_1705_, sizeof(void*)*3);
v_rhs_1709_ = lean_ctor_get(v_x_1705_, 2);
lean_inc_ref(v_rhs_1709_);
lean_dec_ref_known(v_x_1705_, 3);
v___x_1710_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1711_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1706_, v_lhs_1707_);
v___x_1712_ = lean_string_append(v___x_1710_, v___x_1711_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
v___x_1715_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1708_);
v___x_1716_ = lean_string_append(v___x_1714_, v___x_1715_);
lean_dec_ref(v___x_1715_);
v___x_1717_ = lean_string_append(v___x_1716_, v___x_1713_);
v___x_1718_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1706_, v_rhs_1709_);
v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
return v___x_1721_;
}
else
{
lean_object* v_w_1722_; lean_object* v_expr_1723_; lean_object* v_idx_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_w_1722_ = lean_ctor_get(v_x_1705_, 0);
lean_inc(v_w_1722_);
v_expr_1723_ = lean_ctor_get(v_x_1705_, 1);
lean_inc_ref(v_expr_1723_);
v_idx_1724_ = lean_ctor_get(v_x_1705_, 2);
lean_inc(v_idx_1724_);
lean_dec_ref_known(v_x_1705_, 3);
v___x_1725_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1722_, v_expr_1723_);
v___x_1726_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
v___x_1728_ = l_Nat_reprFast(v_idx_1724_);
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_object* v_w_1736_; lean_object* v_lhs_1737_; uint8_t v_op_1738_; lean_object* v_rhs_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_w_1736_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_n(v_w_1736_, 2);
v_lhs_1737_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_lhs_1737_);
v_op_1738_ = lean_ctor_get_uint8(v_x_1735_, sizeof(void*)*3);
v_rhs_1739_ = lean_ctor_get(v_x_1735_, 2);
lean_inc_ref(v_rhs_1739_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1740_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1736_, v_assign_1734_, v_lhs_1737_);
v___x_1741_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1736_, v_assign_1734_, v_rhs_1739_);
v___x_1742_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1738_, v___x_1740_, v___x_1741_);
lean_dec(v___x_1741_);
lean_dec(v___x_1740_);
return v___x_1742_;
}
else
{
lean_object* v_w_1743_; lean_object* v_expr_1744_; lean_object* v_idx_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_w_1743_ = lean_ctor_get(v_x_1735_, 0);
lean_inc(v_w_1743_);
v_expr_1744_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_expr_1744_);
v_idx_1745_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_idx_1745_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1746_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1743_, v_assign_1734_, v_expr_1744_);
v___x_1747_ = l_Nat_testBit(v___x_1746_, v_idx_1745_);
lean_dec(v_idx_1745_);
lean_dec(v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1748_, lean_object* v_x_1749_){
_start:
{
uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_res_1750_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1748_, v_x_1749_);
lean_dec_ref(v_assign_1748_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1752_, lean_object* v_x_1753_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1752_, v_x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1755_, lean_object* v_x_1756_){
_start:
{
uint8_t v_res_1757_; lean_object* v_r_1758_; 
v_res_1757_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1755_, v_x_1756_);
lean_dec_ref(v_assign_1755_);
v_r_1758_ = lean_box(v_res_1757_);
return v_r_1758_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1759_, lean_object* v_expr_1760_){
_start:
{
lean_object* v___f_1761_; uint8_t v___x_1762_; 
v___f_1761_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1761_, 0, v_assign_1759_);
v___x_1762_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1761_, v_expr_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1763_, lean_object* v_expr_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1763_, v_expr_1764_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
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
