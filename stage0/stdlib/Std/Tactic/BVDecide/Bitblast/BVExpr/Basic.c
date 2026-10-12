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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t l_BitVec_hash(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instInhabitedPackedBitVec_default___closed__0_value;
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinPred___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinPred_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVBinPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBinPred_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVBinPred___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBinPred___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVBinPred = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVBinPred___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVPred_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVPred_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_instHashableBVPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVPred_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_instHashableBVPred___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVPred___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_instHashableBVPred = (const lean_object*)&l_Std_Tactic_BVDecide_instHashableBVPred___closed__0_value;
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
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBVBit_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_12_;
v_res_12_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_x_1_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object* v_x_13_){
_start:
{
uint64_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_x_13_);
lean_dec_ref(v_x_13_);
v_r_15_ = lean_box_uint64(v_res_14_);
return v_r_15_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_var_20_; lean_object* v_w_21_; lean_object* v_idx_22_; lean_object* v_var_23_; lean_object* v_w_24_; lean_object* v_idx_25_; uint8_t v___x_26_; 
v_var_20_ = lean_ctor_get(v_x_18_, 0);
v_w_21_ = lean_ctor_get(v_x_18_, 1);
v_idx_22_ = lean_ctor_get(v_x_18_, 2);
v_var_23_ = lean_ctor_get(v_x_19_, 0);
v_w_24_ = lean_ctor_get(v_x_19_, 1);
v_idx_25_ = lean_ctor_get(v_x_19_, 2);
v___x_26_ = lean_nat_dec_eq(v_var_20_, v_var_23_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_w_21_, v_w_24_);
if (v___x_27_ == 0)
{
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_eq(v_idx_22_, v_idx_25_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_18_ = stack[0].m_obj;
lean_object* v_x_19_ = stack[1].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_18_, v_x_19_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_34_, v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVBit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_34_ = stack[0].m_obj;
lean_object* v_x_35_ = stack[1].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit(v_x_34_, v_x_35_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit(v_x_38_, v_x_39_);
lean_dec_ref(v_x_39_);
lean_dec_ref(v_x_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_instReprBVBit_repr_spec__0(lean_object* v_a_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_nat_to_int(v_a_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(7u);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(5u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0));
v___x_72_ = lean_string_length(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(lean_object* v_x_79_){
_start:
{
lean_object* v_var_80_; lean_object* v_w_81_; lean_object* v_idx_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_var_80_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_var_80_);
v_w_81_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_w_81_);
v_idx_82_ = lean_ctor_get(v_x_79_, 2);
lean_inc(v_idx_82_);
lean_dec_ref(v_x_79_);
v___x_83_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5));
v___x_84_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6));
v___x_85_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7);
v___x_86_ = l_Nat_reprFast(v_var_80_);
v___x_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_85_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_84_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_box(1);
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11));
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_83_);
v___x_99_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12);
v___x_100_ = l_Nat_reprFast(v_w_81_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_99_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_89_);
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_98_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_92_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_94_);
v___x_107_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14));
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_83_);
v___x_110_ = l_Nat_reprFast(v_idx_82_);
v___x_111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_85_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_89_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_109_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_obj_once(&l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17, &l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17_once, _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17);
v___x_116_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18));
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_114_);
v___x_118_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19));
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_115_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_89_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr(lean_object* v_x_122_, lean_object* v_prec_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(v_x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed(lean_object* v_x_125_, lean_object* v_prec_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Tactic_BVDecide_instReprBVBit_repr(v_x_125_, v_prec_126_);
lean_dec(v_prec_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object* v_b_133_){
_start:
{
lean_object* v_var_134_; lean_object* v_idx_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_var_134_ = lean_ctor_get(v_b_133_, 0);
lean_inc(v_var_134_);
v_idx_135_ = lean_ctor_get(v_b_133_, 2);
lean_inc(v_idx_135_);
lean_dec_ref(v_b_133_);
v___x_136_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0));
v___x_137_ = l_Nat_reprFast(v_var_134_);
v___x_138_ = lean_string_append(v___x_136_, v___x_137_);
lean_dec_ref(v___x_137_);
v___x_139_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = l_Nat_reprFast(v_idx_135_);
v___x_142_ = lean_string_append(v___x_140_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_144_ = lean_string_append(v___x_142_, v___x_143_);
return v___x_144_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(uint8_t v_x_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(v_x_151_);
v___x_153_ = lean_obj_tag_nat(v___x_152_);
lean_dec(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_151_ = stack[0].m_num;
lean_object* v_res_154_;
v_res_154_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(v_x_151_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl___boxed(lean_object* v_x_155_){
_start:
{
uint8_t v_x_4__boxed_156_; lean_object* v_res_157_; 
v_x_4__boxed_156_ = lean_unbox(v_x_155_);
v_res_157_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(v_x_4__boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* v_k_158_){
_start:
{
lean_inc(v_k_158_);
return v_k_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* v_k_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_159_);
lean_dec(v_k_159_);
return v_res_160_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* v_motive_161_, lean_object* v_ctorIdx_162_, uint8_t v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_inc(v_k_165_);
return v_k_165_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_162_ = stack[1].m_obj;
uint8_t v_t_163_ = stack[2].m_num;
lean_object* v_k_165_ = stack[4].m_obj;
lean_object* v_res_166_;
v_res_166_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_box(0), v_ctorIdx_162_, v_t_163_, lean_box(0), v_k_165_);
stack->m_obj
 = v_res_166_;
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
lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* v_motive_177_, uint8_t v_t_178_, lean_object* v_h_179_, lean_object* v_and_180_){
_start:
{
lean_inc(v_and_180_);
return v_and_180_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_and_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_178_ = stack[1].m_num;
lean_object* v_and_180_ = stack[3].m_obj;
lean_object* v_res_181_;
v_res_181_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_box(0), v_t_178_, lean_box(0), v_and_180_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_and_185_){
_start:
{
uint8_t v_t_boxed_186_; lean_object* v_res_187_; 
v_t_boxed_186_ = lean_unbox(v_t_183_);
v_res_187_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(v_motive_182_, v_t_boxed_186_, v_h_184_, v_and_185_);
lean_dec(v_and_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* v_or_188_){
_start:
{
lean_inc(v_or_188_);
return v_or_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* v_or_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_189_);
lean_dec(v_or_189_);
return v_res_190_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* v_motive_191_, uint8_t v_t_192_, lean_object* v_h_193_, lean_object* v_or_194_){
_start:
{
lean_inc(v_or_194_);
return v_or_194_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_or_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_192_ = stack[1].m_num;
lean_object* v_or_194_ = stack[3].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_box(0), v_t_192_, lean_box(0), v_or_194_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_or_199_){
_start:
{
uint8_t v_t_boxed_200_; lean_object* v_res_201_; 
v_t_boxed_200_ = lean_unbox(v_t_197_);
v_res_201_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(v_motive_196_, v_t_boxed_200_, v_h_198_, v_or_199_);
lean_dec(v_or_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* v_xor_202_){
_start:
{
lean_inc(v_xor_202_);
return v_xor_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* v_xor_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_203_);
lean_dec(v_xor_203_);
return v_res_204_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* v_motive_205_, uint8_t v_t_206_, lean_object* v_h_207_, lean_object* v_xor_208_){
_start:
{
lean_inc(v_xor_208_);
return v_xor_208_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_xor_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_206_ = stack[1].m_num;
lean_object* v_xor_208_ = stack[3].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_box(0), v_t_206_, lean_box(0), v_xor_208_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_xor_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_xor_213_);
lean_dec(v_xor_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* v_add_216_){
_start:
{
lean_inc(v_add_216_);
return v_add_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* v_add_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_217_);
lean_dec(v_add_217_);
return v_res_218_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_add_222_){
_start:
{
lean_inc(v_add_222_);
return v_add_222_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_add_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_220_ = stack[1].m_num;
lean_object* v_add_222_ = stack[3].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_box(0), v_t_220_, lean_box(0), v_add_222_);
stack->m_obj
 = v_res_223_;
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
lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_mul_236_){
_start:
{
lean_inc(v_mul_236_);
return v_mul_236_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_mul_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_234_ = stack[1].m_num;
lean_object* v_mul_236_ = stack[3].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_box(0), v_t_234_, lean_box(0), v_mul_236_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_mul_241_){
_start:
{
uint8_t v_t_boxed_242_; lean_object* v_res_243_; 
v_t_boxed_242_ = lean_unbox(v_t_239_);
v_res_243_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(v_motive_238_, v_t_boxed_242_, v_h_240_, v_mul_241_);
lean_dec(v_mul_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* v_udiv_244_){
_start:
{
lean_inc(v_udiv_244_);
return v_udiv_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* v_udiv_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_245_);
lean_dec(v_udiv_245_);
return v_res_246_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_udiv_250_){
_start:
{
lean_inc(v_udiv_250_);
return v_udiv_250_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_udiv_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_248_ = stack[1].m_num;
lean_object* v_udiv_250_ = stack[3].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_box(0), v_t_248_, lean_box(0), v_udiv_250_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_udiv_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_udiv_255_);
lean_dec(v_udiv_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* v_umod_258_){
_start:
{
lean_inc(v_umod_258_);
return v_umod_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* v_umod_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_259_);
lean_dec(v_umod_259_);
return v_res_260_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_umod_264_){
_start:
{
lean_inc(v_umod_264_);
return v_umod_264_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_umod_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_262_ = stack[1].m_num;
lean_object* v_umod_264_ = stack[3].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_box(0), v_t_262_, lean_box(0), v_umod_264_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_umod_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_umod_269_);
lean_dec(v_umod_269_);
return v_res_271_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t v_x_272_){
_start:
{
switch(v_x_272_)
{
case 0:
{
uint64_t v___x_273_; 
v___x_273_ = 0ULL;
return v___x_273_;
}
case 1:
{
uint64_t v___x_274_; 
v___x_274_ = 1ULL;
return v___x_274_;
}
case 2:
{
uint64_t v___x_275_; 
v___x_275_ = 2ULL;
return v___x_275_;
}
case 3:
{
uint64_t v___x_276_; 
v___x_276_ = 3ULL;
return v___x_276_;
}
case 4:
{
uint64_t v___x_277_; 
v___x_277_ = 4ULL;
return v___x_277_;
}
case 5:
{
uint64_t v___x_278_; 
v___x_278_ = 5ULL;
return v___x_278_;
}
default: 
{
uint64_t v___x_279_; 
v___x_279_ = 6ULL;
return v___x_279_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBVBinOp_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_272_ = stack[0].m_num;
uint64_t v_res_280_;
v_res_280_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_272_);
stack->m_num = v_res_280_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* v_x_281_){
_start:
{
uint8_t v_x_88__boxed_282_; uint64_t v_res_283_; lean_object* v_r_284_; 
v_x_88__boxed_282_ = lean_unbox(v_x_281_);
v_res_283_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_282_);
v_r_284_ = lean_box_uint64(v_res_283_);
return v_r_284_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* v_n_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(2u);
v___x_289_ = lean_nat_dec_le(v_n_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_dec_le(v_n_287_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(5u);
v___x_293_ = lean_nat_dec_le(v_n_287_, v___x_292_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 6;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 5;
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(3u);
v___x_297_ = lean_nat_dec_le(v_n_287_, v___x_296_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = 4;
return v___x_298_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = 3;
return v___x_299_;
}
}
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_le(v_n_287_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_dec_le(v_n_287_, v___x_302_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 2;
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 1;
return v___x_305_;
}
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_287_ = stack[0].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_287_);
stack->m_num = v_res_307_;
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
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t v_x_311_, uint8_t v_y_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_313_ = lean_box(v_x_311_);
v___x_314_ = lean_obj_tag_nat(v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = lean_box(v_y_312_);
v___x_316_ = lean_obj_tag_nat(v___x_315_);
lean_dec(v___x_315_);
v___x_317_ = lean_nat_dec_eq(v___x_314_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVBinOp_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_311_ = stack[0].m_num;
uint8_t v_y_312_ = stack[1].m_num;
uint8_t v_res_318_;
v_res_318_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_311_, v_y_312_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* v_x_319_, lean_object* v_y_320_){
_start:
{
uint8_t v_x_23__boxed_321_; uint8_t v_y_24__boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_x_23__boxed_321_ = lean_unbox(v_x_319_);
v_y_24__boxed_322_ = lean_unbox(v_y_320_);
v_res_323_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_23__boxed_321_, v_y_24__boxed_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t v_x_332_){
_start:
{
switch(v_x_332_)
{
case 0:
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return v___x_333_;
}
case 1:
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return v___x_334_;
}
case 2:
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return v___x_335_;
}
case 3:
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return v___x_336_;
}
case 4:
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return v___x_337_;
}
case 5:
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return v___x_338_;
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return v___x_339_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_332_ = stack[0].m_num;
lean_object* v_res_340_;
v_res_340_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_332_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* v_x_341_){
_start:
{
uint8_t v_x_67__boxed_342_; lean_object* v_res_343_; 
v_x_67__boxed_342_ = lean_unbox(v_x_341_);
v_res_343_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_342_);
return v_res_343_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* v_w_346_, uint8_t v_x_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
switch(v_x_347_)
{
case 0:
{
lean_object* v___x_350_; 
v___x_350_ = lean_nat_land(v_a_348_, v_a_349_);
return v___x_350_;
}
case 1:
{
lean_object* v___x_351_; 
v___x_351_ = lean_nat_lor(v_a_348_, v_a_349_);
return v___x_351_;
}
case 2:
{
lean_object* v___x_352_; 
v___x_352_ = lean_nat_lxor(v_a_348_, v_a_349_);
return v___x_352_;
}
case 3:
{
lean_object* v___x_353_; 
v___x_353_ = l_BitVec_add(v_w_346_, v_a_348_, v_a_349_);
return v___x_353_;
}
case 4:
{
lean_object* v___x_354_; 
v___x_354_ = l_BitVec_mul(v_w_346_, v_a_348_, v_a_349_);
return v___x_354_;
}
case 5:
{
lean_object* v___x_355_; 
v___x_355_ = lean_nat_div(v_a_348_, v_a_349_);
return v___x_355_;
}
default: 
{
lean_object* v___x_356_; 
v___x_356_ = lean_nat_mod(v_a_348_, v_a_349_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinOp_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_346_ = stack[0].m_obj;
uint8_t v_x_347_ = stack[1].m_num;
lean_object* v_a_348_ = stack[2].m_obj;
lean_object* v_a_349_ = stack[3].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_346_, v_x_347_, v_a_348_, v_a_349_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* v_w_358_, lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_x_259__boxed_362_; lean_object* v_res_363_; 
v_x_259__boxed_362_ = lean_unbox(v_x_359_);
v_res_363_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_358_, v_x_259__boxed_362_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_w_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl(lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_tag_nat(v_x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl___boxed(lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl(v_x_366_);
lean_dec(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* v_t_368_, lean_object* v_k_369_){
_start:
{
switch(lean_obj_tag(v_t_368_))
{
case 1:
{
lean_object* v_n_370_; lean_object* v___x_371_; 
v_n_370_ = lean_ctor_get(v_t_368_, 0);
lean_inc(v_n_370_);
lean_dec_ref_known(v_t_368_, 1);
v___x_371_ = lean_apply_1(v_k_369_, v_n_370_);
return v___x_371_;
}
case 2:
{
lean_object* v_n_372_; lean_object* v___x_373_; 
v_n_372_ = lean_ctor_get(v_t_368_, 0);
lean_inc(v_n_372_);
lean_dec_ref_known(v_t_368_, 1);
v___x_373_ = lean_apply_1(v_k_369_, v_n_372_);
return v___x_373_;
}
case 3:
{
lean_object* v_n_374_; lean_object* v___x_375_; 
v_n_374_ = lean_ctor_get(v_t_368_, 0);
lean_inc(v_n_374_);
lean_dec_ref_known(v_t_368_, 1);
v___x_375_ = lean_apply_1(v_k_369_, v_n_374_);
return v___x_375_;
}
default: 
{
lean_dec(v_t_368_);
return v_k_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* v_motive_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_378_, v_k_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(v_motive_382_, v_ctorIdx_383_, v_t_384_, v_h_385_, v_k_386_);
lean_dec(v_ctorIdx_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* v_t_388_, lean_object* v_not_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_388_, v_not_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_not_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_392_, v_not_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* v_t_396_, lean_object* v_rotateLeft_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_396_, v_rotateLeft_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_rotateLeft_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_400_, v_rotateLeft_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* v_t_404_, lean_object* v_rotateRight_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_404_, v_rotateRight_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_rotateRight_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_408_, v_rotateRight_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* v_t_412_, lean_object* v_arithShiftRightConst_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_412_, v_arithShiftRightConst_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_arithShiftRightConst_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_416_, v_arithShiftRightConst_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* v_t_420_, lean_object* v_reverse_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_420_, v_reverse_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_reverse_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_424_, v_reverse_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* v_t_428_, lean_object* v_clz_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_428_, v_clz_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_clz_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_432_, v_clz_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object* v_t_436_, lean_object* v_cpop_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_436_, v_cpop_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_cpop_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_440_, v_cpop_442_);
return v___x_443_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* v_x_444_){
_start:
{
switch(lean_obj_tag(v_x_444_))
{
case 0:
{
uint64_t v___x_445_; 
v___x_445_ = 0ULL;
return v___x_445_;
}
case 1:
{
lean_object* v_n_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; 
v_n_446_ = lean_ctor_get(v_x_444_, 0);
v___x_447_ = 1ULL;
v___x_448_ = lean_uint64_of_nat(v_n_446_);
v___x_449_ = lean_uint64_mix_hash(v___x_447_, v___x_448_);
return v___x_449_;
}
case 2:
{
lean_object* v_n_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; 
v_n_450_ = lean_ctor_get(v_x_444_, 0);
v___x_451_ = 2ULL;
v___x_452_ = lean_uint64_of_nat(v_n_450_);
v___x_453_ = lean_uint64_mix_hash(v___x_451_, v___x_452_);
return v___x_453_;
}
case 3:
{
lean_object* v_n_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; 
v_n_454_ = lean_ctor_get(v_x_444_, 0);
v___x_455_ = 3ULL;
v___x_456_ = lean_uint64_of_nat(v_n_454_);
v___x_457_ = lean_uint64_mix_hash(v___x_455_, v___x_456_);
return v___x_457_;
}
case 4:
{
uint64_t v___x_458_; 
v___x_458_ = 4ULL;
return v___x_458_;
}
case 5:
{
uint64_t v___x_459_; 
v___x_459_ = 5ULL;
return v___x_459_;
}
default: 
{
uint64_t v___x_460_; 
v___x_460_ = 6ULL;
return v___x_460_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBVUnOp_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_444_ = stack[0].m_obj;
uint64_t v_res_461_;
v_res_461_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_444_);
stack->m_num = v_res_461_;
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
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
switch(lean_obj_tag(v_x_467_))
{
case 0:
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
case 1:
{
if (lean_obj_tag(v_x_468_) == 1)
{
lean_object* v_n_471_; lean_object* v_n_472_; uint8_t v___x_473_; 
v_n_471_ = lean_ctor_get(v_x_467_, 0);
v_n_472_ = lean_ctor_get(v_x_468_, 0);
v___x_473_ = lean_nat_dec_eq(v_n_471_, v_n_472_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
}
case 2:
{
if (lean_obj_tag(v_x_468_) == 2)
{
lean_object* v_n_475_; lean_object* v_n_476_; uint8_t v___x_477_; 
v_n_475_ = lean_ctor_get(v_x_467_, 0);
v_n_476_ = lean_ctor_get(v_x_468_, 0);
v___x_477_ = lean_nat_dec_eq(v_n_475_, v_n_476_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = 0;
return v___x_478_;
}
}
case 3:
{
if (lean_obj_tag(v_x_468_) == 3)
{
lean_object* v_n_479_; lean_object* v_n_480_; uint8_t v___x_481_; 
v_n_479_ = lean_ctor_get(v_x_467_, 0);
v_n_480_ = lean_ctor_get(v_x_468_, 0);
v___x_481_ = lean_nat_dec_eq(v_n_479_, v_n_480_);
return v___x_481_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
}
case 4:
{
if (lean_obj_tag(v_x_468_) == 4)
{
uint8_t v___x_483_; 
v___x_483_ = 1;
return v___x_483_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
}
case 5:
{
if (lean_obj_tag(v_x_468_) == 5)
{
uint8_t v___x_485_; 
v___x_485_ = 1;
return v___x_485_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
}
default: 
{
if (lean_obj_tag(v_x_468_) == 6)
{
uint8_t v___x_487_; 
v___x_487_ = 1;
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_467_ = stack[0].m_obj;
lean_object* v_x_468_ = stack[1].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_467_, v_x_468_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_490_, v_x_491_);
lean_dec(v_x_491_);
lean_dec(v_x_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_494_, v_x_495_);
return v___x_496_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_494_ = stack[0].m_obj;
lean_object* v_x_495_ = stack[1].m_obj;
uint8_t v_res_497_;
v_res_497_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_494_, v_x_495_);
stack->m_num = v_res_497_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec(v_x_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_509_){
_start:
{
switch(lean_obj_tag(v_x_509_))
{
case 0:
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_510_;
}
case 1:
{
lean_object* v_n_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_n_511_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_n_511_);
lean_dec_ref_known(v_x_509_, 1);
v___x_512_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_513_ = l_Nat_reprFast(v_n_511_);
v___x_514_ = lean_string_append(v___x_512_, v___x_513_);
lean_dec_ref(v___x_513_);
return v___x_514_;
}
case 2:
{
lean_object* v_n_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_n_515_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_n_515_);
lean_dec_ref_known(v_x_509_, 1);
v___x_516_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_517_ = l_Nat_reprFast(v_n_515_);
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
lean_dec_ref(v___x_517_);
return v___x_518_;
}
case 3:
{
lean_object* v_n_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_n_519_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_n_519_);
lean_dec_ref_known(v_x_509_, 1);
v___x_520_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_521_ = l_Nat_reprFast(v_n_519_);
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
lean_dec_ref(v___x_521_);
return v___x_522_;
}
case 4:
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_523_;
}
case 5:
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_524_;
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_528_, lean_object* v_x_529_, lean_object* v_a_530_){
_start:
{
switch(lean_obj_tag(v_x_529_))
{
case 0:
{
lean_object* v___x_531_; 
v___x_531_ = l_BitVec_not(v_w_528_, v_a_530_);
lean_dec(v_a_530_);
lean_dec(v_w_528_);
return v___x_531_;
}
case 1:
{
lean_object* v_n_532_; lean_object* v___x_533_; 
v_n_532_ = lean_ctor_get(v_x_529_, 0);
v___x_533_ = l_BitVec_rotateLeft(v_w_528_, v_a_530_, v_n_532_);
lean_dec(v_a_530_);
lean_dec(v_w_528_);
return v___x_533_;
}
case 2:
{
lean_object* v_n_534_; lean_object* v___x_535_; 
v_n_534_ = lean_ctor_get(v_x_529_, 0);
v___x_535_ = l_BitVec_rotateRight(v_w_528_, v_a_530_, v_n_534_);
lean_dec(v_a_530_);
lean_dec(v_w_528_);
return v___x_535_;
}
case 3:
{
lean_object* v_n_536_; lean_object* v___x_537_; 
v_n_536_ = lean_ctor_get(v_x_529_, 0);
v___x_537_ = l_BitVec_sshiftRight(v_w_528_, v_a_530_, v_n_536_);
lean_dec(v_w_528_);
return v___x_537_;
}
case 4:
{
lean_object* v___x_538_; 
v___x_538_ = l_BitVec_reverse(v_w_528_, v_a_530_);
lean_dec(v_a_530_);
lean_dec(v_w_528_);
return v___x_538_;
}
case 5:
{
lean_object* v___x_539_; 
v___x_539_ = l_BitVec_clz(v_w_528_, v_a_530_);
lean_dec(v_a_530_);
lean_dec(v_w_528_);
return v___x_539_;
}
default: 
{
lean_object* v___x_540_; 
v___x_540_ = l_BitVec_cpop(v_w_528_, v_a_530_);
lean_dec(v_a_530_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_541_, lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_541_, v_x_542_, v_a_543_);
lean_dec(v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg(lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_tag_nat(v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg___boxed(lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg(v_x_547_);
lean_dec_ref(v_x_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl(lean_object* v_a_549_, lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_tag_nat(v_x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___boxed(lean_object* v_a_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl(v_a_552_, v_x_553_);
lean_dec_ref(v_x_553_);
lean_dec(v_a_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
switch(lean_obj_tag(v_t_555_))
{
case 0:
{
lean_object* v_w_557_; lean_object* v_idx_558_; lean_object* v___x_559_; 
v_w_557_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_557_);
v_idx_558_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_idx_558_);
lean_dec_ref_known(v_t_555_, 2);
v___x_559_ = lean_apply_2(v_k_556_, v_w_557_, v_idx_558_);
return v___x_559_;
}
case 1:
{
lean_object* v_w_560_; lean_object* v_val_561_; lean_object* v___x_562_; 
v_w_560_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_560_);
v_val_561_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_val_561_);
lean_dec_ref_known(v_t_555_, 2);
v___x_562_ = lean_apply_2(v_k_556_, v_w_560_, v_val_561_);
return v___x_562_;
}
case 2:
{
lean_object* v_w_563_; lean_object* v_start_564_; lean_object* v_len_565_; lean_object* v_expr_566_; lean_object* v___x_567_; 
v_w_563_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_563_);
v_start_564_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_start_564_);
v_len_565_ = lean_ctor_get(v_t_555_, 2);
lean_inc(v_len_565_);
v_expr_566_ = lean_ctor_get(v_t_555_, 3);
lean_inc_ref(v_expr_566_);
lean_dec_ref_known(v_t_555_, 4);
v___x_567_ = lean_apply_4(v_k_556_, v_w_563_, v_start_564_, v_len_565_, v_expr_566_);
return v___x_567_;
}
case 3:
{
lean_object* v_w_568_; lean_object* v_lhs_569_; uint8_t v_op_570_; lean_object* v_rhs_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_w_568_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_568_);
v_lhs_569_ = lean_ctor_get(v_t_555_, 1);
lean_inc_ref(v_lhs_569_);
v_op_570_ = lean_ctor_get_uint8(v_t_555_, sizeof(void*)*3);
v_rhs_571_ = lean_ctor_get(v_t_555_, 2);
lean_inc_ref(v_rhs_571_);
lean_dec_ref_known(v_t_555_, 3);
v___x_572_ = lean_box(v_op_570_);
v___x_573_ = lean_apply_4(v_k_556_, v_w_568_, v_lhs_569_, v___x_572_, v_rhs_571_);
return v___x_573_;
}
case 4:
{
lean_object* v_w_574_; lean_object* v_op_575_; lean_object* v_operand_576_; lean_object* v___x_577_; 
v_w_574_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_574_);
v_op_575_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_op_575_);
v_operand_576_ = lean_ctor_get(v_t_555_, 2);
lean_inc_ref(v_operand_576_);
lean_dec_ref_known(v_t_555_, 3);
v___x_577_ = lean_apply_3(v_k_556_, v_w_574_, v_op_575_, v_operand_576_);
return v___x_577_;
}
case 5:
{
lean_object* v_l_578_; lean_object* v_r_579_; lean_object* v_w_580_; lean_object* v_lhs_581_; lean_object* v_rhs_582_; lean_object* v___x_583_; 
v_l_578_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_l_578_);
v_r_579_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_r_579_);
v_w_580_ = lean_ctor_get(v_t_555_, 2);
lean_inc(v_w_580_);
v_lhs_581_ = lean_ctor_get(v_t_555_, 3);
lean_inc_ref(v_lhs_581_);
v_rhs_582_ = lean_ctor_get(v_t_555_, 4);
lean_inc_ref(v_rhs_582_);
lean_dec_ref_known(v_t_555_, 5);
v___x_583_ = lean_apply_6(v_k_556_, v_l_578_, v_r_579_, v_w_580_, v_lhs_581_, v_rhs_582_, lean_box(0));
return v___x_583_;
}
case 6:
{
lean_object* v_w_584_; lean_object* v_w_x27_585_; lean_object* v_n_586_; lean_object* v_expr_587_; lean_object* v___x_588_; 
v_w_584_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_w_584_);
v_w_x27_585_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_w_x27_585_);
v_n_586_ = lean_ctor_get(v_t_555_, 2);
lean_inc(v_n_586_);
v_expr_587_ = lean_ctor_get(v_t_555_, 3);
lean_inc_ref(v_expr_587_);
lean_dec_ref_known(v_t_555_, 4);
v___x_588_ = lean_apply_5(v_k_556_, v_w_584_, v_w_x27_585_, v_n_586_, v_expr_587_, lean_box(0));
return v___x_588_;
}
default: 
{
lean_object* v_m_589_; lean_object* v_n_590_; lean_object* v_lhs_591_; lean_object* v_rhs_592_; lean_object* v___x_593_; 
v_m_589_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_m_589_);
v_n_590_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_n_590_);
v_lhs_591_ = lean_ctor_get(v_t_555_, 2);
lean_inc_ref(v_lhs_591_);
v_rhs_592_ = lean_ctor_get(v_t_555_, 3);
lean_inc_ref(v_rhs_592_);
lean_dec_ref(v_t_555_);
v___x_593_ = lean_apply_4(v_k_556_, v_m_589_, v_n_590_, v_lhs_591_, v_rhs_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_594_, lean_object* v_ctorIdx_595_, lean_object* v_a_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_k_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_597_, v_k_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_601_, lean_object* v_ctorIdx_602_, lean_object* v_a_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_k_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_601_, v_ctorIdx_602_, v_a_603_, v_t_604_, v_h_605_, v_k_606_);
lean_dec(v_a_603_);
lean_dec(v_ctorIdx_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_608_, lean_object* v_var_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_608_, v_var_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_611_, lean_object* v_a_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_var_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_613_, v_var_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_617_, lean_object* v_a_618_, lean_object* v_t_619_, lean_object* v_h_620_, lean_object* v_var_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_617_, v_a_618_, v_t_619_, v_h_620_, v_var_621_);
lean_dec(v_a_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_623_, lean_object* v_const_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_623_, v_const_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_626_, lean_object* v_a_627_, lean_object* v_t_628_, lean_object* v_h_629_, lean_object* v_const_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_628_, v_const_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_632_, lean_object* v_a_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_const_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_632_, v_a_633_, v_t_634_, v_h_635_, v_const_636_);
lean_dec(v_a_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_638_, lean_object* v_extract_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_638_, v_extract_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_641_, lean_object* v_a_642_, lean_object* v_t_643_, lean_object* v_h_644_, lean_object* v_extract_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_643_, v_extract_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_647_, lean_object* v_a_648_, lean_object* v_t_649_, lean_object* v_h_650_, lean_object* v_extract_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_647_, v_a_648_, v_t_649_, v_h_650_, v_extract_651_);
lean_dec(v_a_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_653_, lean_object* v_bin_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_653_, v_bin_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_656_, lean_object* v_a_657_, lean_object* v_t_658_, lean_object* v_h_659_, lean_object* v_bin_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_658_, v_bin_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_662_, lean_object* v_a_663_, lean_object* v_t_664_, lean_object* v_h_665_, lean_object* v_bin_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_662_, v_a_663_, v_t_664_, v_h_665_, v_bin_666_);
lean_dec(v_a_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_668_, lean_object* v_un_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_668_, v_un_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_671_, lean_object* v_a_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_un_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_673_, v_un_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_677_, lean_object* v_a_678_, lean_object* v_t_679_, lean_object* v_h_680_, lean_object* v_un_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_677_, v_a_678_, v_t_679_, v_h_680_, v_un_681_);
lean_dec(v_a_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_683_, lean_object* v_append_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_683_, v_append_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_686_, lean_object* v_a_687_, lean_object* v_t_688_, lean_object* v_h_689_, lean_object* v_append_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_688_, v_append_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_692_, lean_object* v_a_693_, lean_object* v_t_694_, lean_object* v_h_695_, lean_object* v_append_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_692_, v_a_693_, v_t_694_, v_h_695_, v_append_696_);
lean_dec(v_a_693_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_698_, lean_object* v_replicate_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_698_, v_replicate_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_701_, lean_object* v_a_702_, lean_object* v_t_703_, lean_object* v_h_704_, lean_object* v_replicate_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_703_, v_replicate_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_707_, lean_object* v_a_708_, lean_object* v_t_709_, lean_object* v_h_710_, lean_object* v_replicate_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_707_, v_a_708_, v_t_709_, v_h_710_, v_replicate_711_);
lean_dec(v_a_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_713_, lean_object* v_shiftLeft_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_713_, v_shiftLeft_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_716_, lean_object* v_a_717_, lean_object* v_t_718_, lean_object* v_h_719_, lean_object* v_shiftLeft_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_718_, v_shiftLeft_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_722_, lean_object* v_a_723_, lean_object* v_t_724_, lean_object* v_h_725_, lean_object* v_shiftLeft_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_722_, v_a_723_, v_t_724_, v_h_725_, v_shiftLeft_726_);
lean_dec(v_a_723_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_728_, lean_object* v_shiftRight_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_728_, v_shiftRight_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_731_, lean_object* v_a_732_, lean_object* v_t_733_, lean_object* v_h_734_, lean_object* v_shiftRight_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_733_, v_shiftRight_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_737_, lean_object* v_a_738_, lean_object* v_t_739_, lean_object* v_h_740_, lean_object* v_shiftRight_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_737_, v_a_738_, v_t_739_, v_h_740_, v_shiftRight_741_);
lean_dec(v_a_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_743_, lean_object* v_arithShiftRight_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_743_, v_arithShiftRight_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_746_, lean_object* v_a_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_arithShiftRight_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_748_, v_arithShiftRight_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_752_, lean_object* v_a_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_arithShiftRight_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_752_, v_a_753_, v_t_754_, v_h_755_, v_arithShiftRight_756_);
lean_dec(v_a_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_758_, lean_object* v_var_759_, lean_object* v_const_760_, lean_object* v_extract_761_, lean_object* v_bin_762_, lean_object* v_un_763_, lean_object* v_append_764_, lean_object* v_replicate_765_, lean_object* v_shiftLeft_766_, lean_object* v_shiftRight_767_, lean_object* v_arithShiftRight_768_){
_start:
{
switch(lean_obj_tag(v_t_758_))
{
case 0:
{
lean_object* v_w_769_; lean_object* v_idx_770_; lean_object* v___x_771_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
v_w_769_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_769_);
v_idx_770_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_idx_770_);
lean_dec_ref_known(v_t_758_, 2);
v___x_771_ = lean_apply_2(v_var_759_, v_w_769_, v_idx_770_);
return v___x_771_;
}
case 1:
{
lean_object* v_w_772_; lean_object* v_val_773_; lean_object* v___x_774_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_var_759_);
v_w_772_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_772_);
v_val_773_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_val_773_);
lean_dec_ref_known(v_t_758_, 2);
v___x_774_ = lean_apply_2(v_const_760_, v_w_772_, v_val_773_);
return v___x_774_;
}
case 2:
{
lean_object* v_w_775_; lean_object* v_start_776_; lean_object* v_len_777_; lean_object* v_expr_778_; lean_object* v___x_779_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_w_775_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_775_);
v_start_776_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_start_776_);
v_len_777_ = lean_ctor_get(v_t_758_, 2);
lean_inc(v_len_777_);
v_expr_778_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_expr_778_);
lean_dec_ref_known(v_t_758_, 4);
v___x_779_ = lean_apply_4(v_extract_761_, v_w_775_, v_start_776_, v_len_777_, v_expr_778_);
return v___x_779_;
}
case 3:
{
lean_object* v_w_780_; lean_object* v_lhs_781_; uint8_t v_op_782_; lean_object* v_rhs_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_w_780_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_780_);
v_lhs_781_ = lean_ctor_get(v_t_758_, 1);
lean_inc_ref(v_lhs_781_);
v_op_782_ = lean_ctor_get_uint8(v_t_758_, sizeof(void*)*3 + 8);
v_rhs_783_ = lean_ctor_get(v_t_758_, 2);
lean_inc_ref(v_rhs_783_);
lean_dec_ref_known(v_t_758_, 3);
v___x_784_ = lean_box(v_op_782_);
v___x_785_ = lean_apply_4(v_bin_762_, v_w_780_, v_lhs_781_, v___x_784_, v_rhs_783_);
return v___x_785_;
}
case 4:
{
lean_object* v_w_786_; lean_object* v_op_787_; lean_object* v_operand_788_; lean_object* v___x_789_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_w_786_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_786_);
v_op_787_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_op_787_);
v_operand_788_ = lean_ctor_get(v_t_758_, 2);
lean_inc_ref(v_operand_788_);
lean_dec_ref_known(v_t_758_, 3);
v___x_789_ = lean_apply_3(v_un_763_, v_w_786_, v_op_787_, v_operand_788_);
return v___x_789_;
}
case 5:
{
lean_object* v_l_790_; lean_object* v_r_791_; lean_object* v_w_792_; lean_object* v_lhs_793_; lean_object* v_rhs_794_; lean_object* v___x_795_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_l_790_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_l_790_);
v_r_791_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_r_791_);
v_w_792_ = lean_ctor_get(v_t_758_, 2);
lean_inc(v_w_792_);
v_lhs_793_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_lhs_793_);
v_rhs_794_ = lean_ctor_get(v_t_758_, 4);
lean_inc_ref(v_rhs_794_);
lean_dec_ref_known(v_t_758_, 5);
v___x_795_ = lean_apply_6(v_append_764_, v_l_790_, v_r_791_, v_w_792_, v_lhs_793_, v_rhs_794_, lean_box(0));
return v___x_795_;
}
case 6:
{
lean_object* v_w_796_; lean_object* v_w_x27_797_; lean_object* v_n_798_; lean_object* v_expr_799_; lean_object* v___x_800_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_w_796_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_w_796_);
v_w_x27_797_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_w_x27_797_);
v_n_798_ = lean_ctor_get(v_t_758_, 2);
lean_inc(v_n_798_);
v_expr_799_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_expr_799_);
lean_dec_ref_known(v_t_758_, 4);
v___x_800_ = lean_apply_5(v_replicate_765_, v_w_796_, v_w_x27_797_, v_n_798_, v_expr_799_, lean_box(0));
return v___x_800_;
}
case 7:
{
lean_object* v_m_801_; lean_object* v_n_802_; lean_object* v_lhs_803_; lean_object* v_rhs_804_; lean_object* v___x_805_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftRight_767_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_m_801_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_m_801_);
v_n_802_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_n_802_);
v_lhs_803_ = lean_ctor_get(v_t_758_, 2);
lean_inc_ref(v_lhs_803_);
v_rhs_804_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_rhs_804_);
lean_dec_ref_known(v_t_758_, 4);
v___x_805_ = lean_apply_4(v_shiftLeft_766_, v_m_801_, v_n_802_, v_lhs_803_, v_rhs_804_);
return v___x_805_;
}
case 8:
{
lean_object* v_m_806_; lean_object* v_n_807_; lean_object* v_lhs_808_; lean_object* v_rhs_809_; lean_object* v___x_810_; 
lean_dec(v_arithShiftRight_768_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_m_806_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_m_806_);
v_n_807_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_n_807_);
v_lhs_808_ = lean_ctor_get(v_t_758_, 2);
lean_inc_ref(v_lhs_808_);
v_rhs_809_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_rhs_809_);
lean_dec_ref_known(v_t_758_, 4);
v___x_810_ = lean_apply_4(v_shiftRight_767_, v_m_806_, v_n_807_, v_lhs_808_, v_rhs_809_);
return v___x_810_;
}
default: 
{
lean_object* v_m_811_; lean_object* v_n_812_; lean_object* v_lhs_813_; lean_object* v_rhs_814_; lean_object* v___x_815_; 
lean_dec(v_shiftRight_767_);
lean_dec(v_shiftLeft_766_);
lean_dec(v_replicate_765_);
lean_dec(v_append_764_);
lean_dec(v_un_763_);
lean_dec(v_bin_762_);
lean_dec(v_extract_761_);
lean_dec(v_const_760_);
lean_dec(v_var_759_);
v_m_811_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_m_811_);
v_n_812_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_n_812_);
v_lhs_813_ = lean_ctor_get(v_t_758_, 2);
lean_inc_ref(v_lhs_813_);
v_rhs_814_ = lean_ctor_get(v_t_758_, 3);
lean_inc_ref(v_rhs_814_);
lean_dec_ref_known(v_t_758_, 4);
v___x_815_ = lean_apply_4(v_arithShiftRight_768_, v_m_811_, v_n_812_, v_lhs_813_, v_rhs_814_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_816_, lean_object* v_a_817_, lean_object* v_t_818_, lean_object* v_var_819_, lean_object* v_const_820_, lean_object* v_extract_821_, lean_object* v_bin_822_, lean_object* v_un_823_, lean_object* v_append_824_, lean_object* v_replicate_825_, lean_object* v_shiftLeft_826_, lean_object* v_shiftRight_827_, lean_object* v_arithShiftRight_828_){
_start:
{
switch(lean_obj_tag(v_t_818_))
{
case 0:
{
lean_object* v_w_829_; lean_object* v_idx_830_; lean_object* v___x_831_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
v_w_829_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_829_);
v_idx_830_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_idx_830_);
lean_dec_ref_known(v_t_818_, 2);
v___x_831_ = lean_apply_2(v_var_819_, v_w_829_, v_idx_830_);
return v___x_831_;
}
case 1:
{
lean_object* v_w_832_; lean_object* v_val_833_; lean_object* v___x_834_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_var_819_);
v_w_832_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_832_);
v_val_833_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_val_833_);
lean_dec_ref_known(v_t_818_, 2);
v___x_834_ = lean_apply_2(v_const_820_, v_w_832_, v_val_833_);
return v___x_834_;
}
case 2:
{
lean_object* v_w_835_; lean_object* v_start_836_; lean_object* v_len_837_; lean_object* v_expr_838_; lean_object* v___x_839_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_w_835_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_835_);
v_start_836_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_start_836_);
v_len_837_ = lean_ctor_get(v_t_818_, 2);
lean_inc(v_len_837_);
v_expr_838_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_expr_838_);
lean_dec_ref_known(v_t_818_, 4);
v___x_839_ = lean_apply_4(v_extract_821_, v_w_835_, v_start_836_, v_len_837_, v_expr_838_);
return v___x_839_;
}
case 3:
{
lean_object* v_w_840_; lean_object* v_lhs_841_; uint8_t v_op_842_; lean_object* v_rhs_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_w_840_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_840_);
v_lhs_841_ = lean_ctor_get(v_t_818_, 1);
lean_inc_ref(v_lhs_841_);
v_op_842_ = lean_ctor_get_uint8(v_t_818_, sizeof(void*)*3 + 8);
v_rhs_843_ = lean_ctor_get(v_t_818_, 2);
lean_inc_ref(v_rhs_843_);
lean_dec_ref_known(v_t_818_, 3);
v___x_844_ = lean_box(v_op_842_);
v___x_845_ = lean_apply_4(v_bin_822_, v_w_840_, v_lhs_841_, v___x_844_, v_rhs_843_);
return v___x_845_;
}
case 4:
{
lean_object* v_w_846_; lean_object* v_op_847_; lean_object* v_operand_848_; lean_object* v___x_849_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_w_846_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_846_);
v_op_847_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_op_847_);
v_operand_848_ = lean_ctor_get(v_t_818_, 2);
lean_inc_ref(v_operand_848_);
lean_dec_ref_known(v_t_818_, 3);
v___x_849_ = lean_apply_3(v_un_823_, v_w_846_, v_op_847_, v_operand_848_);
return v___x_849_;
}
case 5:
{
lean_object* v_l_850_; lean_object* v_r_851_; lean_object* v_w_852_; lean_object* v_lhs_853_; lean_object* v_rhs_854_; lean_object* v___x_855_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_l_850_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_l_850_);
v_r_851_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_r_851_);
v_w_852_ = lean_ctor_get(v_t_818_, 2);
lean_inc(v_w_852_);
v_lhs_853_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_lhs_853_);
v_rhs_854_ = lean_ctor_get(v_t_818_, 4);
lean_inc_ref(v_rhs_854_);
lean_dec_ref_known(v_t_818_, 5);
v___x_855_ = lean_apply_6(v_append_824_, v_l_850_, v_r_851_, v_w_852_, v_lhs_853_, v_rhs_854_, lean_box(0));
return v___x_855_;
}
case 6:
{
lean_object* v_w_856_; lean_object* v_w_x27_857_; lean_object* v_n_858_; lean_object* v_expr_859_; lean_object* v___x_860_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_w_856_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_w_856_);
v_w_x27_857_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_w_x27_857_);
v_n_858_ = lean_ctor_get(v_t_818_, 2);
lean_inc(v_n_858_);
v_expr_859_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_expr_859_);
lean_dec_ref_known(v_t_818_, 4);
v___x_860_ = lean_apply_5(v_replicate_825_, v_w_856_, v_w_x27_857_, v_n_858_, v_expr_859_, lean_box(0));
return v___x_860_;
}
case 7:
{
lean_object* v_m_861_; lean_object* v_n_862_; lean_object* v_lhs_863_; lean_object* v_rhs_864_; lean_object* v___x_865_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftRight_827_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_m_861_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_m_861_);
v_n_862_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_n_862_);
v_lhs_863_ = lean_ctor_get(v_t_818_, 2);
lean_inc_ref(v_lhs_863_);
v_rhs_864_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_rhs_864_);
lean_dec_ref_known(v_t_818_, 4);
v___x_865_ = lean_apply_4(v_shiftLeft_826_, v_m_861_, v_n_862_, v_lhs_863_, v_rhs_864_);
return v___x_865_;
}
case 8:
{
lean_object* v_m_866_; lean_object* v_n_867_; lean_object* v_lhs_868_; lean_object* v_rhs_869_; lean_object* v___x_870_; 
lean_dec(v_arithShiftRight_828_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_m_866_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_m_866_);
v_n_867_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_n_867_);
v_lhs_868_ = lean_ctor_get(v_t_818_, 2);
lean_inc_ref(v_lhs_868_);
v_rhs_869_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_rhs_869_);
lean_dec_ref_known(v_t_818_, 4);
v___x_870_ = lean_apply_4(v_shiftRight_827_, v_m_866_, v_n_867_, v_lhs_868_, v_rhs_869_);
return v___x_870_;
}
default: 
{
lean_object* v_m_871_; lean_object* v_n_872_; lean_object* v_lhs_873_; lean_object* v_rhs_874_; lean_object* v___x_875_; 
lean_dec(v_shiftRight_827_);
lean_dec(v_shiftLeft_826_);
lean_dec(v_replicate_825_);
lean_dec(v_append_824_);
lean_dec(v_un_823_);
lean_dec(v_bin_822_);
lean_dec(v_extract_821_);
lean_dec(v_const_820_);
lean_dec(v_var_819_);
v_m_871_ = lean_ctor_get(v_t_818_, 0);
lean_inc(v_m_871_);
v_n_872_ = lean_ctor_get(v_t_818_, 1);
lean_inc(v_n_872_);
v_lhs_873_ = lean_ctor_get(v_t_818_, 2);
lean_inc_ref(v_lhs_873_);
v_rhs_874_ = lean_ctor_get(v_t_818_, 3);
lean_inc_ref(v_rhs_874_);
lean_dec_ref_known(v_t_818_, 4);
v___x_875_ = lean_apply_4(v_arithShiftRight_828_, v_m_871_, v_n_872_, v_lhs_873_, v_rhs_874_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_876_, lean_object* v_a_877_, lean_object* v_t_878_, lean_object* v_var_879_, lean_object* v_const_880_, lean_object* v_extract_881_, lean_object* v_bin_882_, lean_object* v_un_883_, lean_object* v_append_884_, lean_object* v_replicate_885_, lean_object* v_shiftLeft_886_, lean_object* v_shiftRight_887_, lean_object* v_arithShiftRight_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_876_, v_a_877_, v_t_878_, v_var_879_, v_const_880_, v_extract_881_, v_bin_882_, v_un_883_, v_append_884_, v_replicate_885_, v_shiftLeft_886_, v_shiftRight_887_, v_arithShiftRight_888_);
lean_dec(v_a_877_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_890_, lean_object* v_idx_891_){
_start:
{
uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; lean_object* v___x_897_; 
v___x_892_ = 5ULL;
v___x_893_ = lean_uint64_of_nat(v_w_890_);
v___x_894_ = lean_uint64_of_nat(v_idx_891_);
v___x_895_ = lean_uint64_mix_hash(v___x_893_, v___x_894_);
v___x_896_ = lean_uint64_mix_hash(v___x_892_, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_897_, 0, v_w_890_);
lean_ctor_set(v___x_897_, 1, v_idx_891_);
lean_ctor_set_uint64(v___x_897_, sizeof(void*)*2, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_898_, lean_object* v_val_899_){
_start:
{
uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; lean_object* v___x_905_; 
v___x_900_ = 7ULL;
v___x_901_ = lean_uint64_of_nat(v_w_898_);
v___x_902_ = l_BitVec_hash(v_w_898_, v_val_899_);
v___x_903_ = lean_uint64_mix_hash(v___x_901_, v___x_902_);
v___x_904_ = lean_uint64_mix_hash(v___x_900_, v___x_903_);
v___x_905_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_905_, 0, v_w_898_);
lean_ctor_set(v___x_905_, 1, v_val_899_);
lean_ctor_set_uint64(v___x_905_, sizeof(void*)*2, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_906_, lean_object* v_start_907_, lean_object* v_len_908_, lean_object* v_expr_909_){
_start:
{
uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___y_914_; 
v___x_910_ = 11ULL;
v___x_911_ = lean_uint64_of_nat(v_start_907_);
v___x_912_ = lean_uint64_of_nat(v_len_908_);
switch(lean_obj_tag(v_expr_909_))
{
case 0:
{
uint64_t v_hashCode_919_; 
v_hashCode_919_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*2);
v___y_914_ = v_hashCode_919_;
goto v___jp_913_;
}
case 1:
{
uint64_t v_hashCode_920_; 
v_hashCode_920_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*2);
v___y_914_ = v_hashCode_920_;
goto v___jp_913_;
}
case 3:
{
uint64_t v_hashCode_921_; 
v_hashCode_921_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*3);
v___y_914_ = v_hashCode_921_;
goto v___jp_913_;
}
case 4:
{
uint64_t v_hashCode_922_; 
v_hashCode_922_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*3);
v___y_914_ = v_hashCode_922_;
goto v___jp_913_;
}
case 5:
{
uint64_t v_hashCode_923_; 
v_hashCode_923_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*5);
v___y_914_ = v_hashCode_923_;
goto v___jp_913_;
}
default: 
{
uint64_t v_hashCode_924_; 
v_hashCode_924_ = lean_ctor_get_uint64(v_expr_909_, sizeof(void*)*4);
v___y_914_ = v_hashCode_924_;
goto v___jp_913_;
}
}
v___jp_913_:
{
uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_uint64_mix_hash(v___x_912_, v___y_914_);
v___x_916_ = lean_uint64_mix_hash(v___x_911_, v___x_915_);
v___x_917_ = lean_uint64_mix_hash(v___x_910_, v___x_916_);
v___x_918_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_918_, 0, v_w_906_);
lean_ctor_set(v___x_918_, 1, v_start_907_);
lean_ctor_set(v___x_918_, 2, v_len_908_);
lean_ctor_set(v___x_918_, 3, v_expr_909_);
lean_ctor_set_uint64(v___x_918_, sizeof(void*)*4, v___x_917_);
return v___x_918_;
}
}
}
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_925_, lean_object* v_lhs_926_, uint8_t v_op_927_, lean_object* v_rhs_928_){
_start:
{
uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___y_932_; uint64_t v___y_933_; uint64_t v___y_934_; uint64_t v___y_941_; 
v___x_929_ = 13ULL;
v___x_930_ = lean_uint64_of_nat(v_w_925_);
switch(lean_obj_tag(v_lhs_926_))
{
case 0:
{
uint64_t v_hashCode_949_; 
v_hashCode_949_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*2);
v___y_941_ = v_hashCode_949_;
goto v___jp_940_;
}
case 1:
{
uint64_t v_hashCode_950_; 
v_hashCode_950_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*2);
v___y_941_ = v_hashCode_950_;
goto v___jp_940_;
}
case 3:
{
uint64_t v_hashCode_951_; 
v_hashCode_951_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*3);
v___y_941_ = v_hashCode_951_;
goto v___jp_940_;
}
case 4:
{
uint64_t v_hashCode_952_; 
v_hashCode_952_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*3);
v___y_941_ = v_hashCode_952_;
goto v___jp_940_;
}
case 5:
{
uint64_t v_hashCode_953_; 
v_hashCode_953_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*5);
v___y_941_ = v_hashCode_953_;
goto v___jp_940_;
}
default: 
{
uint64_t v_hashCode_954_; 
v_hashCode_954_ = lean_ctor_get_uint64(v_lhs_926_, sizeof(void*)*4);
v___y_941_ = v_hashCode_954_;
goto v___jp_940_;
}
}
v___jp_931_:
{
uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; lean_object* v___x_939_; 
v___x_935_ = lean_uint64_mix_hash(v___y_932_, v___y_934_);
v___x_936_ = lean_uint64_mix_hash(v___y_933_, v___x_935_);
v___x_937_ = lean_uint64_mix_hash(v___x_930_, v___x_936_);
v___x_938_ = lean_uint64_mix_hash(v___x_929_, v___x_937_);
v___x_939_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_939_, 0, v_w_925_);
lean_ctor_set(v___x_939_, 1, v_lhs_926_);
lean_ctor_set(v___x_939_, 2, v_rhs_928_);
lean_ctor_set_uint64(v___x_939_, sizeof(void*)*3, v___x_938_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 8, v_op_927_);
return v___x_939_;
}
v___jp_940_:
{
uint64_t v___x_942_; 
v___x_942_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_927_);
switch(lean_obj_tag(v_rhs_928_))
{
case 0:
{
uint64_t v_hashCode_943_; 
v_hashCode_943_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*2);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_943_;
goto v___jp_931_;
}
case 1:
{
uint64_t v_hashCode_944_; 
v_hashCode_944_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*2);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_944_;
goto v___jp_931_;
}
case 3:
{
uint64_t v_hashCode_945_; 
v_hashCode_945_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*3);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_945_;
goto v___jp_931_;
}
case 4:
{
uint64_t v_hashCode_946_; 
v_hashCode_946_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*3);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_946_;
goto v___jp_931_;
}
case 5:
{
uint64_t v_hashCode_947_; 
v_hashCode_947_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*5);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_947_;
goto v___jp_931_;
}
default: 
{
uint64_t v_hashCode_948_; 
v_hashCode_948_ = lean_ctor_get_uint64(v_rhs_928_, sizeof(void*)*4);
v___y_932_ = v___x_942_;
v___y_933_ = v___y_941_;
v___y_934_ = v_hashCode_948_;
goto v___jp_931_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_bin___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_925_ = stack[0].m_obj;
lean_object* v_lhs_926_ = stack[1].m_obj;
uint8_t v_op_927_ = stack[2].m_num;
lean_object* v_rhs_928_ = stack[3].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_925_, v_lhs_926_, v_op_927_, v_rhs_928_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_956_, lean_object* v_lhs_957_, lean_object* v_op_958_, lean_object* v_rhs_959_){
_start:
{
uint8_t v_op_boxed_960_; lean_object* v_res_961_; 
v_op_boxed_960_ = lean_unbox(v_op_958_);
v_res_961_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_956_, v_lhs_957_, v_op_boxed_960_, v_rhs_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_962_, lean_object* v_op_963_, lean_object* v_operand_964_){
_start:
{
uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___y_969_; 
v___x_965_ = 17ULL;
v___x_966_ = lean_uint64_of_nat(v_w_962_);
v___x_967_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_963_);
switch(lean_obj_tag(v_operand_964_))
{
case 0:
{
uint64_t v_hashCode_974_; 
v_hashCode_974_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*2);
v___y_969_ = v_hashCode_974_;
goto v___jp_968_;
}
case 1:
{
uint64_t v_hashCode_975_; 
v_hashCode_975_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*2);
v___y_969_ = v_hashCode_975_;
goto v___jp_968_;
}
case 3:
{
uint64_t v_hashCode_976_; 
v_hashCode_976_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*3);
v___y_969_ = v_hashCode_976_;
goto v___jp_968_;
}
case 4:
{
uint64_t v_hashCode_977_; 
v_hashCode_977_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*3);
v___y_969_ = v_hashCode_977_;
goto v___jp_968_;
}
case 5:
{
uint64_t v_hashCode_978_; 
v_hashCode_978_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*5);
v___y_969_ = v_hashCode_978_;
goto v___jp_968_;
}
default: 
{
uint64_t v_hashCode_979_; 
v_hashCode_979_ = lean_ctor_get_uint64(v_operand_964_, sizeof(void*)*4);
v___y_969_ = v_hashCode_979_;
goto v___jp_968_;
}
}
v___jp_968_:
{
uint64_t v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_uint64_mix_hash(v___x_967_, v___y_969_);
v___x_971_ = lean_uint64_mix_hash(v___x_966_, v___x_970_);
v___x_972_ = lean_uint64_mix_hash(v___x_965_, v___x_971_);
v___x_973_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_973_, 0, v_w_962_);
lean_ctor_set(v___x_973_, 1, v_op_963_);
lean_ctor_set(v___x_973_, 2, v_operand_964_);
lean_ctor_set_uint64(v___x_973_, sizeof(void*)*3, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_980_, lean_object* v_r_981_, lean_object* v_w_982_, lean_object* v_lhs_983_, lean_object* v_rhs_984_){
_start:
{
uint64_t v___x_985_; uint64_t v___x_986_; uint64_t v___y_988_; uint64_t v___y_989_; uint64_t v___y_995_; 
v___x_985_ = 19ULL;
v___x_986_ = lean_uint64_of_nat(v_w_982_);
switch(lean_obj_tag(v_lhs_983_))
{
case 0:
{
uint64_t v_hashCode_1002_; 
v_hashCode_1002_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*2);
v___y_995_ = v_hashCode_1002_;
goto v___jp_994_;
}
case 1:
{
uint64_t v_hashCode_1003_; 
v_hashCode_1003_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*2);
v___y_995_ = v_hashCode_1003_;
goto v___jp_994_;
}
case 3:
{
uint64_t v_hashCode_1004_; 
v_hashCode_1004_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*3);
v___y_995_ = v_hashCode_1004_;
goto v___jp_994_;
}
case 4:
{
uint64_t v_hashCode_1005_; 
v_hashCode_1005_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*3);
v___y_995_ = v_hashCode_1005_;
goto v___jp_994_;
}
case 5:
{
uint64_t v_hashCode_1006_; 
v_hashCode_1006_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*5);
v___y_995_ = v_hashCode_1006_;
goto v___jp_994_;
}
default: 
{
uint64_t v_hashCode_1007_; 
v_hashCode_1007_ = lean_ctor_get_uint64(v_lhs_983_, sizeof(void*)*4);
v___y_995_ = v_hashCode_1007_;
goto v___jp_994_;
}
}
v___jp_987_:
{
uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_uint64_mix_hash(v___y_988_, v___y_989_);
v___x_991_ = lean_uint64_mix_hash(v___x_986_, v___x_990_);
v___x_992_ = lean_uint64_mix_hash(v___x_985_, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_993_, 0, v_l_980_);
lean_ctor_set(v___x_993_, 1, v_r_981_);
lean_ctor_set(v___x_993_, 2, v_w_982_);
lean_ctor_set(v___x_993_, 3, v_lhs_983_);
lean_ctor_set(v___x_993_, 4, v_rhs_984_);
lean_ctor_set_uint64(v___x_993_, sizeof(void*)*5, v___x_992_);
return v___x_993_;
}
v___jp_994_:
{
switch(lean_obj_tag(v_rhs_984_))
{
case 0:
{
uint64_t v_hashCode_996_; 
v_hashCode_996_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*2);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_996_;
goto v___jp_987_;
}
case 1:
{
uint64_t v_hashCode_997_; 
v_hashCode_997_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*2);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_997_;
goto v___jp_987_;
}
case 3:
{
uint64_t v_hashCode_998_; 
v_hashCode_998_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*3);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_998_;
goto v___jp_987_;
}
case 4:
{
uint64_t v_hashCode_999_; 
v_hashCode_999_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*3);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_999_;
goto v___jp_987_;
}
case 5:
{
uint64_t v_hashCode_1000_; 
v_hashCode_1000_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*5);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_1000_;
goto v___jp_987_;
}
default: 
{
uint64_t v_hashCode_1001_; 
v_hashCode_1001_ = lean_ctor_get_uint64(v_rhs_984_, sizeof(void*)*4);
v___y_988_ = v___y_995_;
v___y_989_ = v_hashCode_1001_;
goto v___jp_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_1008_, lean_object* v_r_1009_, lean_object* v_w_1010_, lean_object* v_lhs_1011_, lean_object* v_rhs_1012_, lean_object* v_h_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_1008_, v_r_1009_, v_w_1010_, v_lhs_1011_, v_rhs_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_1015_, lean_object* v_w_x27_1016_, lean_object* v_n_1017_, lean_object* v_expr_1018_){
_start:
{
uint64_t v___x_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v___y_1023_; 
v___x_1019_ = 23ULL;
v___x_1020_ = lean_uint64_of_nat(v_w_x27_1016_);
v___x_1021_ = lean_uint64_of_nat(v_n_1017_);
switch(lean_obj_tag(v_expr_1018_))
{
case 0:
{
uint64_t v_hashCode_1028_; 
v_hashCode_1028_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*2);
v___y_1023_ = v_hashCode_1028_;
goto v___jp_1022_;
}
case 1:
{
uint64_t v_hashCode_1029_; 
v_hashCode_1029_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*2);
v___y_1023_ = v_hashCode_1029_;
goto v___jp_1022_;
}
case 3:
{
uint64_t v_hashCode_1030_; 
v_hashCode_1030_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*3);
v___y_1023_ = v_hashCode_1030_;
goto v___jp_1022_;
}
case 4:
{
uint64_t v_hashCode_1031_; 
v_hashCode_1031_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*3);
v___y_1023_ = v_hashCode_1031_;
goto v___jp_1022_;
}
case 5:
{
uint64_t v_hashCode_1032_; 
v_hashCode_1032_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*5);
v___y_1023_ = v_hashCode_1032_;
goto v___jp_1022_;
}
default: 
{
uint64_t v_hashCode_1033_; 
v_hashCode_1033_ = lean_ctor_get_uint64(v_expr_1018_, sizeof(void*)*4);
v___y_1023_ = v_hashCode_1033_;
goto v___jp_1022_;
}
}
v___jp_1022_:
{
uint64_t v___x_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_uint64_mix_hash(v___x_1021_, v___y_1023_);
v___x_1025_ = lean_uint64_mix_hash(v___x_1020_, v___x_1024_);
v___x_1026_ = lean_uint64_mix_hash(v___x_1019_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1027_, 0, v_w_1015_);
lean_ctor_set(v___x_1027_, 1, v_w_x27_1016_);
lean_ctor_set(v___x_1027_, 2, v_n_1017_);
lean_ctor_set(v___x_1027_, 3, v_expr_1018_);
lean_ctor_set_uint64(v___x_1027_, sizeof(void*)*4, v___x_1026_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1034_, lean_object* v_w_x27_1035_, lean_object* v_n_1036_, lean_object* v_expr_1037_, lean_object* v_h_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1034_, v_w_x27_1035_, v_n_1036_, v_expr_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1040_, lean_object* v_n_1041_, lean_object* v_lhs_1042_, lean_object* v_rhs_1043_){
_start:
{
uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___y_1047_; uint64_t v___y_1048_; uint64_t v___y_1054_; 
v___x_1044_ = 29ULL;
v___x_1045_ = lean_uint64_of_nat(v_m_1040_);
switch(lean_obj_tag(v_lhs_1042_))
{
case 0:
{
uint64_t v_hashCode_1061_; 
v_hashCode_1061_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*2);
v___y_1054_ = v_hashCode_1061_;
goto v___jp_1053_;
}
case 1:
{
uint64_t v_hashCode_1062_; 
v_hashCode_1062_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*2);
v___y_1054_ = v_hashCode_1062_;
goto v___jp_1053_;
}
case 3:
{
uint64_t v_hashCode_1063_; 
v_hashCode_1063_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*3);
v___y_1054_ = v_hashCode_1063_;
goto v___jp_1053_;
}
case 4:
{
uint64_t v_hashCode_1064_; 
v_hashCode_1064_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*3);
v___y_1054_ = v_hashCode_1064_;
goto v___jp_1053_;
}
case 5:
{
uint64_t v_hashCode_1065_; 
v_hashCode_1065_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*5);
v___y_1054_ = v_hashCode_1065_;
goto v___jp_1053_;
}
default: 
{
uint64_t v_hashCode_1066_; 
v_hashCode_1066_ = lean_ctor_get_uint64(v_lhs_1042_, sizeof(void*)*4);
v___y_1054_ = v_hashCode_1066_;
goto v___jp_1053_;
}
}
v___jp_1046_:
{
uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_uint64_mix_hash(v___y_1047_, v___y_1048_);
v___x_1050_ = lean_uint64_mix_hash(v___x_1045_, v___x_1049_);
v___x_1051_ = lean_uint64_mix_hash(v___x_1044_, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1052_, 0, v_m_1040_);
lean_ctor_set(v___x_1052_, 1, v_n_1041_);
lean_ctor_set(v___x_1052_, 2, v_lhs_1042_);
lean_ctor_set(v___x_1052_, 3, v_rhs_1043_);
lean_ctor_set_uint64(v___x_1052_, sizeof(void*)*4, v___x_1051_);
return v___x_1052_;
}
v___jp_1053_:
{
switch(lean_obj_tag(v_rhs_1043_))
{
case 0:
{
uint64_t v_hashCode_1055_; 
v_hashCode_1055_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*2);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1055_;
goto v___jp_1046_;
}
case 1:
{
uint64_t v_hashCode_1056_; 
v_hashCode_1056_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*2);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1056_;
goto v___jp_1046_;
}
case 3:
{
uint64_t v_hashCode_1057_; 
v_hashCode_1057_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*3);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1057_;
goto v___jp_1046_;
}
case 4:
{
uint64_t v_hashCode_1058_; 
v_hashCode_1058_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*3);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1058_;
goto v___jp_1046_;
}
case 5:
{
uint64_t v_hashCode_1059_; 
v_hashCode_1059_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*5);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1059_;
goto v___jp_1046_;
}
default: 
{
uint64_t v_hashCode_1060_; 
v_hashCode_1060_ = lean_ctor_get_uint64(v_rhs_1043_, sizeof(void*)*4);
v___y_1047_ = v___y_1054_;
v___y_1048_ = v_hashCode_1060_;
goto v___jp_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1067_, lean_object* v_n_1068_, lean_object* v_lhs_1069_, lean_object* v_rhs_1070_){
_start:
{
uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v___y_1074_; uint64_t v___y_1075_; uint64_t v___y_1081_; 
v___x_1071_ = 31ULL;
v___x_1072_ = lean_uint64_of_nat(v_m_1067_);
switch(lean_obj_tag(v_lhs_1069_))
{
case 0:
{
uint64_t v_hashCode_1088_; 
v_hashCode_1088_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*2);
v___y_1081_ = v_hashCode_1088_;
goto v___jp_1080_;
}
case 1:
{
uint64_t v_hashCode_1089_; 
v_hashCode_1089_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*2);
v___y_1081_ = v_hashCode_1089_;
goto v___jp_1080_;
}
case 3:
{
uint64_t v_hashCode_1090_; 
v_hashCode_1090_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*3);
v___y_1081_ = v_hashCode_1090_;
goto v___jp_1080_;
}
case 4:
{
uint64_t v_hashCode_1091_; 
v_hashCode_1091_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*3);
v___y_1081_ = v_hashCode_1091_;
goto v___jp_1080_;
}
case 5:
{
uint64_t v_hashCode_1092_; 
v_hashCode_1092_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*5);
v___y_1081_ = v_hashCode_1092_;
goto v___jp_1080_;
}
default: 
{
uint64_t v_hashCode_1093_; 
v_hashCode_1093_ = lean_ctor_get_uint64(v_lhs_1069_, sizeof(void*)*4);
v___y_1081_ = v_hashCode_1093_;
goto v___jp_1080_;
}
}
v___jp_1073_:
{
uint64_t v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_uint64_mix_hash(v___y_1074_, v___y_1075_);
v___x_1077_ = lean_uint64_mix_hash(v___x_1072_, v___x_1076_);
v___x_1078_ = lean_uint64_mix_hash(v___x_1071_, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1079_, 0, v_m_1067_);
lean_ctor_set(v___x_1079_, 1, v_n_1068_);
lean_ctor_set(v___x_1079_, 2, v_lhs_1069_);
lean_ctor_set(v___x_1079_, 3, v_rhs_1070_);
lean_ctor_set_uint64(v___x_1079_, sizeof(void*)*4, v___x_1078_);
return v___x_1079_;
}
v___jp_1080_:
{
switch(lean_obj_tag(v_rhs_1070_))
{
case 0:
{
uint64_t v_hashCode_1082_; 
v_hashCode_1082_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*2);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1082_;
goto v___jp_1073_;
}
case 1:
{
uint64_t v_hashCode_1083_; 
v_hashCode_1083_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*2);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1083_;
goto v___jp_1073_;
}
case 3:
{
uint64_t v_hashCode_1084_; 
v_hashCode_1084_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*3);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1084_;
goto v___jp_1073_;
}
case 4:
{
uint64_t v_hashCode_1085_; 
v_hashCode_1085_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*3);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1085_;
goto v___jp_1073_;
}
case 5:
{
uint64_t v_hashCode_1086_; 
v_hashCode_1086_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*5);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1086_;
goto v___jp_1073_;
}
default: 
{
uint64_t v_hashCode_1087_; 
v_hashCode_1087_ = lean_ctor_get_uint64(v_rhs_1070_, sizeof(void*)*4);
v___y_1074_ = v___y_1081_;
v___y_1075_ = v_hashCode_1087_;
goto v___jp_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1094_, lean_object* v_n_1095_, lean_object* v_lhs_1096_, lean_object* v_rhs_1097_){
_start:
{
uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___y_1101_; uint64_t v___y_1102_; uint64_t v___y_1108_; 
v___x_1098_ = 37ULL;
v___x_1099_ = lean_uint64_of_nat(v_m_1094_);
switch(lean_obj_tag(v_lhs_1096_))
{
case 0:
{
uint64_t v_hashCode_1115_; 
v_hashCode_1115_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*2);
v___y_1108_ = v_hashCode_1115_;
goto v___jp_1107_;
}
case 1:
{
uint64_t v_hashCode_1116_; 
v_hashCode_1116_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*2);
v___y_1108_ = v_hashCode_1116_;
goto v___jp_1107_;
}
case 3:
{
uint64_t v_hashCode_1117_; 
v_hashCode_1117_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*3);
v___y_1108_ = v_hashCode_1117_;
goto v___jp_1107_;
}
case 4:
{
uint64_t v_hashCode_1118_; 
v_hashCode_1118_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*3);
v___y_1108_ = v_hashCode_1118_;
goto v___jp_1107_;
}
case 5:
{
uint64_t v_hashCode_1119_; 
v_hashCode_1119_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*5);
v___y_1108_ = v_hashCode_1119_;
goto v___jp_1107_;
}
default: 
{
uint64_t v_hashCode_1120_; 
v_hashCode_1120_ = lean_ctor_get_uint64(v_lhs_1096_, sizeof(void*)*4);
v___y_1108_ = v_hashCode_1120_;
goto v___jp_1107_;
}
}
v___jp_1100_:
{
uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = lean_uint64_mix_hash(v___y_1101_, v___y_1102_);
v___x_1104_ = lean_uint64_mix_hash(v___x_1099_, v___x_1103_);
v___x_1105_ = lean_uint64_mix_hash(v___x_1098_, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1106_, 0, v_m_1094_);
lean_ctor_set(v___x_1106_, 1, v_n_1095_);
lean_ctor_set(v___x_1106_, 2, v_lhs_1096_);
lean_ctor_set(v___x_1106_, 3, v_rhs_1097_);
lean_ctor_set_uint64(v___x_1106_, sizeof(void*)*4, v___x_1105_);
return v___x_1106_;
}
v___jp_1107_:
{
switch(lean_obj_tag(v_rhs_1097_))
{
case 0:
{
uint64_t v_hashCode_1109_; 
v_hashCode_1109_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*2);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1109_;
goto v___jp_1100_;
}
case 1:
{
uint64_t v_hashCode_1110_; 
v_hashCode_1110_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*2);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1110_;
goto v___jp_1100_;
}
case 3:
{
uint64_t v_hashCode_1111_; 
v_hashCode_1111_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*3);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1111_;
goto v___jp_1100_;
}
case 4:
{
uint64_t v_hashCode_1112_; 
v_hashCode_1112_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*3);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1112_;
goto v___jp_1100_;
}
case 5:
{
uint64_t v_hashCode_1113_; 
v_hashCode_1113_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*5);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1113_;
goto v___jp_1100_;
}
default: 
{
uint64_t v_hashCode_1114_; 
v_hashCode_1114_ = lean_ctor_get_uint64(v_rhs_1097_, sizeof(void*)*4);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v_hashCode_1114_;
goto v___jp_1100_;
}
}
}
}
}
uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1121_){
_start:
{
switch(lean_obj_tag(v_x_1121_))
{
case 0:
{
uint64_t v_hashCode_1122_; 
v_hashCode_1122_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*2);
return v_hashCode_1122_;
}
case 1:
{
uint64_t v_hashCode_1123_; 
v_hashCode_1123_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*2);
return v_hashCode_1123_;
}
case 3:
{
uint64_t v_hashCode_1124_; 
v_hashCode_1124_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*3);
return v_hashCode_1124_;
}
case 4:
{
uint64_t v_hashCode_1125_; 
v_hashCode_1125_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*3);
return v_hashCode_1125_;
}
case 5:
{
uint64_t v_hashCode_1126_; 
v_hashCode_1126_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*5);
return v_hashCode_1126_;
}
default: 
{
uint64_t v_hashCode_1127_; 
v_hashCode_1127_ = lean_ctor_get_uint64(v_x_1121_, sizeof(void*)*4);
return v_hashCode_1127_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1121_ = stack[0].m_obj;
uint64_t v_res_1128_;
v_res_1128_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1121_);
stack->m_num = v_res_1128_;
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
uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1132_, lean_object* v_x_1133_){
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
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_hashCode___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1132_ = stack[0].m_obj;
lean_object* v_x_1133_ = stack[1].m_obj;
uint64_t v_res_1140_;
v_res_1140_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1132_, v_x_1133_);
stack->m_num = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1141_, lean_object* v_x_1142_){
_start:
{
uint64_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1141_, v_x_1142_);
lean_dec_ref(v_x_1142_);
lean_dec(v_a_1141_);
v_r_1144_ = lean_box_uint64(v_res_1143_);
return v_r_1144_;
}
}
uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(lean_object* v_expr_1145_){
_start:
{
switch(lean_obj_tag(v_expr_1145_))
{
case 0:
{
uint64_t v_hashCode_1146_; 
v_hashCode_1146_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*2);
return v_hashCode_1146_;
}
case 1:
{
uint64_t v_hashCode_1147_; 
v_hashCode_1147_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*2);
return v_hashCode_1147_;
}
case 3:
{
uint64_t v_hashCode_1148_; 
v_hashCode_1148_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*3);
return v_hashCode_1148_;
}
case 4:
{
uint64_t v_hashCode_1149_; 
v_hashCode_1149_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*3);
return v_hashCode_1149_;
}
case 5:
{
uint64_t v_hashCode_1150_; 
v_hashCode_1150_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*5);
return v_hashCode_1150_;
}
default: 
{
uint64_t v_hashCode_1151_; 
v_hashCode_1151_ = lean_ctor_get_uint64(v_expr_1145_, sizeof(void*)*4);
return v_hashCode_1151_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_1145_ = stack[0].m_obj;
uint64_t v_res_1152_;
v_res_1152_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(v_expr_1145_);
stack->m_num = v_res_1152_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0___boxed(lean_object* v_expr_1153_){
_start:
{
uint64_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(v_expr_1153_);
lean_dec_ref(v_expr_1153_);
v_r_1155_ = lean_box_uint64(v_res_1154_);
return v_r_1155_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg(){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1158_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1159_;
v_res_1159_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg();
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___boxed(lean_object* v___dummy_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg();
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1162_){
_start:
{
lean_object* v___f_1163_; 
v___f_1163_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* v_w_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_1164_);
lean_dec(v_w_1164_);
return v_res_1165_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(lean_object* v_a_1166_, lean_object* v_b_1167_, lean_object* v_k_1168_){
_start:
{
size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_ptr_addr(v_a_1166_);
v___x_1170_ = lean_ptr_addr(v_b_1167_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_apply_1(v_k_1168_, v___x_1172_);
v___x_1174_ = lean_unbox(v___x_1173_);
return v___x_1174_;
}
else
{
lean_dec_ref(v_k_1168_);
return v___x_1171_;
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1166_ = stack[0].m_obj;
lean_object* v_b_1167_ = stack[1].m_obj;
lean_object* v_k_1168_ = stack[2].m_obj;
uint8_t v_res_1175_;
v_res_1175_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(v_a_1166_, v_b_1167_, v_k_1168_);
stack->m_num = v_res_1175_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg___boxed(lean_object* v_a_1176_, lean_object* v_b_1177_, lean_object* v_k_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(v_a_1176_, v_b_1177_, v_k_1178_);
lean_dec_ref(v_b_1177_);
lean_dec_ref(v_a_1176_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(lean_object* v_w_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_, lean_object* v_k_1184_, lean_object* v_h_1185_){
_start:
{
size_t v___x_1186_; size_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_ptr_addr(v_a_1182_);
v___x_1187_ = lean_ptr_addr(v_b_1183_);
v___x_1188_ = lean_usize_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_apply_1(v_k_1184_, v___x_1189_);
v___x_1191_ = lean_unbox(v___x_1190_);
return v___x_1191_;
}
else
{
lean_dec_ref(v_k_1184_);
return v___x_1188_;
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1181_ = stack[0].m_obj;
lean_object* v_a_1182_ = stack[1].m_obj;
lean_object* v_b_1183_ = stack[2].m_obj;
lean_object* v_k_1184_ = stack[3].m_obj;
uint8_t v_res_1192_;
v_res_1192_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(v_w_1181_, v_a_1182_, v_b_1183_, v_k_1184_, lean_box(0));
stack->m_num = v_res_1192_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___boxed(lean_object* v_w_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_, lean_object* v_k_1196_, lean_object* v_h_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(v_w_1193_, v_a_1194_, v_b_1195_, v_k_1196_, v_h_1197_);
lean_dec_ref(v_b_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_w_1193_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1200_, lean_object* v_r_1201_){
_start:
{
size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; uint64_t v___y_1206_; uint64_t v___y_1207_; uint64_t v___y_1292_; 
v___x_1202_ = lean_ptr_addr(v_l_1200_);
v___x_1203_ = lean_ptr_addr(v_r_1201_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
switch(lean_obj_tag(v_l_1200_))
{
case 0:
{
uint64_t v_hashCode_1299_; 
v_hashCode_1299_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*2);
v___y_1292_ = v_hashCode_1299_;
goto v___jp_1291_;
}
case 1:
{
uint64_t v_hashCode_1300_; 
v_hashCode_1300_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*2);
v___y_1292_ = v_hashCode_1300_;
goto v___jp_1291_;
}
case 3:
{
uint64_t v_hashCode_1301_; 
v_hashCode_1301_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*3);
v___y_1292_ = v_hashCode_1301_;
goto v___jp_1291_;
}
case 4:
{
uint64_t v_hashCode_1302_; 
v_hashCode_1302_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*3);
v___y_1292_ = v_hashCode_1302_;
goto v___jp_1291_;
}
case 5:
{
uint64_t v_hashCode_1303_; 
v_hashCode_1303_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*5);
v___y_1292_ = v_hashCode_1303_;
goto v___jp_1291_;
}
default: 
{
uint64_t v_hashCode_1304_; 
v_hashCode_1304_ = lean_ctor_get_uint64(v_l_1200_, sizeof(void*)*4);
v___y_1292_ = v_hashCode_1304_;
goto v___jp_1291_;
}
}
}
else
{
return v___x_1204_;
}
v___jp_1205_:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_uint64_dec_eq(v___y_1206_, v___y_1207_);
if (v___x_1208_ == 0)
{
return v___x_1204_;
}
else
{
if (v___x_1204_ == 0)
{
switch(lean_obj_tag(v_l_1200_))
{
case 0:
{
if (lean_obj_tag(v_r_1201_) == 0)
{
lean_object* v_idx_1209_; lean_object* v_idx_1210_; uint8_t v___x_1211_; 
v_idx_1209_ = lean_ctor_get(v_l_1200_, 1);
v_idx_1210_ = lean_ctor_get(v_r_1201_, 1);
v___x_1211_ = lean_nat_dec_eq(v_idx_1209_, v_idx_1210_);
return v___x_1211_;
}
else
{
return v___x_1204_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1201_) == 1)
{
lean_object* v_val_1212_; lean_object* v_val_1213_; uint8_t v___x_1214_; 
v_val_1212_ = lean_ctor_get(v_l_1200_, 1);
v_val_1213_ = lean_ctor_get(v_r_1201_, 1);
v___x_1214_ = lean_nat_dec_eq(v_val_1212_, v_val_1213_);
return v___x_1214_;
}
else
{
return v___x_1204_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1201_) == 2)
{
lean_object* v_w_1215_; lean_object* v_start_1216_; lean_object* v_expr_1217_; lean_object* v_w_1218_; lean_object* v_start_1219_; lean_object* v_expr_1220_; uint8_t v___x_1221_; 
v_w_1215_ = lean_ctor_get(v_l_1200_, 0);
v_start_1216_ = lean_ctor_get(v_l_1200_, 1);
v_expr_1217_ = lean_ctor_get(v_l_1200_, 3);
v_w_1218_ = lean_ctor_get(v_r_1201_, 0);
v_start_1219_ = lean_ctor_get(v_r_1201_, 1);
v_expr_1220_ = lean_ctor_get(v_r_1201_, 3);
v___x_1221_ = lean_nat_dec_eq(v_w_1215_, v_w_1218_);
if (v___x_1221_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_eq(v_start_1216_, v_start_1219_);
if (v___x_1222_ == 0)
{
return v___x_1222_;
}
else
{
uint8_t v_decide_1223_; 
v_decide_1223_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1217_, v_expr_1220_);
if (v_decide_1223_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1222_;
}
}
}
}
else
{
return v___x_1204_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1201_) == 3)
{
lean_object* v_lhs_1224_; uint8_t v_op_1225_; lean_object* v_rhs_1226_; lean_object* v_lhs_1227_; uint8_t v_op_1228_; lean_object* v_rhs_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_lhs_1224_ = lean_ctor_get(v_l_1200_, 1);
v_op_1225_ = lean_ctor_get_uint8(v_l_1200_, sizeof(void*)*3 + 8);
v_rhs_1226_ = lean_ctor_get(v_l_1200_, 2);
v_lhs_1227_ = lean_ctor_get(v_r_1201_, 1);
v_op_1228_ = lean_ctor_get_uint8(v_r_1201_, sizeof(void*)*3 + 8);
v_rhs_1229_ = lean_ctor_get(v_r_1201_, 2);
v___x_1230_ = lean_box(v_op_1225_);
v___x_1231_ = lean_obj_tag_nat(v___x_1230_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_box(v_op_1228_);
v___x_1233_ = lean_obj_tag_nat(v___x_1232_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_nat_dec_eq(v___x_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
return v___x_1234_;
}
else
{
uint8_t v_decide_1235_; 
v_decide_1235_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1224_, v_lhs_1227_);
if (v_decide_1235_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v_decide_1236_; 
v_decide_1236_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1226_, v_rhs_1229_);
if (v_decide_1236_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1234_;
}
}
}
}
else
{
return v___x_1204_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1201_) == 4)
{
lean_object* v_op_1237_; lean_object* v_operand_1238_; lean_object* v_op_1239_; lean_object* v_operand_1240_; uint8_t v___x_1241_; 
v_op_1237_ = lean_ctor_get(v_l_1200_, 1);
v_operand_1238_ = lean_ctor_get(v_l_1200_, 2);
v_op_1239_ = lean_ctor_get(v_r_1201_, 1);
v_operand_1240_ = lean_ctor_get(v_r_1201_, 2);
v___x_1241_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1237_, v_op_1239_);
if (v___x_1241_ == 0)
{
return v___x_1241_;
}
else
{
uint8_t v_decide_1242_; 
v_decide_1242_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_operand_1238_, v_operand_1240_);
if (v_decide_1242_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1241_;
}
}
}
else
{
return v___x_1204_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1201_) == 5)
{
lean_object* v_l_1243_; lean_object* v_r_1244_; lean_object* v_lhs_1245_; lean_object* v_rhs_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v_lhs_1249_; lean_object* v_rhs_1250_; uint8_t v___x_1251_; 
v_l_1243_ = lean_ctor_get(v_l_1200_, 0);
v_r_1244_ = lean_ctor_get(v_l_1200_, 1);
v_lhs_1245_ = lean_ctor_get(v_l_1200_, 3);
v_rhs_1246_ = lean_ctor_get(v_l_1200_, 4);
v_l_1247_ = lean_ctor_get(v_r_1201_, 0);
v_r_1248_ = lean_ctor_get(v_r_1201_, 1);
v_lhs_1249_ = lean_ctor_get(v_r_1201_, 3);
v_rhs_1250_ = lean_ctor_get(v_r_1201_, 4);
v___x_1251_ = lean_nat_dec_eq(v_l_1243_, v_l_1247_);
if (v___x_1251_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_nat_dec_eq(v_r_1244_, v_r_1248_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
uint8_t v_decide_1253_; 
v_decide_1253_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1245_, v_lhs_1249_);
if (v_decide_1253_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v_decide_1254_; 
v_decide_1254_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1246_, v_rhs_1250_);
if (v_decide_1254_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1252_;
}
}
}
}
}
else
{
return v___x_1204_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1201_) == 6)
{
lean_object* v_w_1255_; lean_object* v_n_1256_; lean_object* v_expr_1257_; lean_object* v_w_1258_; lean_object* v_n_1259_; lean_object* v_expr_1260_; uint8_t v___x_1261_; 
v_w_1255_ = lean_ctor_get(v_l_1200_, 0);
v_n_1256_ = lean_ctor_get(v_l_1200_, 2);
v_expr_1257_ = lean_ctor_get(v_l_1200_, 3);
v_w_1258_ = lean_ctor_get(v_r_1201_, 0);
v_n_1259_ = lean_ctor_get(v_r_1201_, 2);
v_expr_1260_ = lean_ctor_get(v_r_1201_, 3);
v___x_1261_ = lean_nat_dec_eq(v_n_1256_, v_n_1259_);
if (v___x_1261_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_w_1255_, v_w_1258_);
if (v___x_1262_ == 0)
{
return v___x_1262_;
}
else
{
uint8_t v_decide_1263_; 
v_decide_1263_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1257_, v_expr_1260_);
if (v_decide_1263_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1262_;
}
}
}
}
else
{
return v___x_1204_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1201_) == 7)
{
lean_object* v_n_1264_; lean_object* v_lhs_1265_; lean_object* v_rhs_1266_; lean_object* v_n_1267_; lean_object* v_lhs_1268_; lean_object* v_rhs_1269_; uint8_t v___x_1270_; 
v_n_1264_ = lean_ctor_get(v_l_1200_, 1);
v_lhs_1265_ = lean_ctor_get(v_l_1200_, 2);
v_rhs_1266_ = lean_ctor_get(v_l_1200_, 3);
v_n_1267_ = lean_ctor_get(v_r_1201_, 1);
v_lhs_1268_ = lean_ctor_get(v_r_1201_, 2);
v_rhs_1269_ = lean_ctor_get(v_r_1201_, 3);
v___x_1270_ = lean_nat_dec_eq(v_n_1264_, v_n_1267_);
if (v___x_1270_ == 0)
{
return v___x_1270_;
}
else
{
uint8_t v_decide_1271_; 
v_decide_1271_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1265_, v_lhs_1268_);
if (v_decide_1271_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v_decide_1272_; 
v_decide_1272_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1266_, v_rhs_1269_);
if (v_decide_1272_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1270_;
}
}
}
}
else
{
return v___x_1204_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1201_) == 8)
{
lean_object* v_n_1273_; lean_object* v_lhs_1274_; lean_object* v_rhs_1275_; lean_object* v_n_1276_; lean_object* v_lhs_1277_; lean_object* v_rhs_1278_; uint8_t v___x_1279_; 
v_n_1273_ = lean_ctor_get(v_l_1200_, 1);
v_lhs_1274_ = lean_ctor_get(v_l_1200_, 2);
v_rhs_1275_ = lean_ctor_get(v_l_1200_, 3);
v_n_1276_ = lean_ctor_get(v_r_1201_, 1);
v_lhs_1277_ = lean_ctor_get(v_r_1201_, 2);
v_rhs_1278_ = lean_ctor_get(v_r_1201_, 3);
v___x_1279_ = lean_nat_dec_eq(v_n_1273_, v_n_1276_);
if (v___x_1279_ == 0)
{
return v___x_1279_;
}
else
{
uint8_t v_decide_1280_; 
v_decide_1280_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1274_, v_lhs_1277_);
if (v_decide_1280_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v_decide_1281_; 
v_decide_1281_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1275_, v_rhs_1278_);
if (v_decide_1281_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1279_;
}
}
}
}
else
{
return v___x_1204_;
}
}
default: 
{
if (lean_obj_tag(v_r_1201_) == 9)
{
lean_object* v_n_1282_; lean_object* v_lhs_1283_; lean_object* v_rhs_1284_; lean_object* v_n_1285_; lean_object* v_lhs_1286_; lean_object* v_rhs_1287_; uint8_t v___x_1288_; 
v_n_1282_ = lean_ctor_get(v_l_1200_, 1);
v_lhs_1283_ = lean_ctor_get(v_l_1200_, 2);
v_rhs_1284_ = lean_ctor_get(v_l_1200_, 3);
v_n_1285_ = lean_ctor_get(v_r_1201_, 1);
v_lhs_1286_ = lean_ctor_get(v_r_1201_, 2);
v_rhs_1287_ = lean_ctor_get(v_r_1201_, 3);
v___x_1288_ = lean_nat_dec_eq(v_n_1282_, v_n_1285_);
if (v___x_1288_ == 0)
{
return v___x_1288_;
}
else
{
uint8_t v_decide_1289_; 
v_decide_1289_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1283_, v_lhs_1286_);
if (v_decide_1289_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v_decide_1290_; 
v_decide_1290_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1284_, v_rhs_1287_);
if (v_decide_1290_ == 0)
{
return v___x_1204_;
}
else
{
return v___x_1288_;
}
}
}
}
else
{
return v___x_1204_;
}
}
}
}
else
{
return v___x_1204_;
}
}
}
v___jp_1291_:
{
switch(lean_obj_tag(v_r_1201_))
{
case 0:
{
uint64_t v_hashCode_1293_; 
v_hashCode_1293_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*2);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1293_;
goto v___jp_1205_;
}
case 1:
{
uint64_t v_hashCode_1294_; 
v_hashCode_1294_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*2);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1294_;
goto v___jp_1205_;
}
case 3:
{
uint64_t v_hashCode_1295_; 
v_hashCode_1295_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*3);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1295_;
goto v___jp_1205_;
}
case 4:
{
uint64_t v_hashCode_1296_; 
v_hashCode_1296_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*3);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1296_;
goto v___jp_1205_;
}
case 5:
{
uint64_t v_hashCode_1297_; 
v_hashCode_1297_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*5);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1297_;
goto v___jp_1205_;
}
default: 
{
uint64_t v_hashCode_1298_; 
v_hashCode_1298_ = lean_ctor_get_uint64(v_r_1201_, sizeof(void*)*4);
v___y_1206_ = v___y_1292_;
v___y_1207_ = v_hashCode_1298_;
goto v___jp_1205_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_1200_ = stack[0].m_obj;
lean_object* v_r_1201_ = stack[1].m_obj;
uint8_t v_res_1305_;
v_res_1305_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1200_, v_r_1201_);
stack->m_num = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1306_, lean_object* v_r_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1306_, v_r_1307_);
lean_dec_ref(v_r_1307_);
lean_dec_ref(v_l_1306_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1310_, lean_object* v_l_1311_, lean_object* v_r_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1311_, v_r_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1310_ = stack[0].m_obj;
lean_object* v_l_1311_ = stack[1].m_obj;
lean_object* v_r_1312_ = stack[2].m_obj;
uint8_t v_res_1314_;
v_res_1314_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1310_, v_l_1311_, v_r_1312_);
stack->m_num = v_res_1314_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1315_, lean_object* v_l_1316_, lean_object* v_r_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1315_, v_l_1316_, v_r_1317_);
lean_dec_ref(v_r_1317_);
lean_dec_ref(v_l_1316_);
lean_dec(v_w_1315_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1329_, lean_object* v_x_1330_){
_start:
{
switch(lean_obj_tag(v_x_1330_))
{
case 0:
{
lean_object* v_idx_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v_w_1329_);
v_idx_1331_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_idx_1331_);
lean_dec_ref_known(v_x_1330_, 2);
v___x_1332_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1333_ = l_Nat_reprFast(v_idx_1331_);
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
lean_dec_ref(v___x_1333_);
return v___x_1334_;
}
case 1:
{
lean_object* v_val_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_val_1335_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_x_1330_, 2);
v___x_1336_ = l_BitVec_repr(v_w_1329_, v_val_1335_);
v___x_1337_ = l_Std_Format_defWidth;
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = l_Std_Format_pretty(v___x_1336_, v___x_1337_, v___x_1338_, v___x_1338_);
return v___x_1339_;
}
case 2:
{
lean_object* v_w_1340_; lean_object* v_start_1341_; lean_object* v_expr_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_w_1340_ = lean_ctor_get(v_x_1330_, 0);
lean_inc(v_w_1340_);
v_start_1341_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_start_1341_);
v_expr_1342_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_expr_1342_);
lean_dec_ref_known(v_x_1330_, 4);
v___x_1343_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1340_, v_expr_1342_);
v___x_1344_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
v___x_1346_ = l_Nat_reprFast(v_start_1341_);
v___x_1347_ = lean_string_append(v___x_1345_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
v___x_1350_ = l_Nat_reprFast(v_w_1329_);
v___x_1351_ = lean_string_append(v___x_1349_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
return v___x_1353_;
}
case 3:
{
lean_object* v_lhs_1354_; uint8_t v_op_1355_; lean_object* v_rhs_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_lhs_1354_ = lean_ctor_get(v_x_1330_, 1);
lean_inc_ref(v_lhs_1354_);
v_op_1355_ = lean_ctor_get_uint8(v_x_1330_, sizeof(void*)*3 + 8);
v_rhs_1356_ = lean_ctor_get(v_x_1330_, 2);
lean_inc_ref(v_rhs_1356_);
lean_dec_ref_known(v_x_1330_, 3);
v___x_1357_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1329_);
v___x_1358_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_lhs_1354_);
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
v___x_1362_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1355_);
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = lean_string_append(v___x_1363_, v___x_1360_);
v___x_1365_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_rhs_1356_);
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
return v___x_1368_;
}
case 4:
{
lean_object* v_op_1369_; lean_object* v_operand_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_op_1369_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_op_1369_);
v_operand_1370_ = lean_ctor_get(v_x_1330_, 2);
lean_inc_ref(v_operand_1370_);
lean_dec_ref_known(v_x_1330_, 3);
v___x_1371_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1372_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1369_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v___x_1376_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_operand_1370_);
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
return v___x_1379_;
}
case 5:
{
lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v_lhs_1382_; lean_object* v_rhs_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v_w_1329_);
v_l_1380_ = lean_ctor_get(v_x_1330_, 0);
lean_inc(v_l_1380_);
v_r_1381_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_r_1381_);
v_lhs_1382_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_lhs_1382_);
v_rhs_1383_ = lean_ctor_get(v_x_1330_, 4);
lean_inc_ref(v_rhs_1383_);
lean_dec_ref_known(v_x_1330_, 5);
v___x_1384_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1385_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1380_, v_lhs_1382_);
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
v___x_1389_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1381_, v_rhs_1383_);
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
return v___x_1392_;
}
case 6:
{
lean_object* v_w_1393_; lean_object* v_n_1394_; lean_object* v_expr_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_w_1329_);
v_w_1393_ = lean_ctor_get(v_x_1330_, 0);
lean_inc(v_w_1393_);
v_n_1394_ = lean_ctor_get(v_x_1330_, 2);
lean_inc(v_n_1394_);
v_expr_1395_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_expr_1395_);
lean_dec_ref_known(v_x_1330_, 4);
v___x_1396_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1397_ = l_Nat_reprFast(v_n_1394_);
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
v___x_1401_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1393_, v_expr_1395_);
v___x_1402_ = lean_string_append(v___x_1400_, v___x_1401_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
return v___x_1404_;
}
case 7:
{
lean_object* v_n_1405_; lean_object* v_lhs_1406_; lean_object* v_rhs_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_n_1405_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_n_1405_);
v_lhs_1406_ = lean_ctor_get(v_x_1330_, 2);
lean_inc_ref(v_lhs_1406_);
v_rhs_1407_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_rhs_1407_);
lean_dec_ref_known(v_x_1330_, 4);
v___x_1408_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1409_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_lhs_1406_);
v___x_1410_ = lean_string_append(v___x_1408_, v___x_1409_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1412_ = lean_string_append(v___x_1410_, v___x_1411_);
v___x_1413_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1405_, v_rhs_1407_);
v___x_1414_ = lean_string_append(v___x_1412_, v___x_1413_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1416_ = lean_string_append(v___x_1414_, v___x_1415_);
return v___x_1416_;
}
case 8:
{
lean_object* v_n_1417_; lean_object* v_lhs_1418_; lean_object* v_rhs_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_n_1417_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_n_1417_);
v_lhs_1418_ = lean_ctor_get(v_x_1330_, 2);
lean_inc_ref(v_lhs_1418_);
v_rhs_1419_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_rhs_1419_);
lean_dec_ref_known(v_x_1330_, 4);
v___x_1420_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1421_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_lhs_1418_);
v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v___x_1425_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1417_, v_rhs_1419_);
v___x_1426_ = lean_string_append(v___x_1424_, v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
return v___x_1428_;
}
default: 
{
lean_object* v_n_1429_; lean_object* v_lhs_1430_; lean_object* v_rhs_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_n_1429_ = lean_ctor_get(v_x_1330_, 1);
lean_inc(v_n_1429_);
v_lhs_1430_ = lean_ctor_get(v_x_1330_, 2);
lean_inc_ref(v_lhs_1430_);
v_rhs_1431_ = lean_ctor_get(v_x_1330_, 3);
lean_inc_ref(v_rhs_1431_);
lean_dec_ref_known(v_x_1330_, 4);
v___x_1432_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1433_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1329_, v_lhs_1430_);
v___x_1434_ = lean_string_append(v___x_1432_, v___x_1433_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1436_ = lean_string_append(v___x_1434_, v___x_1435_);
v___x_1437_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1429_, v_rhs_1431_);
v___x_1438_ = lean_string_append(v___x_1436_, v___x_1437_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1440_ = lean_string_append(v___x_1438_, v___x_1439_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1442_, 0, v_w_1441_);
return v___x_1442_;
}
}
uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(lean_object* v_x_1447_){
_start:
{
lean_object* v_w_1448_; lean_object* v_bv_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; 
v_w_1448_ = lean_ctor_get(v_x_1447_, 0);
v_bv_1449_ = lean_ctor_get(v_x_1447_, 1);
v___x_1450_ = 0ULL;
v___x_1451_ = lean_uint64_of_nat(v_w_1448_);
v___x_1452_ = lean_uint64_mix_hash(v___x_1450_, v___x_1451_);
v___x_1453_ = l_BitVec_hash(v_w_1448_, v_bv_1449_);
v___x_1454_ = lean_uint64_mix_hash(v___x_1452_, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1447_ = stack[0].m_obj;
uint64_t v_res_1455_;
v_res_1455_ = l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(v_x_1447_);
stack->m_num = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash___boxed(lean_object* v_x_1456_){
_start:
{
uint64_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(v_x_1456_);
lean_dec_ref(v_x_1456_);
v_r_1458_ = lean_box_uint64(v_res_1457_);
return v_r_1458_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_w_1463_; lean_object* v_bv_1464_; lean_object* v_w_1465_; lean_object* v_bv_1466_; uint8_t v___x_1467_; 
v_w_1463_ = lean_ctor_get(v_x_1461_, 0);
v_bv_1464_ = lean_ctor_get(v_x_1461_, 1);
v_w_1465_ = lean_ctor_get(v_x_1462_, 0);
v_bv_1466_ = lean_ctor_get(v_x_1462_, 1);
v___x_1467_ = lean_nat_dec_eq(v_w_1463_, v_w_1465_);
if (v___x_1467_ == 0)
{
return v___x_1467_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_eq(v_bv_1464_, v_bv_1466_);
return v___x_1468_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1461_ = stack[0].m_obj;
lean_object* v_x_1462_ = stack[1].m_obj;
uint8_t v_res_1469_;
v_res_1469_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_x_1461_, v_x_1462_);
stack->m_num = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq___boxed(lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_res_1472_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_x_1470_, v_x_1471_);
lean_dec_ref(v_x_1471_);
lean_dec_ref(v_x_1470_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_x_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1474_ = stack[0].m_obj;
lean_object* v_x_1475_ = stack[1].m_obj;
uint8_t v_res_1477_;
v_res_1477_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(v_x_1474_, v_x_1475_);
stack->m_num = v_res_1477_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec___boxed(lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(v_x_1478_, v_x_1479_);
lean_dec_ref(v_x_1479_);
lean_dec_ref(v_x_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1482_, lean_object* v_idx_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_RArray_getImpl___redArg(v_assign_1482_, v_idx_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1485_, lean_object* v_idx_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1485_, v_idx_1486_);
lean_dec(v_idx_1486_);
lean_dec_ref(v_assign_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1488_, lean_object* v_assign_1489_, lean_object* v_x_1490_){
_start:
{
switch(lean_obj_tag(v_x_1490_))
{
case 0:
{
lean_object* v_idx_1491_; lean_object* v_packedBv_1492_; lean_object* v_w_1493_; lean_object* v_bv_1494_; uint8_t v___x_1495_; 
v_idx_1491_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_idx_1491_);
lean_dec_ref_known(v_x_1490_, 2);
v_packedBv_1492_ = l_Lean_RArray_getImpl___redArg(v_assign_1489_, v_idx_1491_);
lean_dec(v_idx_1491_);
v_w_1493_ = lean_ctor_get(v_packedBv_1492_, 0);
lean_inc(v_w_1493_);
v_bv_1494_ = lean_ctor_get(v_packedBv_1492_, 1);
lean_inc(v_bv_1494_);
lean_dec(v_packedBv_1492_);
v___x_1495_ = lean_nat_dec_eq(v_w_1493_, v_w_1488_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = l_BitVec_setWidth(v_w_1493_, v_w_1488_, v_bv_1494_);
lean_dec(v_bv_1494_);
lean_dec(v_w_1488_);
lean_dec(v_w_1493_);
return v___x_1496_;
}
else
{
lean_dec(v_w_1493_);
lean_dec(v_w_1488_);
return v_bv_1494_;
}
}
case 1:
{
lean_object* v_val_1497_; 
lean_dec(v_w_1488_);
v_val_1497_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_val_1497_);
lean_dec_ref_known(v_x_1490_, 2);
return v_val_1497_;
}
case 2:
{
lean_object* v_w_1498_; lean_object* v_start_1499_; lean_object* v_expr_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_w_1498_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_w_1498_);
v_start_1499_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_start_1499_);
v_expr_1500_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_expr_1500_);
lean_dec_ref_known(v_x_1490_, 4);
v___x_1501_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1498_, v_assign_1489_, v_expr_1500_);
v___x_1502_ = l_BitVec_extractLsb_x27___redArg(v_start_1499_, v_w_1488_, v___x_1501_);
lean_dec(v___x_1501_);
lean_dec(v_w_1488_);
lean_dec(v_start_1499_);
return v___x_1502_;
}
case 3:
{
lean_object* v_lhs_1503_; uint8_t v_op_1504_; lean_object* v_rhs_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_lhs_1503_ = lean_ctor_get(v_x_1490_, 1);
lean_inc_ref(v_lhs_1503_);
v_op_1504_ = lean_ctor_get_uint8(v_x_1490_, sizeof(void*)*3 + 8);
v_rhs_1505_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_rhs_1505_);
lean_dec_ref_known(v_x_1490_, 3);
lean_inc_n(v_w_1488_, 2);
v___x_1506_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_lhs_1503_);
v___x_1507_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_rhs_1505_);
v___x_1508_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1488_, v_op_1504_, v___x_1506_, v___x_1507_);
lean_dec(v___x_1507_);
lean_dec(v___x_1506_);
lean_dec(v_w_1488_);
return v___x_1508_;
}
case 4:
{
lean_object* v_op_1509_; lean_object* v_operand_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_op_1509_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_op_1509_);
v_operand_1510_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_operand_1510_);
lean_dec_ref_known(v_x_1490_, 3);
lean_inc(v_w_1488_);
v___x_1511_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_operand_1510_);
v___x_1512_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1488_, v_op_1509_, v___x_1511_);
lean_dec(v_op_1509_);
return v___x_1512_;
}
case 5:
{
lean_object* v_l_1513_; lean_object* v_r_1514_; lean_object* v_lhs_1515_; lean_object* v_rhs_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_w_1488_);
v_l_1513_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_l_1513_);
v_r_1514_ = lean_ctor_get(v_x_1490_, 1);
lean_inc_n(v_r_1514_, 2);
v_lhs_1515_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_lhs_1515_);
v_rhs_1516_ = lean_ctor_get(v_x_1490_, 4);
lean_inc_ref(v_rhs_1516_);
lean_dec_ref_known(v_x_1490_, 5);
v___x_1517_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1513_, v_assign_1489_, v_lhs_1515_);
v___x_1518_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1514_, v_assign_1489_, v_rhs_1516_);
v___x_1519_ = l_BitVec_append___redArg(v_r_1514_, v___x_1517_, v___x_1518_);
lean_dec(v___x_1518_);
lean_dec(v___x_1517_);
lean_dec(v_r_1514_);
return v___x_1519_;
}
case 6:
{
lean_object* v_w_1520_; lean_object* v_n_1521_; lean_object* v_expr_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_w_1488_);
v_w_1520_ = lean_ctor_get(v_x_1490_, 0);
lean_inc_n(v_w_1520_, 2);
v_n_1521_ = lean_ctor_get(v_x_1490_, 2);
lean_inc(v_n_1521_);
v_expr_1522_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_expr_1522_);
lean_dec_ref_known(v_x_1490_, 4);
v___x_1523_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1520_, v_assign_1489_, v_expr_1522_);
v___x_1524_ = l_BitVec_replicate(v_w_1520_, v_n_1521_, v___x_1523_);
lean_dec(v___x_1523_);
lean_dec(v_n_1521_);
lean_dec(v_w_1520_);
return v___x_1524_;
}
case 7:
{
lean_object* v_n_1525_; lean_object* v_lhs_1526_; lean_object* v_rhs_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_n_1525_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_n_1525_);
v_lhs_1526_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_lhs_1526_);
v_rhs_1527_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_rhs_1527_);
lean_dec_ref_known(v_x_1490_, 4);
lean_inc(v_w_1488_);
v___x_1528_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_lhs_1526_);
v___x_1529_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1525_, v_assign_1489_, v_rhs_1527_);
v___x_1530_ = l_BitVec_shiftLeft(v_w_1488_, v___x_1528_, v___x_1529_);
lean_dec(v___x_1529_);
lean_dec(v___x_1528_);
lean_dec(v_w_1488_);
return v___x_1530_;
}
case 8:
{
lean_object* v_n_1531_; lean_object* v_lhs_1532_; lean_object* v_rhs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_n_1531_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_n_1531_);
v_lhs_1532_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_lhs_1532_);
v_rhs_1533_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_rhs_1533_);
lean_dec_ref_known(v_x_1490_, 4);
v___x_1534_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_lhs_1532_);
v___x_1535_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1531_, v_assign_1489_, v_rhs_1533_);
v___x_1536_ = lean_nat_shiftr(v___x_1534_, v___x_1535_);
lean_dec(v___x_1535_);
lean_dec(v___x_1534_);
return v___x_1536_;
}
default: 
{
lean_object* v_n_1537_; lean_object* v_lhs_1538_; lean_object* v_rhs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_n_1537_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_n_1537_);
v_lhs_1538_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_lhs_1538_);
v_rhs_1539_ = lean_ctor_get(v_x_1490_, 3);
lean_inc_ref(v_rhs_1539_);
lean_dec_ref_known(v_x_1490_, 4);
lean_inc(v_w_1488_);
v___x_1540_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1489_, v_lhs_1538_);
v___x_1541_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1537_, v_assign_1489_, v_rhs_1539_);
v___x_1542_ = l_BitVec_sshiftRight(v_w_1488_, v___x_1540_, v___x_1541_);
lean_dec(v___x_1541_);
lean_dec(v_w_1488_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1543_, lean_object* v_assign_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1543_, v_assign_1544_, v_x_1545_);
lean_dec_ref(v_assign_1544_);
return v_res_1546_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(uint8_t v_x_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(v_x_1547_);
v___x_1549_ = lean_obj_tag_nat(v___x_1548_);
lean_dec(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1547_ = stack[0].m_num;
lean_object* v_res_1550_;
v_res_1550_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(v_x_1547_);
stack->m_obj
 = v_res_1550_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl___boxed(lean_object* v_x_1551_){
_start:
{
uint8_t v_x_4__boxed_1552_; lean_object* v_res_1553_; 
v_x_4__boxed_1552_ = lean_unbox(v_x_1551_);
v_res_1553_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(v_x_4__boxed_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1554_){
_start:
{
lean_inc(v_k_1554_);
return v_k_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1555_);
lean_dec(v_k_1555_);
return v_res_1556_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1557_, lean_object* v_ctorIdx_1558_, uint8_t v_t_1559_, lean_object* v_h_1560_, lean_object* v_k_1561_){
_start:
{
lean_inc(v_k_1561_);
return v_k_1561_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1558_ = stack[1].m_obj;
uint8_t v_t_1559_ = stack[2].m_num;
lean_object* v_k_1561_ = stack[4].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_box(0), v_ctorIdx_1558_, v_t_1559_, lean_box(0), v_k_1561_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1563_, lean_object* v_ctorIdx_1564_, lean_object* v_t_1565_, lean_object* v_h_1566_, lean_object* v_k_1567_){
_start:
{
uint8_t v_t_boxed_1568_; lean_object* v_res_1569_; 
v_t_boxed_1568_ = lean_unbox(v_t_1565_);
v_res_1569_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1563_, v_ctorIdx_1564_, v_t_boxed_1568_, v_h_1566_, v_k_1567_);
lean_dec(v_k_1567_);
lean_dec(v_ctorIdx_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1570_){
_start:
{
lean_inc(v_eq_1570_);
return v_eq_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1571_);
lean_dec(v_eq_1571_);
return v_res_1572_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1573_, uint8_t v_t_1574_, lean_object* v_h_1575_, lean_object* v_eq_1576_){
_start:
{
lean_inc(v_eq_1576_);
return v_eq_1576_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_eq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1574_ = stack[1].m_num;
lean_object* v_eq_1576_ = stack[3].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_box(0), v_t_1574_, lean_box(0), v_eq_1576_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1578_, lean_object* v_t_1579_, lean_object* v_h_1580_, lean_object* v_eq_1581_){
_start:
{
uint8_t v_t_boxed_1582_; lean_object* v_res_1583_; 
v_t_boxed_1582_ = lean_unbox(v_t_1579_);
v_res_1583_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1578_, v_t_boxed_1582_, v_h_1580_, v_eq_1581_);
lean_dec(v_eq_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1584_){
_start:
{
lean_inc(v_ult_1584_);
return v_ult_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1585_);
lean_dec(v_ult_1585_);
return v_res_1586_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1587_, uint8_t v_t_1588_, lean_object* v_h_1589_, lean_object* v_ult_1590_){
_start:
{
lean_inc(v_ult_1590_);
return v_ult_1590_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_ult_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1588_ = stack[1].m_num;
lean_object* v_ult_1590_ = stack[3].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_box(0), v_t_1588_, lean_box(0), v_ult_1590_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1592_, lean_object* v_t_1593_, lean_object* v_h_1594_, lean_object* v_ult_1595_){
_start:
{
uint8_t v_t_boxed_1596_; lean_object* v_res_1597_; 
v_t_boxed_1596_ = lean_unbox(v_t_1593_);
v_res_1597_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1592_, v_t_boxed_1596_, v_h_1594_, v_ult_1595_);
lean_dec(v_ult_1595_);
return v_res_1597_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVBinPred_ofNat(lean_object* v_n_1598_){
_start:
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_nat_dec_le(v_n_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; 
v___x_1601_ = 1;
return v___x_1601_;
}
else
{
uint8_t v___x_1602_; 
v___x_1602_ = 0;
return v___x_1602_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1598_ = stack[0].m_obj;
uint8_t v_res_1603_;
v_res_1603_ = l_Std_Tactic_BVDecide_BVBinPred_ofNat(v_n_1598_);
stack->m_num = v_res_1603_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ofNat___boxed(lean_object* v_n_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_Tactic_BVDecide_BVBinPred_ofNat(v_n_1604_);
lean_dec(v_n_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(uint8_t v_x_1607_, uint8_t v_y_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1609_ = lean_box(v_x_1607_);
v___x_1610_ = lean_obj_tag_nat(v___x_1609_);
lean_dec(v___x_1609_);
v___x_1611_ = lean_box(v_y_1608_);
v___x_1612_ = lean_obj_tag_nat(v___x_1611_);
lean_dec(v___x_1611_);
v___x_1613_ = lean_nat_dec_eq(v___x_1610_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVBinPred_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1607_ = stack[0].m_num;
uint8_t v_y_1608_ = stack[1].m_num;
uint8_t v_res_1614_;
v_res_1614_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(v_x_1607_, v_y_1608_);
stack->m_num = v_res_1614_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinPred___boxed(lean_object* v_x_1615_, lean_object* v_y_1616_){
_start:
{
uint8_t v_x_23__boxed_1617_; uint8_t v_y_24__boxed_1618_; uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_x_23__boxed_1617_ = lean_unbox(v_x_1615_);
v_y_24__boxed_1618_ = lean_unbox(v_y_1616_);
v_res_1619_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(v_x_23__boxed_1617_, v_y_24__boxed_1618_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(uint8_t v_x_1621_){
_start:
{
if (v_x_1621_ == 0)
{
uint64_t v___x_1622_; 
v___x_1622_ = 0ULL;
return v___x_1622_;
}
else
{
uint64_t v___x_1623_; 
v___x_1623_ = 1ULL;
return v___x_1623_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBVBinPred_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1621_ = stack[0].m_num;
uint64_t v_res_1624_;
v_res_1624_ = l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(v_x_1621_);
stack->m_num = v_res_1624_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinPred_hash___boxed(lean_object* v_x_1625_){
_start:
{
uint8_t v_x_28__boxed_1626_; uint64_t v_res_1627_; lean_object* v_r_1628_; 
v_x_28__boxed_1626_ = lean_unbox(v_x_1625_);
v_res_1627_ = l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(v_x_28__boxed_1626_);
v_r_1628_ = lean_box_uint64(v_res_1627_);
return v_r_1628_;
}
}
lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1633_){
_start:
{
if (v_x_1633_ == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1635_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1633_ = stack[0].m_num;
lean_object* v_res_1636_;
v_res_1636_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_1633_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1637_){
_start:
{
uint8_t v_x_22__boxed_1638_; lean_object* v_res_1639_; 
v_x_22__boxed_1638_ = lean_unbox(v_x_1637_);
v_res_1639_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1638_);
return v_res_1639_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
if (v_x_1642_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_eq(v_a_1643_, v_a_1644_);
return v___x_1645_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_nat_dec_lt(v_a_1643_, v_a_1644_);
return v___x_1646_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_eval___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1642_ = stack[0].m_num;
lean_object* v_a_1643_ = stack[1].m_obj;
lean_object* v_a_1644_ = stack[2].m_obj;
uint8_t v_res_1647_;
v_res_1647_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1642_, v_a_1643_, v_a_1644_);
stack->m_num = v_res_1647_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
uint8_t v_x_70__boxed_1651_; uint8_t v_res_1652_; lean_object* v_r_1653_; 
v_x_70__boxed_1651_ = lean_unbox(v_x_1648_);
v_res_1652_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_70__boxed_1651_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
v_r_1653_ = lean_box(v_res_1652_);
return v_r_1653_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1654_, uint8_t v_x_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
uint8_t v___x_1658_; 
v___x_1658_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1655_, v_a_1656_, v_a_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVBinPred_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1654_ = stack[0].m_obj;
uint8_t v_x_1655_ = stack[1].m_num;
lean_object* v_a_1656_ = stack[2].m_obj;
lean_object* v_a_1657_ = stack[3].m_obj;
uint8_t v_res_1659_;
v_res_1659_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1654_, v_x_1655_, v_a_1656_, v_a_1657_);
stack->m_num = v_res_1659_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1660_, lean_object* v_x_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
uint8_t v_x_91__boxed_1664_; uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_x_91__boxed_1664_ = lean_unbox(v_x_1661_);
v_res_1665_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1660_, v_x_91__boxed_1664_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_w_1660_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl(lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_tag_nat(v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl___boxed(lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl(v_x_1669_);
lean_dec_ref(v_x_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1671_, lean_object* v_k_1672_){
_start:
{
if (lean_obj_tag(v_t_1671_) == 0)
{
lean_object* v_w_1673_; lean_object* v_lhs_1674_; uint8_t v_op_1675_; lean_object* v_rhs_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_w_1673_ = lean_ctor_get(v_t_1671_, 0);
lean_inc(v_w_1673_);
v_lhs_1674_ = lean_ctor_get(v_t_1671_, 1);
lean_inc_ref(v_lhs_1674_);
v_op_1675_ = lean_ctor_get_uint8(v_t_1671_, sizeof(void*)*3);
v_rhs_1676_ = lean_ctor_get(v_t_1671_, 2);
lean_inc_ref(v_rhs_1676_);
lean_dec_ref_known(v_t_1671_, 3);
v___x_1677_ = lean_box(v_op_1675_);
v___x_1678_ = lean_apply_4(v_k_1672_, v_w_1673_, v_lhs_1674_, v___x_1677_, v_rhs_1676_);
return v___x_1678_;
}
else
{
lean_object* v_w_1679_; lean_object* v_expr_1680_; lean_object* v_idx_1681_; lean_object* v___x_1682_; 
v_w_1679_ = lean_ctor_get(v_t_1671_, 0);
lean_inc(v_w_1679_);
v_expr_1680_ = lean_ctor_get(v_t_1671_, 1);
lean_inc_ref(v_expr_1680_);
v_idx_1681_ = lean_ctor_get(v_t_1671_, 2);
lean_inc(v_idx_1681_);
lean_dec_ref_known(v_t_1671_, 3);
v___x_1682_ = lean_apply_3(v_k_1672_, v_w_1679_, v_expr_1680_, v_idx_1681_);
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1683_, lean_object* v_ctorIdx_1684_, lean_object* v_t_1685_, lean_object* v_h_1686_, lean_object* v_k_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1685_, v_k_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1689_, lean_object* v_ctorIdx_1690_, lean_object* v_t_1691_, lean_object* v_h_1692_, lean_object* v_k_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1689_, v_ctorIdx_1690_, v_t_1691_, v_h_1692_, v_k_1693_);
lean_dec(v_ctorIdx_1690_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1695_, lean_object* v_bin_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1695_, v_bin_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1698_, lean_object* v_t_1699_, lean_object* v_h_1700_, lean_object* v_bin_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1699_, v_bin_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1703_, lean_object* v_getLsbD_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1703_, v_getLsbD_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1706_, lean_object* v_t_1707_, lean_object* v_h_1708_, lean_object* v_getLsbD_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1707_, v_getLsbD_1709_);
return v___x_1710_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(lean_object* v_x_1711_, lean_object* v_x_1712_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
if (lean_obj_tag(v_x_1712_) == 0)
{
lean_object* v_w_1713_; lean_object* v_lhs_1714_; uint8_t v_op_1715_; lean_object* v_rhs_1716_; lean_object* v_w_1717_; lean_object* v_lhs_1718_; uint8_t v_op_1719_; lean_object* v_rhs_1720_; uint8_t v___x_1721_; 
v_w_1713_ = lean_ctor_get(v_x_1711_, 0);
v_lhs_1714_ = lean_ctor_get(v_x_1711_, 1);
v_op_1715_ = lean_ctor_get_uint8(v_x_1711_, sizeof(void*)*3);
v_rhs_1716_ = lean_ctor_get(v_x_1711_, 2);
v_w_1717_ = lean_ctor_get(v_x_1712_, 0);
v_lhs_1718_ = lean_ctor_get(v_x_1712_, 1);
v_op_1719_ = lean_ctor_get_uint8(v_x_1712_, sizeof(void*)*3);
v_rhs_1720_ = lean_ctor_get(v_x_1712_, 2);
v___x_1721_ = lean_nat_dec_eq(v_w_1713_, v_w_1717_);
if (v___x_1721_ == 0)
{
return v___x_1721_;
}
else
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1714_, v_lhs_1718_);
if (v___x_1722_ == 0)
{
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1723_ = lean_box(v_op_1715_);
v___x_1724_ = lean_obj_tag_nat(v___x_1723_);
lean_dec(v___x_1723_);
v___x_1725_ = lean_box(v_op_1719_);
v___x_1726_ = lean_obj_tag_nat(v___x_1725_);
lean_dec(v___x_1725_);
v___x_1727_ = lean_nat_dec_eq(v___x_1724_, v___x_1726_);
if (v___x_1727_ == 0)
{
return v___x_1727_;
}
else
{
uint8_t v___x_1728_; 
v___x_1728_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1716_, v_rhs_1720_);
return v___x_1728_;
}
}
}
}
else
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
return v___x_1729_;
}
}
else
{
if (lean_obj_tag(v_x_1712_) == 0)
{
uint8_t v___x_1730_; 
v___x_1730_ = 0;
return v___x_1730_;
}
else
{
lean_object* v_w_1731_; lean_object* v_expr_1732_; lean_object* v_idx_1733_; lean_object* v_w_1734_; lean_object* v_expr_1735_; lean_object* v_idx_1736_; uint8_t v___x_1737_; 
v_w_1731_ = lean_ctor_get(v_x_1711_, 0);
v_expr_1732_ = lean_ctor_get(v_x_1711_, 1);
v_idx_1733_ = lean_ctor_get(v_x_1711_, 2);
v_w_1734_ = lean_ctor_get(v_x_1712_, 0);
v_expr_1735_ = lean_ctor_get(v_x_1712_, 1);
v_idx_1736_ = lean_ctor_get(v_x_1712_, 2);
v___x_1737_ = lean_nat_dec_eq(v_w_1731_, v_w_1734_);
if (v___x_1737_ == 0)
{
return v___x_1737_;
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1732_, v_expr_1735_);
if (v___x_1738_ == 0)
{
return v___x_1738_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_nat_dec_eq(v_idx_1733_, v_idx_1736_);
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1711_ = stack[0].m_obj;
lean_object* v_x_1712_ = stack[1].m_obj;
uint8_t v_res_1740_;
v_res_1740_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(v_x_1711_, v_x_1712_);
stack->m_num = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq___boxed(lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(v_x_1741_, v_x_1742_);
lean_dec_ref(v_x_1742_);
lean_dec_ref(v_x_1741_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred(lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(v_x_1745_, v_x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instDecidableEqBVPred_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1745_ = stack[0].m_obj;
lean_object* v_x_1746_ = stack[1].m_obj;
uint8_t v_res_1748_;
v_res_1748_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred(v_x_1745_, v_x_1746_);
stack->m_num = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred___boxed(lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
uint8_t v_res_1751_; lean_object* v_r_1752_; 
v_res_1751_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred(v_x_1749_, v_x_1750_);
lean_dec_ref(v_x_1750_);
lean_dec_ref(v_x_1749_);
v_r_1752_ = lean_box(v_res_1751_);
return v_r_1752_;
}
}
uint64_t l_Std_Tactic_BVDecide_instHashableBVPred_hash(lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v_w_1754_; lean_object* v_lhs_1755_; uint8_t v_op_1756_; lean_object* v_rhs_1757_; uint64_t v___x_1758_; uint64_t v___x_1759_; uint64_t v___x_1760_; uint64_t v___y_1762_; 
v_w_1754_ = lean_ctor_get(v_x_1753_, 0);
v_lhs_1755_ = lean_ctor_get(v_x_1753_, 1);
v_op_1756_ = lean_ctor_get_uint8(v_x_1753_, sizeof(void*)*3);
v_rhs_1757_ = lean_ctor_get(v_x_1753_, 2);
v___x_1758_ = 0ULL;
v___x_1759_ = lean_uint64_of_nat(v_w_1754_);
v___x_1760_ = lean_uint64_mix_hash(v___x_1758_, v___x_1759_);
switch(lean_obj_tag(v_lhs_1755_))
{
case 0:
{
uint64_t v_hashCode_1778_; 
v_hashCode_1778_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*2);
v___y_1762_ = v_hashCode_1778_;
goto v___jp_1761_;
}
case 1:
{
uint64_t v_hashCode_1779_; 
v_hashCode_1779_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*2);
v___y_1762_ = v_hashCode_1779_;
goto v___jp_1761_;
}
case 3:
{
uint64_t v_hashCode_1780_; 
v_hashCode_1780_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*3);
v___y_1762_ = v_hashCode_1780_;
goto v___jp_1761_;
}
case 4:
{
uint64_t v_hashCode_1781_; 
v_hashCode_1781_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*3);
v___y_1762_ = v_hashCode_1781_;
goto v___jp_1761_;
}
case 5:
{
uint64_t v_hashCode_1782_; 
v_hashCode_1782_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*5);
v___y_1762_ = v_hashCode_1782_;
goto v___jp_1761_;
}
default: 
{
uint64_t v_hashCode_1783_; 
v_hashCode_1783_ = lean_ctor_get_uint64(v_lhs_1755_, sizeof(void*)*4);
v___y_1762_ = v_hashCode_1783_;
goto v___jp_1761_;
}
}
v___jp_1761_:
{
uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; 
v___x_1763_ = lean_uint64_mix_hash(v___x_1760_, v___y_1762_);
v___x_1764_ = l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(v_op_1756_);
v___x_1765_ = lean_uint64_mix_hash(v___x_1763_, v___x_1764_);
switch(lean_obj_tag(v_rhs_1757_))
{
case 0:
{
uint64_t v_hashCode_1766_; uint64_t v___x_1767_; 
v_hashCode_1766_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*2);
v___x_1767_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1766_);
return v___x_1767_;
}
case 1:
{
uint64_t v_hashCode_1768_; uint64_t v___x_1769_; 
v_hashCode_1768_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*2);
v___x_1769_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1768_);
return v___x_1769_;
}
case 3:
{
uint64_t v_hashCode_1770_; uint64_t v___x_1771_; 
v_hashCode_1770_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*3);
v___x_1771_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1770_);
return v___x_1771_;
}
case 4:
{
uint64_t v_hashCode_1772_; uint64_t v___x_1773_; 
v_hashCode_1772_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*3);
v___x_1773_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1772_);
return v___x_1773_;
}
case 5:
{
uint64_t v_hashCode_1774_; uint64_t v___x_1775_; 
v_hashCode_1774_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*5);
v___x_1775_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1774_);
return v___x_1775_;
}
default: 
{
uint64_t v_hashCode_1776_; uint64_t v___x_1777_; 
v_hashCode_1776_ = lean_ctor_get_uint64(v_rhs_1757_, sizeof(void*)*4);
v___x_1777_ = lean_uint64_mix_hash(v___x_1765_, v_hashCode_1776_);
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_w_1784_; lean_object* v_expr_1785_; lean_object* v_idx_1786_; uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; uint64_t v___y_1791_; 
v_w_1784_ = lean_ctor_get(v_x_1753_, 0);
v_expr_1785_ = lean_ctor_get(v_x_1753_, 1);
v_idx_1786_ = lean_ctor_get(v_x_1753_, 2);
v___x_1787_ = 1ULL;
v___x_1788_ = lean_uint64_of_nat(v_w_1784_);
v___x_1789_ = lean_uint64_mix_hash(v___x_1787_, v___x_1788_);
switch(lean_obj_tag(v_expr_1785_))
{
case 0:
{
uint64_t v_hashCode_1795_; 
v_hashCode_1795_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*2);
v___y_1791_ = v_hashCode_1795_;
goto v___jp_1790_;
}
case 1:
{
uint64_t v_hashCode_1796_; 
v_hashCode_1796_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*2);
v___y_1791_ = v_hashCode_1796_;
goto v___jp_1790_;
}
case 3:
{
uint64_t v_hashCode_1797_; 
v_hashCode_1797_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*3);
v___y_1791_ = v_hashCode_1797_;
goto v___jp_1790_;
}
case 4:
{
uint64_t v_hashCode_1798_; 
v_hashCode_1798_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*3);
v___y_1791_ = v_hashCode_1798_;
goto v___jp_1790_;
}
case 5:
{
uint64_t v_hashCode_1799_; 
v_hashCode_1799_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*5);
v___y_1791_ = v_hashCode_1799_;
goto v___jp_1790_;
}
default: 
{
uint64_t v_hashCode_1800_; 
v_hashCode_1800_ = lean_ctor_get_uint64(v_expr_1785_, sizeof(void*)*4);
v___y_1791_ = v_hashCode_1800_;
goto v___jp_1790_;
}
}
v___jp_1790_:
{
uint64_t v___x_1792_; uint64_t v___x_1793_; uint64_t v___x_1794_; 
v___x_1792_ = lean_uint64_mix_hash(v___x_1789_, v___y_1791_);
v___x_1793_ = lean_uint64_of_nat(v_idx_1786_);
v___x_1794_ = lean_uint64_mix_hash(v___x_1792_, v___x_1793_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_instHashableBVPred_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1753_ = stack[0].m_obj;
uint64_t v_res_1801_;
v_res_1801_ = l_Std_Tactic_BVDecide_instHashableBVPred_hash(v_x_1753_);
stack->m_num = v_res_1801_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVPred_hash___boxed(lean_object* v_x_1802_){
_start:
{
uint64_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Std_Tactic_BVDecide_instHashableBVPred_hash(v_x_1802_);
lean_dec_ref(v_x_1802_);
v_r_1804_ = lean_box_uint64(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v_w_1808_; lean_object* v_lhs_1809_; uint8_t v_op_1810_; lean_object* v_rhs_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_w_1808_ = lean_ctor_get(v_x_1807_, 0);
lean_inc_n(v_w_1808_, 2);
v_lhs_1809_ = lean_ctor_get(v_x_1807_, 1);
lean_inc_ref(v_lhs_1809_);
v_op_1810_ = lean_ctor_get_uint8(v_x_1807_, sizeof(void*)*3);
v_rhs_1811_ = lean_ctor_get(v_x_1807_, 2);
lean_inc_ref(v_rhs_1811_);
lean_dec_ref_known(v_x_1807_, 3);
v___x_1812_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1813_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1808_, v_lhs_1809_);
v___x_1814_ = lean_string_append(v___x_1812_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1816_ = lean_string_append(v___x_1814_, v___x_1815_);
v___x_1817_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1810_);
v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = lean_string_append(v___x_1818_, v___x_1815_);
v___x_1820_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1808_, v_rhs_1811_);
v___x_1821_ = lean_string_append(v___x_1819_, v___x_1820_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1823_ = lean_string_append(v___x_1821_, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v_w_1824_; lean_object* v_expr_1825_; lean_object* v_idx_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_w_1824_ = lean_ctor_get(v_x_1807_, 0);
lean_inc(v_w_1824_);
v_expr_1825_ = lean_ctor_get(v_x_1807_, 1);
lean_inc_ref(v_expr_1825_);
v_idx_1826_ = lean_ctor_get(v_x_1807_, 2);
lean_inc(v_idx_1826_);
lean_dec_ref_known(v_x_1807_, 3);
v___x_1827_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1824_, v_expr_1825_);
v___x_1828_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1829_ = lean_string_append(v___x_1827_, v___x_1828_);
v___x_1830_ = l_Nat_reprFast(v_idx_1826_);
v___x_1831_ = lean_string_append(v___x_1829_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1833_ = lean_string_append(v___x_1831_, v___x_1832_);
return v___x_1833_;
}
}
}
uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1836_, lean_object* v_x_1837_){
_start:
{
if (lean_obj_tag(v_x_1837_) == 0)
{
lean_object* v_w_1838_; lean_object* v_lhs_1839_; uint8_t v_op_1840_; lean_object* v_rhs_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_w_1838_ = lean_ctor_get(v_x_1837_, 0);
lean_inc_n(v_w_1838_, 2);
v_lhs_1839_ = lean_ctor_get(v_x_1837_, 1);
lean_inc_ref(v_lhs_1839_);
v_op_1840_ = lean_ctor_get_uint8(v_x_1837_, sizeof(void*)*3);
v_rhs_1841_ = lean_ctor_get(v_x_1837_, 2);
lean_inc_ref(v_rhs_1841_);
lean_dec_ref_known(v_x_1837_, 3);
v___x_1842_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1838_, v_assign_1836_, v_lhs_1839_);
v___x_1843_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1838_, v_assign_1836_, v_rhs_1841_);
v___x_1844_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1840_, v___x_1842_, v___x_1843_);
lean_dec(v___x_1843_);
lean_dec(v___x_1842_);
return v___x_1844_;
}
else
{
lean_object* v_w_1845_; lean_object* v_expr_1846_; lean_object* v_idx_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_w_1845_ = lean_ctor_get(v_x_1837_, 0);
lean_inc(v_w_1845_);
v_expr_1846_ = lean_ctor_get(v_x_1837_, 1);
lean_inc_ref(v_expr_1846_);
v_idx_1847_ = lean_ctor_get(v_x_1837_, 2);
lean_inc(v_idx_1847_);
lean_dec_ref_known(v_x_1837_, 3);
v___x_1848_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1845_, v_assign_1836_, v_expr_1846_);
v___x_1849_ = l_Nat_testBit(v___x_1848_, v_idx_1847_);
lean_dec(v_idx_1847_);
lean_dec(v___x_1848_);
return v___x_1849_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVPred_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_1836_ = stack[0].m_obj;
lean_object* v_x_1837_ = stack[1].m_obj;
uint8_t v_res_1850_;
v_res_1850_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1836_, v_x_1837_);
stack->m_num = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1851_, v_x_1852_);
lean_dec_ref(v_assign_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_1855_ = stack[0].m_obj;
lean_object* v_x_1856_ = stack[1].m_obj;
uint8_t v_res_1858_;
v_res_1858_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1855_, v_x_1856_);
stack->m_num = v_res_1858_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1859_, v_x_1860_);
lean_dec_ref(v_assign_1859_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1863_, lean_object* v_expr_1864_){
_start:
{
lean_object* v___f_1865_; uint8_t v___x_1866_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1865_, 0, v_assign_1863_);
v___x_1866_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1865_, v_expr_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_BVLogicalExpr_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_assign_1863_ = stack[0].m_obj;
lean_object* v_expr_1864_ = stack[1].m_obj;
uint8_t v_res_1867_;
v_res_1867_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1863_, v_expr_1864_);
stack->m_num = v_res_1867_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1868_, lean_object* v_expr_1869_){
_start:
{
uint8_t v_res_1870_; lean_object* v_r_1871_; 
v_res_1870_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1868_, v_expr_1869_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
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
