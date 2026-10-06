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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(uint8_t v_x_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(v_x_148_);
v___x_150_ = lean_obj_tag_nat(v___x_149_);
lean_dec(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl___boxed(lean_object* v_x_151_){
_start:
{
uint8_t v_x_4__boxed_152_; lean_object* v_res_153_; 
v_x_4__boxed_152_ = lean_unbox(v_x_151_);
v_res_153_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___impl(v_x_4__boxed_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(lean_object* v_k_154_){
_start:
{
lean_inc(v_k_154_);
return v_k_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_155_);
lean_dec(v_k_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
lean_inc(v_k_161_);
return v_k_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(lean_object* v_motive_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
uint8_t v_t_boxed_167_; lean_object* v_res_168_; 
v_t_boxed_167_ = lean_unbox(v_t_164_);
v_res_168_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(v_motive_162_, v_ctorIdx_163_, v_t_boxed_167_, v_h_165_, v_k_166_);
lean_dec(v_k_166_);
lean_dec(v_ctorIdx_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(lean_object* v_and_169_){
_start:
{
lean_inc(v_and_169_);
return v_and_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(lean_object* v_and_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(v_and_170_);
lean_dec(v_and_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim(lean_object* v_motive_172_, uint8_t v_t_173_, lean_object* v_h_174_, lean_object* v_and_175_){
_start:
{
lean_inc(v_and_175_);
return v_and_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_and_179_){
_start:
{
uint8_t v_t_boxed_180_; lean_object* v_res_181_; 
v_t_boxed_180_ = lean_unbox(v_t_177_);
v_res_181_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(v_motive_176_, v_t_boxed_180_, v_h_178_, v_and_179_);
lean_dec(v_and_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(lean_object* v_or_182_){
_start:
{
lean_inc(v_or_182_);
return v_or_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(lean_object* v_or_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_183_);
lean_dec(v_or_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim(lean_object* v_motive_185_, uint8_t v_t_186_, lean_object* v_h_187_, lean_object* v_or_188_){
_start:
{
lean_inc(v_or_188_);
return v_or_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(lean_object* v_motive_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_or_192_){
_start:
{
uint8_t v_t_boxed_193_; lean_object* v_res_194_; 
v_t_boxed_193_ = lean_unbox(v_t_190_);
v_res_194_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(v_motive_189_, v_t_boxed_193_, v_h_191_, v_or_192_);
lean_dec(v_or_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(lean_object* v_xor_195_){
_start:
{
lean_inc(v_xor_195_);
return v_xor_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(lean_object* v_xor_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_196_);
lean_dec(v_xor_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim(lean_object* v_motive_198_, uint8_t v_t_199_, lean_object* v_h_200_, lean_object* v_xor_201_){
_start:
{
lean_inc(v_xor_201_);
return v_xor_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_xor_205_){
_start:
{
uint8_t v_t_boxed_206_; lean_object* v_res_207_; 
v_t_boxed_206_ = lean_unbox(v_t_203_);
v_res_207_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(v_motive_202_, v_t_boxed_206_, v_h_204_, v_xor_205_);
lean_dec(v_xor_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(lean_object* v_add_208_){
_start:
{
lean_inc(v_add_208_);
return v_add_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(lean_object* v_add_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_209_);
lean_dec(v_add_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim(lean_object* v_motive_211_, uint8_t v_t_212_, lean_object* v_h_213_, lean_object* v_add_214_){
_start:
{
lean_inc(v_add_214_);
return v_add_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(lean_object* v_motive_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_add_218_){
_start:
{
uint8_t v_t_boxed_219_; lean_object* v_res_220_; 
v_t_boxed_219_ = lean_unbox(v_t_216_);
v_res_220_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(v_motive_215_, v_t_boxed_219_, v_h_217_, v_add_218_);
lean_dec(v_add_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(lean_object* v_mul_221_){
_start:
{
lean_inc(v_mul_221_);
return v_mul_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(lean_object* v_mul_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(v_mul_222_);
lean_dec(v_mul_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim(lean_object* v_motive_224_, uint8_t v_t_225_, lean_object* v_h_226_, lean_object* v_mul_227_){
_start:
{
lean_inc(v_mul_227_);
return v_mul_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_mul_231_){
_start:
{
uint8_t v_t_boxed_232_; lean_object* v_res_233_; 
v_t_boxed_232_ = lean_unbox(v_t_229_);
v_res_233_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(v_motive_228_, v_t_boxed_232_, v_h_230_, v_mul_231_);
lean_dec(v_mul_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(lean_object* v_udiv_234_){
_start:
{
lean_inc(v_udiv_234_);
return v_udiv_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(lean_object* v_udiv_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_235_);
lean_dec(v_udiv_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(lean_object* v_motive_237_, uint8_t v_t_238_, lean_object* v_h_239_, lean_object* v_udiv_240_){
_start:
{
lean_inc(v_udiv_240_);
return v_udiv_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(lean_object* v_motive_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_udiv_244_){
_start:
{
uint8_t v_t_boxed_245_; lean_object* v_res_246_; 
v_t_boxed_245_ = lean_unbox(v_t_242_);
v_res_246_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(v_motive_241_, v_t_boxed_245_, v_h_243_, v_udiv_244_);
lean_dec(v_udiv_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(lean_object* v_umod_247_){
_start:
{
lean_inc(v_umod_247_);
return v_umod_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(lean_object* v_umod_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_248_);
lean_dec(v_umod_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim(lean_object* v_motive_250_, uint8_t v_t_251_, lean_object* v_h_252_, lean_object* v_umod_253_){
_start:
{
lean_inc(v_umod_253_);
return v_umod_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(lean_object* v_motive_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_umod_257_){
_start:
{
uint8_t v_t_boxed_258_; lean_object* v_res_259_; 
v_t_boxed_258_ = lean_unbox(v_t_255_);
v_res_259_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(v_motive_254_, v_t_boxed_258_, v_h_256_, v_umod_257_);
lean_dec(v_umod_257_);
return v_res_259_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(uint8_t v_x_260_){
_start:
{
switch(v_x_260_)
{
case 0:
{
uint64_t v___x_261_; 
v___x_261_ = 0ULL;
return v___x_261_;
}
case 1:
{
uint64_t v___x_262_; 
v___x_262_ = 1ULL;
return v___x_262_;
}
case 2:
{
uint64_t v___x_263_; 
v___x_263_ = 2ULL;
return v___x_263_;
}
case 3:
{
uint64_t v___x_264_; 
v___x_264_ = 3ULL;
return v___x_264_;
}
case 4:
{
uint64_t v___x_265_; 
v___x_265_ = 4ULL;
return v___x_265_;
}
case 5:
{
uint64_t v___x_266_; 
v___x_266_ = 5ULL;
return v___x_266_;
}
default: 
{
uint64_t v___x_267_; 
v___x_267_ = 6ULL;
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(lean_object* v_x_268_){
_start:
{
uint8_t v_x_88__boxed_269_; uint64_t v_res_270_; lean_object* v_r_271_; 
v_x_88__boxed_269_ = lean_unbox(v_x_268_);
v_res_270_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_269_);
v_r_271_ = lean_box_uint64(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* v_n_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(2u);
v___x_276_ = lean_nat_dec_le(v_n_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lean_nat_dec_le(v_n_274_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(5u);
v___x_280_ = lean_nat_dec_le(v_n_274_, v___x_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = 6;
return v___x_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = 5;
return v___x_282_;
}
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(3u);
v___x_284_ = lean_nat_dec_le(v_n_274_, v___x_283_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
v___x_285_ = 4;
return v___x_285_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 3;
return v___x_286_;
}
}
}
else
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_le(v_n_274_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_dec_le(v_n_274_, v___x_289_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 2;
return v___x_291_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = 1;
return v___x_292_;
}
}
else
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* v_n_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_294_);
lean_dec(v_n_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t v_x_297_, uint8_t v_y_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_299_ = lean_box(v_x_297_);
v___x_300_ = lean_obj_tag_nat(v___x_299_);
lean_dec(v___x_299_);
v___x_301_ = lean_box(v_y_298_);
v___x_302_ = lean_obj_tag_nat(v___x_301_);
lean_dec(v___x_301_);
v___x_303_ = lean_nat_dec_eq(v___x_300_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* v_x_304_, lean_object* v_y_305_){
_start:
{
uint8_t v_x_23__boxed_306_; uint8_t v_y_24__boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_x_23__boxed_306_ = lean_unbox(v_x_304_);
v_y_24__boxed_307_ = lean_unbox(v_y_305_);
v_res_308_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_23__boxed_306_, v_y_24__boxed_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t v_x_317_){
_start:
{
switch(v_x_317_)
{
case 0:
{
lean_object* v___x_318_; 
v___x_318_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0));
return v___x_318_;
}
case 1:
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1));
return v___x_319_;
}
case 2:
{
lean_object* v___x_320_; 
v___x_320_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2));
return v___x_320_;
}
case 3:
{
lean_object* v___x_321_; 
v___x_321_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3));
return v___x_321_;
}
case 4:
{
lean_object* v___x_322_; 
v___x_322_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4));
return v___x_322_;
}
case 5:
{
lean_object* v___x_323_; 
v___x_323_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5));
return v___x_323_;
}
default: 
{
lean_object* v___x_324_; 
v___x_324_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6));
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* v_x_325_){
_start:
{
uint8_t v_x_67__boxed_326_; lean_object* v_res_327_; 
v_x_67__boxed_326_ = lean_unbox(v_x_325_);
v_res_327_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* v_w_330_, uint8_t v_x_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
switch(v_x_331_)
{
case 0:
{
lean_object* v___x_334_; 
v___x_334_ = lean_nat_land(v_a_332_, v_a_333_);
return v___x_334_;
}
case 1:
{
lean_object* v___x_335_; 
v___x_335_ = lean_nat_lor(v_a_332_, v_a_333_);
return v___x_335_;
}
case 2:
{
lean_object* v___x_336_; 
v___x_336_ = lean_nat_lxor(v_a_332_, v_a_333_);
return v___x_336_;
}
case 3:
{
lean_object* v___x_337_; 
v___x_337_ = l_BitVec_add(v_w_330_, v_a_332_, v_a_333_);
return v___x_337_;
}
case 4:
{
lean_object* v___x_338_; 
v___x_338_ = l_BitVec_mul(v_w_330_, v_a_332_, v_a_333_);
return v___x_338_;
}
case 5:
{
lean_object* v___x_339_; 
v___x_339_ = lean_nat_div(v_a_332_, v_a_333_);
return v___x_339_;
}
default: 
{
lean_object* v___x_340_; 
v___x_340_ = lean_nat_mod(v_a_332_, v_a_333_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* v_w_341_, lean_object* v_x_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
uint8_t v_x_259__boxed_345_; lean_object* v_res_346_; 
v_x_259__boxed_345_ = lean_unbox(v_x_342_);
v_res_346_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_341_, v_x_259__boxed_345_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
lean_dec(v_w_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl(lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_tag_nat(v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl___boxed(lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___impl(v_x_349_);
lean_dec(v_x_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(lean_object* v_t_351_, lean_object* v_k_352_){
_start:
{
switch(lean_obj_tag(v_t_351_))
{
case 1:
{
lean_object* v_n_353_; lean_object* v___x_354_; 
v_n_353_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_n_353_);
lean_dec_ref_known(v_t_351_, 1);
v___x_354_ = lean_apply_1(v_k_352_, v_n_353_);
return v___x_354_;
}
case 2:
{
lean_object* v_n_355_; lean_object* v___x_356_; 
v_n_355_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_n_355_);
lean_dec_ref_known(v_t_351_, 1);
v___x_356_ = lean_apply_1(v_k_352_, v_n_355_);
return v___x_356_;
}
case 3:
{
lean_object* v_n_357_; lean_object* v___x_358_; 
v_n_357_ = lean_ctor_get(v_t_351_, 0);
lean_inc(v_n_357_);
lean_dec_ref_known(v_t_351_, 1);
v___x_358_ = lean_apply_1(v_k_352_, v_n_357_);
return v___x_358_;
}
default: 
{
lean_dec(v_t_351_);
return v_k_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim(lean_object* v_motive_359_, lean_object* v_ctorIdx_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_k_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_361_, v_k_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(lean_object* v_motive_365_, lean_object* v_ctorIdx_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_k_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(v_motive_365_, v_ctorIdx_366_, v_t_367_, v_h_368_, v_k_369_);
lean_dec(v_ctorIdx_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(lean_object* v_t_371_, lean_object* v_not_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_371_, v_not_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_not_elim(lean_object* v_motive_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_not_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_375_, v_not_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(lean_object* v_t_379_, lean_object* v_rotateLeft_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_379_, v_rotateLeft_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_rotateLeft_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_383_, v_rotateLeft_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(lean_object* v_t_387_, lean_object* v_rotateRight_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_387_, v_rotateRight_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_rotateRight_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_391_, v_rotateRight_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(lean_object* v_t_395_, lean_object* v_arithShiftRightConst_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_395_, v_arithShiftRightConst_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(lean_object* v_motive_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_arithShiftRightConst_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_399_, v_arithShiftRightConst_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(lean_object* v_t_403_, lean_object* v_reverse_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_403_, v_reverse_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(lean_object* v_motive_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_reverse_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_407_, v_reverse_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(lean_object* v_t_411_, lean_object* v_clz_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_411_, v_clz_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_clz_elim(lean_object* v_motive_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_clz_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_415_, v_clz_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(lean_object* v_t_419_, lean_object* v_cpop_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_419_, v_cpop_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(lean_object* v_motive_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_cpop_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_423_, v_cpop_425_);
return v___x_426_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(lean_object* v_x_427_){
_start:
{
switch(lean_obj_tag(v_x_427_))
{
case 0:
{
uint64_t v___x_428_; 
v___x_428_ = 0ULL;
return v___x_428_;
}
case 1:
{
lean_object* v_n_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; 
v_n_429_ = lean_ctor_get(v_x_427_, 0);
v___x_430_ = 1ULL;
v___x_431_ = lean_uint64_of_nat(v_n_429_);
v___x_432_ = lean_uint64_mix_hash(v___x_430_, v___x_431_);
return v___x_432_;
}
case 2:
{
lean_object* v_n_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; 
v_n_433_ = lean_ctor_get(v_x_427_, 0);
v___x_434_ = 2ULL;
v___x_435_ = lean_uint64_of_nat(v_n_433_);
v___x_436_ = lean_uint64_mix_hash(v___x_434_, v___x_435_);
return v___x_436_;
}
case 3:
{
lean_object* v_n_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; 
v_n_437_ = lean_ctor_get(v_x_427_, 0);
v___x_438_ = 3ULL;
v___x_439_ = lean_uint64_of_nat(v_n_437_);
v___x_440_ = lean_uint64_mix_hash(v___x_438_, v___x_439_);
return v___x_440_;
}
case 4:
{
uint64_t v___x_441_; 
v___x_441_ = 4ULL;
return v___x_441_;
}
case 5:
{
uint64_t v___x_442_; 
v___x_442_ = 5ULL;
return v___x_442_;
}
default: 
{
uint64_t v___x_443_; 
v___x_443_ = 6ULL;
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(lean_object* v_x_444_){
_start:
{
uint64_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_444_);
lean_dec(v_x_444_);
v_r_446_ = lean_box_uint64(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
switch(lean_obj_tag(v_x_449_))
{
case 0:
{
if (lean_obj_tag(v_x_450_) == 0)
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
}
case 1:
{
if (lean_obj_tag(v_x_450_) == 1)
{
lean_object* v_n_453_; lean_object* v_n_454_; uint8_t v___x_455_; 
v_n_453_ = lean_ctor_get(v_x_449_, 0);
v_n_454_ = lean_ctor_get(v_x_450_, 0);
v___x_455_ = lean_nat_dec_eq(v_n_453_, v_n_454_);
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
case 2:
{
if (lean_obj_tag(v_x_450_) == 2)
{
lean_object* v_n_457_; lean_object* v_n_458_; uint8_t v___x_459_; 
v_n_457_ = lean_ctor_get(v_x_449_, 0);
v_n_458_ = lean_ctor_get(v_x_450_, 0);
v___x_459_ = lean_nat_dec_eq(v_n_457_, v_n_458_);
return v___x_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
case 3:
{
if (lean_obj_tag(v_x_450_) == 3)
{
lean_object* v_n_461_; lean_object* v_n_462_; uint8_t v___x_463_; 
v_n_461_ = lean_ctor_get(v_x_449_, 0);
v_n_462_ = lean_ctor_get(v_x_450_, 0);
v___x_463_ = lean_nat_dec_eq(v_n_461_, v_n_462_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = 0;
return v___x_464_;
}
}
case 4:
{
if (lean_obj_tag(v_x_450_) == 4)
{
uint8_t v___x_465_; 
v___x_465_ = 1;
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
}
case 5:
{
if (lean_obj_tag(v_x_450_) == 5)
{
uint8_t v___x_467_; 
v___x_467_ = 1;
return v___x_467_;
}
else
{
uint8_t v___x_468_; 
v___x_468_ = 0;
return v___x_468_;
}
}
default: 
{
if (lean_obj_tag(v_x_450_) == 6)
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_471_, v_x_472_);
lean_dec(v_x_472_);
lean_dec(v_x_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_x_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* v_x_489_){
_start:
{
switch(lean_obj_tag(v_x_489_))
{
case 0:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0));
return v___x_490_;
}
case 1:
{
lean_object* v_n_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_n_491_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_n_491_);
lean_dec_ref_known(v_x_489_, 1);
v___x_492_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1));
v___x_493_ = l_Nat_reprFast(v_n_491_);
v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
lean_dec_ref(v___x_493_);
return v___x_494_;
}
case 2:
{
lean_object* v_n_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_n_495_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_n_495_);
lean_dec_ref_known(v_x_489_, 1);
v___x_496_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2));
v___x_497_ = l_Nat_reprFast(v_n_495_);
v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
lean_dec_ref(v___x_497_);
return v___x_498_;
}
case 3:
{
lean_object* v_n_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_n_499_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_n_499_);
lean_dec_ref_known(v_x_489_, 1);
v___x_500_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3));
v___x_501_ = l_Nat_reprFast(v_n_499_);
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
lean_dec_ref(v___x_501_);
return v___x_502_;
}
case 4:
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4));
return v___x_503_;
}
case 5:
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5));
return v___x_504_;
}
default: 
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6));
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* v_w_508_, lean_object* v_x_509_, lean_object* v_a_510_){
_start:
{
switch(lean_obj_tag(v_x_509_))
{
case 0:
{
lean_object* v___x_511_; 
v___x_511_ = l_BitVec_not(v_w_508_, v_a_510_);
lean_dec(v_a_510_);
lean_dec(v_w_508_);
return v___x_511_;
}
case 1:
{
lean_object* v_n_512_; lean_object* v___x_513_; 
v_n_512_ = lean_ctor_get(v_x_509_, 0);
v___x_513_ = l_BitVec_rotateLeft(v_w_508_, v_a_510_, v_n_512_);
lean_dec(v_a_510_);
lean_dec(v_w_508_);
return v___x_513_;
}
case 2:
{
lean_object* v_n_514_; lean_object* v___x_515_; 
v_n_514_ = lean_ctor_get(v_x_509_, 0);
v___x_515_ = l_BitVec_rotateRight(v_w_508_, v_a_510_, v_n_514_);
lean_dec(v_a_510_);
lean_dec(v_w_508_);
return v___x_515_;
}
case 3:
{
lean_object* v_n_516_; lean_object* v___x_517_; 
v_n_516_ = lean_ctor_get(v_x_509_, 0);
v___x_517_ = l_BitVec_sshiftRight(v_w_508_, v_a_510_, v_n_516_);
lean_dec(v_w_508_);
return v___x_517_;
}
case 4:
{
lean_object* v___x_518_; 
v___x_518_ = l_BitVec_reverse(v_w_508_, v_a_510_);
lean_dec(v_a_510_);
lean_dec(v_w_508_);
return v___x_518_;
}
case 5:
{
lean_object* v___x_519_; 
v___x_519_ = l_BitVec_clz(v_w_508_, v_a_510_);
lean_dec(v_a_510_);
lean_dec(v_w_508_);
return v___x_519_;
}
default: 
{
lean_object* v___x_520_; 
v___x_520_ = l_BitVec_cpop(v_w_508_, v_a_510_);
lean_dec(v_a_510_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* v_w_521_, lean_object* v_x_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_521_, v_x_522_, v_a_523_);
lean_dec(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg(lean_object* v_x_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_tag_nat(v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg___boxed(lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___redArg(v_x_527_);
lean_dec_ref(v_x_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl(lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_tag_nat(v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl___boxed(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___impl(v_a_532_, v_x_533_);
lean_dec_ref(v_x_533_);
lean_dec(v_a_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(lean_object* v_t_535_, lean_object* v_k_536_){
_start:
{
switch(lean_obj_tag(v_t_535_))
{
case 0:
{
lean_object* v_w_537_; lean_object* v_idx_538_; lean_object* v___x_539_; 
v_w_537_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_537_);
v_idx_538_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_idx_538_);
lean_dec_ref_known(v_t_535_, 2);
v___x_539_ = lean_apply_2(v_k_536_, v_w_537_, v_idx_538_);
return v___x_539_;
}
case 1:
{
lean_object* v_w_540_; lean_object* v_val_541_; lean_object* v___x_542_; 
v_w_540_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_540_);
v_val_541_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_val_541_);
lean_dec_ref_known(v_t_535_, 2);
v___x_542_ = lean_apply_2(v_k_536_, v_w_540_, v_val_541_);
return v___x_542_;
}
case 2:
{
lean_object* v_w_543_; lean_object* v_start_544_; lean_object* v_len_545_; lean_object* v_expr_546_; lean_object* v___x_547_; 
v_w_543_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_543_);
v_start_544_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_start_544_);
v_len_545_ = lean_ctor_get(v_t_535_, 2);
lean_inc(v_len_545_);
v_expr_546_ = lean_ctor_get(v_t_535_, 3);
lean_inc_ref(v_expr_546_);
lean_dec_ref_known(v_t_535_, 4);
v___x_547_ = lean_apply_4(v_k_536_, v_w_543_, v_start_544_, v_len_545_, v_expr_546_);
return v___x_547_;
}
case 3:
{
lean_object* v_w_548_; lean_object* v_lhs_549_; uint8_t v_op_550_; lean_object* v_rhs_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_w_548_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_548_);
v_lhs_549_ = lean_ctor_get(v_t_535_, 1);
lean_inc_ref(v_lhs_549_);
v_op_550_ = lean_ctor_get_uint8(v_t_535_, sizeof(void*)*3);
v_rhs_551_ = lean_ctor_get(v_t_535_, 2);
lean_inc_ref(v_rhs_551_);
lean_dec_ref_known(v_t_535_, 3);
v___x_552_ = lean_box(v_op_550_);
v___x_553_ = lean_apply_4(v_k_536_, v_w_548_, v_lhs_549_, v___x_552_, v_rhs_551_);
return v___x_553_;
}
case 4:
{
lean_object* v_w_554_; lean_object* v_op_555_; lean_object* v_operand_556_; lean_object* v___x_557_; 
v_w_554_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_554_);
v_op_555_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_op_555_);
v_operand_556_ = lean_ctor_get(v_t_535_, 2);
lean_inc_ref(v_operand_556_);
lean_dec_ref_known(v_t_535_, 3);
v___x_557_ = lean_apply_3(v_k_536_, v_w_554_, v_op_555_, v_operand_556_);
return v___x_557_;
}
case 5:
{
lean_object* v_l_558_; lean_object* v_r_559_; lean_object* v_w_560_; lean_object* v_lhs_561_; lean_object* v_rhs_562_; lean_object* v___x_563_; 
v_l_558_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_l_558_);
v_r_559_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_r_559_);
v_w_560_ = lean_ctor_get(v_t_535_, 2);
lean_inc(v_w_560_);
v_lhs_561_ = lean_ctor_get(v_t_535_, 3);
lean_inc_ref(v_lhs_561_);
v_rhs_562_ = lean_ctor_get(v_t_535_, 4);
lean_inc_ref(v_rhs_562_);
lean_dec_ref_known(v_t_535_, 5);
v___x_563_ = lean_apply_6(v_k_536_, v_l_558_, v_r_559_, v_w_560_, v_lhs_561_, v_rhs_562_, lean_box(0));
return v___x_563_;
}
case 6:
{
lean_object* v_w_564_; lean_object* v_w_x27_565_; lean_object* v_n_566_; lean_object* v_expr_567_; lean_object* v___x_568_; 
v_w_564_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_w_564_);
v_w_x27_565_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_w_x27_565_);
v_n_566_ = lean_ctor_get(v_t_535_, 2);
lean_inc(v_n_566_);
v_expr_567_ = lean_ctor_get(v_t_535_, 3);
lean_inc_ref(v_expr_567_);
lean_dec_ref_known(v_t_535_, 4);
v___x_568_ = lean_apply_5(v_k_536_, v_w_564_, v_w_x27_565_, v_n_566_, v_expr_567_, lean_box(0));
return v___x_568_;
}
default: 
{
lean_object* v_m_569_; lean_object* v_n_570_; lean_object* v_lhs_571_; lean_object* v_rhs_572_; lean_object* v___x_573_; 
v_m_569_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_m_569_);
v_n_570_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_n_570_);
v_lhs_571_ = lean_ctor_get(v_t_535_, 2);
lean_inc_ref(v_lhs_571_);
v_rhs_572_ = lean_ctor_get(v_t_535_, 3);
lean_inc_ref(v_rhs_572_);
lean_dec_ref(v_t_535_);
v___x_573_ = lean_apply_4(v_k_536_, v_m_569_, v_n_570_, v_lhs_571_, v_rhs_572_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim(lean_object* v_motive_574_, lean_object* v_ctorIdx_575_, lean_object* v_a_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_577_, v_k_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(lean_object* v_motive_581_, lean_object* v_ctorIdx_582_, lean_object* v_a_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(v_motive_581_, v_ctorIdx_582_, v_a_583_, v_t_584_, v_h_585_, v_k_586_);
lean_dec(v_a_583_);
lean_dec(v_ctorIdx_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(lean_object* v_t_588_, lean_object* v_var_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_588_, v_var_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim(lean_object* v_motive_591_, lean_object* v_a_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_var_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_593_, v_var_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(lean_object* v_motive_597_, lean_object* v_a_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_var_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(v_motive_597_, v_a_598_, v_t_599_, v_h_600_, v_var_601_);
lean_dec(v_a_598_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(lean_object* v_t_603_, lean_object* v_const_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_603_, v_const_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim(lean_object* v_motive_606_, lean_object* v_a_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_const_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_608_, v_const_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(lean_object* v_motive_612_, lean_object* v_a_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_const_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(v_motive_612_, v_a_613_, v_t_614_, v_h_615_, v_const_616_);
lean_dec(v_a_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(lean_object* v_t_618_, lean_object* v_extract_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_618_, v_extract_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim(lean_object* v_motive_621_, lean_object* v_a_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_extract_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_623_, v_extract_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(lean_object* v_motive_627_, lean_object* v_a_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_extract_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(v_motive_627_, v_a_628_, v_t_629_, v_h_630_, v_extract_631_);
lean_dec(v_a_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(lean_object* v_t_633_, lean_object* v_bin_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_633_, v_bin_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim(lean_object* v_motive_636_, lean_object* v_a_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_bin_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_638_, v_bin_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(lean_object* v_motive_642_, lean_object* v_a_643_, lean_object* v_t_644_, lean_object* v_h_645_, lean_object* v_bin_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(v_motive_642_, v_a_643_, v_t_644_, v_h_645_, v_bin_646_);
lean_dec(v_a_643_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(lean_object* v_t_648_, lean_object* v_un_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_648_, v_un_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim(lean_object* v_motive_651_, lean_object* v_a_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_un_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_653_, v_un_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(lean_object* v_motive_657_, lean_object* v_a_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_un_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(v_motive_657_, v_a_658_, v_t_659_, v_h_660_, v_un_661_);
lean_dec(v_a_658_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(lean_object* v_t_663_, lean_object* v_append_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_663_, v_append_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim(lean_object* v_motive_666_, lean_object* v_a_667_, lean_object* v_t_668_, lean_object* v_h_669_, lean_object* v_append_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_668_, v_append_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(lean_object* v_motive_672_, lean_object* v_a_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_append_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(v_motive_672_, v_a_673_, v_t_674_, v_h_675_, v_append_676_);
lean_dec(v_a_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(lean_object* v_t_678_, lean_object* v_replicate_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_678_, v_replicate_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim(lean_object* v_motive_681_, lean_object* v_a_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_replicate_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_683_, v_replicate_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(lean_object* v_motive_687_, lean_object* v_a_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_replicate_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(v_motive_687_, v_a_688_, v_t_689_, v_h_690_, v_replicate_691_);
lean_dec(v_a_688_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(lean_object* v_t_693_, lean_object* v_shiftLeft_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_693_, v_shiftLeft_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(lean_object* v_motive_696_, lean_object* v_a_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_shiftLeft_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_698_, v_shiftLeft_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(lean_object* v_motive_702_, lean_object* v_a_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_shiftLeft_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(v_motive_702_, v_a_703_, v_t_704_, v_h_705_, v_shiftLeft_706_);
lean_dec(v_a_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(lean_object* v_t_708_, lean_object* v_shiftRight_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_708_, v_shiftRight_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(lean_object* v_motive_711_, lean_object* v_a_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_shiftRight_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_713_, v_shiftRight_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(lean_object* v_motive_717_, lean_object* v_a_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_shiftRight_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(v_motive_717_, v_a_718_, v_t_719_, v_h_720_, v_shiftRight_721_);
lean_dec(v_a_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(lean_object* v_t_723_, lean_object* v_arithShiftRight_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_723_, v_arithShiftRight_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(lean_object* v_motive_726_, lean_object* v_a_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_arithShiftRight_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_728_, v_arithShiftRight_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(lean_object* v_motive_732_, lean_object* v_a_733_, lean_object* v_t_734_, lean_object* v_h_735_, lean_object* v_arithShiftRight_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(v_motive_732_, v_a_733_, v_t_734_, v_h_735_, v_arithShiftRight_736_);
lean_dec(v_a_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* v_t_738_, lean_object* v_var_739_, lean_object* v_const_740_, lean_object* v_extract_741_, lean_object* v_bin_742_, lean_object* v_un_743_, lean_object* v_append_744_, lean_object* v_replicate_745_, lean_object* v_shiftLeft_746_, lean_object* v_shiftRight_747_, lean_object* v_arithShiftRight_748_){
_start:
{
switch(lean_obj_tag(v_t_738_))
{
case 0:
{
lean_object* v_w_749_; lean_object* v_idx_750_; lean_object* v___x_751_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
v_w_749_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_749_);
v_idx_750_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_idx_750_);
lean_dec_ref_known(v_t_738_, 2);
v___x_751_ = lean_apply_2(v_var_739_, v_w_749_, v_idx_750_);
return v___x_751_;
}
case 1:
{
lean_object* v_w_752_; lean_object* v_val_753_; lean_object* v___x_754_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_var_739_);
v_w_752_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_752_);
v_val_753_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_val_753_);
lean_dec_ref_known(v_t_738_, 2);
v___x_754_ = lean_apply_2(v_const_740_, v_w_752_, v_val_753_);
return v___x_754_;
}
case 2:
{
lean_object* v_w_755_; lean_object* v_start_756_; lean_object* v_len_757_; lean_object* v_expr_758_; lean_object* v___x_759_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_w_755_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_755_);
v_start_756_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_start_756_);
v_len_757_ = lean_ctor_get(v_t_738_, 2);
lean_inc(v_len_757_);
v_expr_758_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_expr_758_);
lean_dec_ref_known(v_t_738_, 4);
v___x_759_ = lean_apply_4(v_extract_741_, v_w_755_, v_start_756_, v_len_757_, v_expr_758_);
return v___x_759_;
}
case 3:
{
lean_object* v_w_760_; lean_object* v_lhs_761_; uint8_t v_op_762_; lean_object* v_rhs_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_w_760_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_760_);
v_lhs_761_ = lean_ctor_get(v_t_738_, 1);
lean_inc_ref(v_lhs_761_);
v_op_762_ = lean_ctor_get_uint8(v_t_738_, sizeof(void*)*3 + 8);
v_rhs_763_ = lean_ctor_get(v_t_738_, 2);
lean_inc_ref(v_rhs_763_);
lean_dec_ref_known(v_t_738_, 3);
v___x_764_ = lean_box(v_op_762_);
v___x_765_ = lean_apply_4(v_bin_742_, v_w_760_, v_lhs_761_, v___x_764_, v_rhs_763_);
return v___x_765_;
}
case 4:
{
lean_object* v_w_766_; lean_object* v_op_767_; lean_object* v_operand_768_; lean_object* v___x_769_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_w_766_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_766_);
v_op_767_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_op_767_);
v_operand_768_ = lean_ctor_get(v_t_738_, 2);
lean_inc_ref(v_operand_768_);
lean_dec_ref_known(v_t_738_, 3);
v___x_769_ = lean_apply_3(v_un_743_, v_w_766_, v_op_767_, v_operand_768_);
return v___x_769_;
}
case 5:
{
lean_object* v_l_770_; lean_object* v_r_771_; lean_object* v_w_772_; lean_object* v_lhs_773_; lean_object* v_rhs_774_; lean_object* v___x_775_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_l_770_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_l_770_);
v_r_771_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_r_771_);
v_w_772_ = lean_ctor_get(v_t_738_, 2);
lean_inc(v_w_772_);
v_lhs_773_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_lhs_773_);
v_rhs_774_ = lean_ctor_get(v_t_738_, 4);
lean_inc_ref(v_rhs_774_);
lean_dec_ref_known(v_t_738_, 5);
v___x_775_ = lean_apply_6(v_append_744_, v_l_770_, v_r_771_, v_w_772_, v_lhs_773_, v_rhs_774_, lean_box(0));
return v___x_775_;
}
case 6:
{
lean_object* v_w_776_; lean_object* v_w_x27_777_; lean_object* v_n_778_; lean_object* v_expr_779_; lean_object* v___x_780_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_w_776_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_w_776_);
v_w_x27_777_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_w_x27_777_);
v_n_778_ = lean_ctor_get(v_t_738_, 2);
lean_inc(v_n_778_);
v_expr_779_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_expr_779_);
lean_dec_ref_known(v_t_738_, 4);
v___x_780_ = lean_apply_5(v_replicate_745_, v_w_776_, v_w_x27_777_, v_n_778_, v_expr_779_, lean_box(0));
return v___x_780_;
}
case 7:
{
lean_object* v_m_781_; lean_object* v_n_782_; lean_object* v_lhs_783_; lean_object* v_rhs_784_; lean_object* v___x_785_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftRight_747_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_m_781_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_m_781_);
v_n_782_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_n_782_);
v_lhs_783_ = lean_ctor_get(v_t_738_, 2);
lean_inc_ref(v_lhs_783_);
v_rhs_784_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_rhs_784_);
lean_dec_ref_known(v_t_738_, 4);
v___x_785_ = lean_apply_4(v_shiftLeft_746_, v_m_781_, v_n_782_, v_lhs_783_, v_rhs_784_);
return v___x_785_;
}
case 8:
{
lean_object* v_m_786_; lean_object* v_n_787_; lean_object* v_lhs_788_; lean_object* v_rhs_789_; lean_object* v___x_790_; 
lean_dec(v_arithShiftRight_748_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_m_786_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_m_786_);
v_n_787_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_n_787_);
v_lhs_788_ = lean_ctor_get(v_t_738_, 2);
lean_inc_ref(v_lhs_788_);
v_rhs_789_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_rhs_789_);
lean_dec_ref_known(v_t_738_, 4);
v___x_790_ = lean_apply_4(v_shiftRight_747_, v_m_786_, v_n_787_, v_lhs_788_, v_rhs_789_);
return v___x_790_;
}
default: 
{
lean_object* v_m_791_; lean_object* v_n_792_; lean_object* v_lhs_793_; lean_object* v_rhs_794_; lean_object* v___x_795_; 
lean_dec(v_shiftRight_747_);
lean_dec(v_shiftLeft_746_);
lean_dec(v_replicate_745_);
lean_dec(v_append_744_);
lean_dec(v_un_743_);
lean_dec(v_bin_742_);
lean_dec(v_extract_741_);
lean_dec(v_const_740_);
lean_dec(v_var_739_);
v_m_791_ = lean_ctor_get(v_t_738_, 0);
lean_inc(v_m_791_);
v_n_792_ = lean_ctor_get(v_t_738_, 1);
lean_inc(v_n_792_);
v_lhs_793_ = lean_ctor_get(v_t_738_, 2);
lean_inc_ref(v_lhs_793_);
v_rhs_794_ = lean_ctor_get(v_t_738_, 3);
lean_inc_ref(v_rhs_794_);
lean_dec_ref_known(v_t_738_, 4);
v___x_795_ = lean_apply_4(v_arithShiftRight_748_, v_m_791_, v_n_792_, v_lhs_793_, v_rhs_794_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* v_motive_796_, lean_object* v_a_797_, lean_object* v_t_798_, lean_object* v_var_799_, lean_object* v_const_800_, lean_object* v_extract_801_, lean_object* v_bin_802_, lean_object* v_un_803_, lean_object* v_append_804_, lean_object* v_replicate_805_, lean_object* v_shiftLeft_806_, lean_object* v_shiftRight_807_, lean_object* v_arithShiftRight_808_){
_start:
{
switch(lean_obj_tag(v_t_798_))
{
case 0:
{
lean_object* v_w_809_; lean_object* v_idx_810_; lean_object* v___x_811_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
v_w_809_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_809_);
v_idx_810_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_idx_810_);
lean_dec_ref_known(v_t_798_, 2);
v___x_811_ = lean_apply_2(v_var_799_, v_w_809_, v_idx_810_);
return v___x_811_;
}
case 1:
{
lean_object* v_w_812_; lean_object* v_val_813_; lean_object* v___x_814_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_var_799_);
v_w_812_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_812_);
v_val_813_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_val_813_);
lean_dec_ref_known(v_t_798_, 2);
v___x_814_ = lean_apply_2(v_const_800_, v_w_812_, v_val_813_);
return v___x_814_;
}
case 2:
{
lean_object* v_w_815_; lean_object* v_start_816_; lean_object* v_len_817_; lean_object* v_expr_818_; lean_object* v___x_819_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_w_815_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_815_);
v_start_816_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_start_816_);
v_len_817_ = lean_ctor_get(v_t_798_, 2);
lean_inc(v_len_817_);
v_expr_818_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_expr_818_);
lean_dec_ref_known(v_t_798_, 4);
v___x_819_ = lean_apply_4(v_extract_801_, v_w_815_, v_start_816_, v_len_817_, v_expr_818_);
return v___x_819_;
}
case 3:
{
lean_object* v_w_820_; lean_object* v_lhs_821_; uint8_t v_op_822_; lean_object* v_rhs_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_w_820_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_820_);
v_lhs_821_ = lean_ctor_get(v_t_798_, 1);
lean_inc_ref(v_lhs_821_);
v_op_822_ = lean_ctor_get_uint8(v_t_798_, sizeof(void*)*3 + 8);
v_rhs_823_ = lean_ctor_get(v_t_798_, 2);
lean_inc_ref(v_rhs_823_);
lean_dec_ref_known(v_t_798_, 3);
v___x_824_ = lean_box(v_op_822_);
v___x_825_ = lean_apply_4(v_bin_802_, v_w_820_, v_lhs_821_, v___x_824_, v_rhs_823_);
return v___x_825_;
}
case 4:
{
lean_object* v_w_826_; lean_object* v_op_827_; lean_object* v_operand_828_; lean_object* v___x_829_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_w_826_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_826_);
v_op_827_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_op_827_);
v_operand_828_ = lean_ctor_get(v_t_798_, 2);
lean_inc_ref(v_operand_828_);
lean_dec_ref_known(v_t_798_, 3);
v___x_829_ = lean_apply_3(v_un_803_, v_w_826_, v_op_827_, v_operand_828_);
return v___x_829_;
}
case 5:
{
lean_object* v_l_830_; lean_object* v_r_831_; lean_object* v_w_832_; lean_object* v_lhs_833_; lean_object* v_rhs_834_; lean_object* v___x_835_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_l_830_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_l_830_);
v_r_831_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_r_831_);
v_w_832_ = lean_ctor_get(v_t_798_, 2);
lean_inc(v_w_832_);
v_lhs_833_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_lhs_833_);
v_rhs_834_ = lean_ctor_get(v_t_798_, 4);
lean_inc_ref(v_rhs_834_);
lean_dec_ref_known(v_t_798_, 5);
v___x_835_ = lean_apply_6(v_append_804_, v_l_830_, v_r_831_, v_w_832_, v_lhs_833_, v_rhs_834_, lean_box(0));
return v___x_835_;
}
case 6:
{
lean_object* v_w_836_; lean_object* v_w_x27_837_; lean_object* v_n_838_; lean_object* v_expr_839_; lean_object* v___x_840_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_w_836_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_w_836_);
v_w_x27_837_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_w_x27_837_);
v_n_838_ = lean_ctor_get(v_t_798_, 2);
lean_inc(v_n_838_);
v_expr_839_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_expr_839_);
lean_dec_ref_known(v_t_798_, 4);
v___x_840_ = lean_apply_5(v_replicate_805_, v_w_836_, v_w_x27_837_, v_n_838_, v_expr_839_, lean_box(0));
return v___x_840_;
}
case 7:
{
lean_object* v_m_841_; lean_object* v_n_842_; lean_object* v_lhs_843_; lean_object* v_rhs_844_; lean_object* v___x_845_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftRight_807_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_m_841_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_m_841_);
v_n_842_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_n_842_);
v_lhs_843_ = lean_ctor_get(v_t_798_, 2);
lean_inc_ref(v_lhs_843_);
v_rhs_844_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_rhs_844_);
lean_dec_ref_known(v_t_798_, 4);
v___x_845_ = lean_apply_4(v_shiftLeft_806_, v_m_841_, v_n_842_, v_lhs_843_, v_rhs_844_);
return v___x_845_;
}
case 8:
{
lean_object* v_m_846_; lean_object* v_n_847_; lean_object* v_lhs_848_; lean_object* v_rhs_849_; lean_object* v___x_850_; 
lean_dec(v_arithShiftRight_808_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_m_846_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_m_846_);
v_n_847_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_n_847_);
v_lhs_848_ = lean_ctor_get(v_t_798_, 2);
lean_inc_ref(v_lhs_848_);
v_rhs_849_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_rhs_849_);
lean_dec_ref_known(v_t_798_, 4);
v___x_850_ = lean_apply_4(v_shiftRight_807_, v_m_846_, v_n_847_, v_lhs_848_, v_rhs_849_);
return v___x_850_;
}
default: 
{
lean_object* v_m_851_; lean_object* v_n_852_; lean_object* v_lhs_853_; lean_object* v_rhs_854_; lean_object* v___x_855_; 
lean_dec(v_shiftRight_807_);
lean_dec(v_shiftLeft_806_);
lean_dec(v_replicate_805_);
lean_dec(v_append_804_);
lean_dec(v_un_803_);
lean_dec(v_bin_802_);
lean_dec(v_extract_801_);
lean_dec(v_const_800_);
lean_dec(v_var_799_);
v_m_851_ = lean_ctor_get(v_t_798_, 0);
lean_inc(v_m_851_);
v_n_852_ = lean_ctor_get(v_t_798_, 1);
lean_inc(v_n_852_);
v_lhs_853_ = lean_ctor_get(v_t_798_, 2);
lean_inc_ref(v_lhs_853_);
v_rhs_854_ = lean_ctor_get(v_t_798_, 3);
lean_inc_ref(v_rhs_854_);
lean_dec_ref_known(v_t_798_, 4);
v___x_855_ = lean_apply_4(v_arithShiftRight_808_, v_m_851_, v_n_852_, v_lhs_853_, v_rhs_854_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* v_motive_856_, lean_object* v_a_857_, lean_object* v_t_858_, lean_object* v_var_859_, lean_object* v_const_860_, lean_object* v_extract_861_, lean_object* v_bin_862_, lean_object* v_un_863_, lean_object* v_append_864_, lean_object* v_replicate_865_, lean_object* v_shiftLeft_866_, lean_object* v_shiftRight_867_, lean_object* v_arithShiftRight_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(v_motive_856_, v_a_857_, v_t_858_, v_var_859_, v_const_860_, v_extract_861_, v_bin_862_, v_un_863_, v_append_864_, v_replicate_865_, v_shiftLeft_866_, v_shiftRight_867_, v_arithShiftRight_868_);
lean_dec(v_a_857_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* v_w_870_, lean_object* v_idx_871_){
_start:
{
uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; lean_object* v___x_877_; 
v___x_872_ = 5ULL;
v___x_873_ = lean_uint64_of_nat(v_w_870_);
v___x_874_ = lean_uint64_of_nat(v_idx_871_);
v___x_875_ = lean_uint64_mix_hash(v___x_873_, v___x_874_);
v___x_876_ = lean_uint64_mix_hash(v___x_872_, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_877_, 0, v_w_870_);
lean_ctor_set(v___x_877_, 1, v_idx_871_);
lean_ctor_set_uint64(v___x_877_, sizeof(void*)*2, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* v_w_878_, lean_object* v_val_879_){
_start:
{
uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; lean_object* v___x_885_; 
v___x_880_ = 7ULL;
v___x_881_ = lean_uint64_of_nat(v_w_878_);
v___x_882_ = l_BitVec_hash(v_w_878_, v_val_879_);
v___x_883_ = lean_uint64_mix_hash(v___x_881_, v___x_882_);
v___x_884_ = lean_uint64_mix_hash(v___x_880_, v___x_883_);
v___x_885_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_885_, 0, v_w_878_);
lean_ctor_set(v___x_885_, 1, v_val_879_);
lean_ctor_set_uint64(v___x_885_, sizeof(void*)*2, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* v_w_886_, lean_object* v_start_887_, lean_object* v_len_888_, lean_object* v_expr_889_){
_start:
{
uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v___y_894_; 
v___x_890_ = 11ULL;
v___x_891_ = lean_uint64_of_nat(v_start_887_);
v___x_892_ = lean_uint64_of_nat(v_len_888_);
switch(lean_obj_tag(v_expr_889_))
{
case 0:
{
uint64_t v_hashCode_899_; 
v_hashCode_899_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*2);
v___y_894_ = v_hashCode_899_;
goto v___jp_893_;
}
case 1:
{
uint64_t v_hashCode_900_; 
v_hashCode_900_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*2);
v___y_894_ = v_hashCode_900_;
goto v___jp_893_;
}
case 3:
{
uint64_t v_hashCode_901_; 
v_hashCode_901_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*3);
v___y_894_ = v_hashCode_901_;
goto v___jp_893_;
}
case 4:
{
uint64_t v_hashCode_902_; 
v_hashCode_902_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*3);
v___y_894_ = v_hashCode_902_;
goto v___jp_893_;
}
case 5:
{
uint64_t v_hashCode_903_; 
v_hashCode_903_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*5);
v___y_894_ = v_hashCode_903_;
goto v___jp_893_;
}
default: 
{
uint64_t v_hashCode_904_; 
v_hashCode_904_ = lean_ctor_get_uint64(v_expr_889_, sizeof(void*)*4);
v___y_894_ = v_hashCode_904_;
goto v___jp_893_;
}
}
v___jp_893_:
{
uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; lean_object* v___x_898_; 
v___x_895_ = lean_uint64_mix_hash(v___x_892_, v___y_894_);
v___x_896_ = lean_uint64_mix_hash(v___x_891_, v___x_895_);
v___x_897_ = lean_uint64_mix_hash(v___x_890_, v___x_896_);
v___x_898_ = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(v___x_898_, 0, v_w_886_);
lean_ctor_set(v___x_898_, 1, v_start_887_);
lean_ctor_set(v___x_898_, 2, v_len_888_);
lean_ctor_set(v___x_898_, 3, v_expr_889_);
lean_ctor_set_uint64(v___x_898_, sizeof(void*)*4, v___x_897_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* v_w_905_, lean_object* v_lhs_906_, uint8_t v_op_907_, lean_object* v_rhs_908_){
_start:
{
uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___y_912_; uint64_t v___y_913_; uint64_t v___y_914_; uint64_t v___y_921_; 
v___x_909_ = 13ULL;
v___x_910_ = lean_uint64_of_nat(v_w_905_);
switch(lean_obj_tag(v_lhs_906_))
{
case 0:
{
uint64_t v_hashCode_929_; 
v_hashCode_929_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*2);
v___y_921_ = v_hashCode_929_;
goto v___jp_920_;
}
case 1:
{
uint64_t v_hashCode_930_; 
v_hashCode_930_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*2);
v___y_921_ = v_hashCode_930_;
goto v___jp_920_;
}
case 3:
{
uint64_t v_hashCode_931_; 
v_hashCode_931_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*3);
v___y_921_ = v_hashCode_931_;
goto v___jp_920_;
}
case 4:
{
uint64_t v_hashCode_932_; 
v_hashCode_932_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*3);
v___y_921_ = v_hashCode_932_;
goto v___jp_920_;
}
case 5:
{
uint64_t v_hashCode_933_; 
v_hashCode_933_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*5);
v___y_921_ = v_hashCode_933_;
goto v___jp_920_;
}
default: 
{
uint64_t v_hashCode_934_; 
v_hashCode_934_ = lean_ctor_get_uint64(v_lhs_906_, sizeof(void*)*4);
v___y_921_ = v_hashCode_934_;
goto v___jp_920_;
}
}
v___jp_911_:
{
uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; lean_object* v___x_919_; 
v___x_915_ = lean_uint64_mix_hash(v___y_912_, v___y_914_);
v___x_916_ = lean_uint64_mix_hash(v___y_913_, v___x_915_);
v___x_917_ = lean_uint64_mix_hash(v___x_910_, v___x_916_);
v___x_918_ = lean_uint64_mix_hash(v___x_909_, v___x_917_);
v___x_919_ = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(v___x_919_, 0, v_w_905_);
lean_ctor_set(v___x_919_, 1, v_lhs_906_);
lean_ctor_set(v___x_919_, 2, v_rhs_908_);
lean_ctor_set_uint64(v___x_919_, sizeof(void*)*3, v___x_918_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*3 + 8, v_op_907_);
return v___x_919_;
}
v___jp_920_:
{
uint64_t v___x_922_; 
v___x_922_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_907_);
switch(lean_obj_tag(v_rhs_908_))
{
case 0:
{
uint64_t v_hashCode_923_; 
v_hashCode_923_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*2);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_923_;
goto v___jp_911_;
}
case 1:
{
uint64_t v_hashCode_924_; 
v_hashCode_924_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*2);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_924_;
goto v___jp_911_;
}
case 3:
{
uint64_t v_hashCode_925_; 
v_hashCode_925_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*3);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_925_;
goto v___jp_911_;
}
case 4:
{
uint64_t v_hashCode_926_; 
v_hashCode_926_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*3);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_926_;
goto v___jp_911_;
}
case 5:
{
uint64_t v_hashCode_927_; 
v_hashCode_927_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*5);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_927_;
goto v___jp_911_;
}
default: 
{
uint64_t v_hashCode_928_; 
v_hashCode_928_ = lean_ctor_get_uint64(v_rhs_908_, sizeof(void*)*4);
v___y_912_ = v___x_922_;
v___y_913_ = v___y_921_;
v___y_914_ = v_hashCode_928_;
goto v___jp_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* v_w_935_, lean_object* v_lhs_936_, lean_object* v_op_937_, lean_object* v_rhs_938_){
_start:
{
uint8_t v_op_boxed_939_; lean_object* v_res_940_; 
v_op_boxed_939_ = lean_unbox(v_op_937_);
v_res_940_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_935_, v_lhs_936_, v_op_boxed_939_, v_rhs_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* v_w_941_, lean_object* v_op_942_, lean_object* v_operand_943_){
_start:
{
uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v___y_948_; 
v___x_944_ = 17ULL;
v___x_945_ = lean_uint64_of_nat(v_w_941_);
v___x_946_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_942_);
switch(lean_obj_tag(v_operand_943_))
{
case 0:
{
uint64_t v_hashCode_953_; 
v_hashCode_953_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*2);
v___y_948_ = v_hashCode_953_;
goto v___jp_947_;
}
case 1:
{
uint64_t v_hashCode_954_; 
v_hashCode_954_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*2);
v___y_948_ = v_hashCode_954_;
goto v___jp_947_;
}
case 3:
{
uint64_t v_hashCode_955_; 
v_hashCode_955_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*3);
v___y_948_ = v_hashCode_955_;
goto v___jp_947_;
}
case 4:
{
uint64_t v_hashCode_956_; 
v_hashCode_956_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*3);
v___y_948_ = v_hashCode_956_;
goto v___jp_947_;
}
case 5:
{
uint64_t v_hashCode_957_; 
v_hashCode_957_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*5);
v___y_948_ = v_hashCode_957_;
goto v___jp_947_;
}
default: 
{
uint64_t v_hashCode_958_; 
v_hashCode_958_ = lean_ctor_get_uint64(v_operand_943_, sizeof(void*)*4);
v___y_948_ = v_hashCode_958_;
goto v___jp_947_;
}
}
v___jp_947_:
{
uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; lean_object* v___x_952_; 
v___x_949_ = lean_uint64_mix_hash(v___x_946_, v___y_948_);
v___x_950_ = lean_uint64_mix_hash(v___x_945_, v___x_949_);
v___x_951_ = lean_uint64_mix_hash(v___x_944_, v___x_950_);
v___x_952_ = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(v___x_952_, 0, v_w_941_);
lean_ctor_set(v___x_952_, 1, v_op_942_);
lean_ctor_set(v___x_952_, 2, v_operand_943_);
lean_ctor_set_uint64(v___x_952_, sizeof(void*)*3, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* v_l_959_, lean_object* v_r_960_, lean_object* v_w_961_, lean_object* v_lhs_962_, lean_object* v_rhs_963_){
_start:
{
uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___y_967_; uint64_t v___y_968_; uint64_t v___y_974_; 
v___x_964_ = 19ULL;
v___x_965_ = lean_uint64_of_nat(v_w_961_);
switch(lean_obj_tag(v_lhs_962_))
{
case 0:
{
uint64_t v_hashCode_981_; 
v_hashCode_981_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*2);
v___y_974_ = v_hashCode_981_;
goto v___jp_973_;
}
case 1:
{
uint64_t v_hashCode_982_; 
v_hashCode_982_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*2);
v___y_974_ = v_hashCode_982_;
goto v___jp_973_;
}
case 3:
{
uint64_t v_hashCode_983_; 
v_hashCode_983_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*3);
v___y_974_ = v_hashCode_983_;
goto v___jp_973_;
}
case 4:
{
uint64_t v_hashCode_984_; 
v_hashCode_984_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*3);
v___y_974_ = v_hashCode_984_;
goto v___jp_973_;
}
case 5:
{
uint64_t v_hashCode_985_; 
v_hashCode_985_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*5);
v___y_974_ = v_hashCode_985_;
goto v___jp_973_;
}
default: 
{
uint64_t v_hashCode_986_; 
v_hashCode_986_ = lean_ctor_get_uint64(v_lhs_962_, sizeof(void*)*4);
v___y_974_ = v_hashCode_986_;
goto v___jp_973_;
}
}
v___jp_966_:
{
uint64_t v___x_969_; uint64_t v___x_970_; uint64_t v___x_971_; lean_object* v___x_972_; 
v___x_969_ = lean_uint64_mix_hash(v___y_967_, v___y_968_);
v___x_970_ = lean_uint64_mix_hash(v___x_965_, v___x_969_);
v___x_971_ = lean_uint64_mix_hash(v___x_964_, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(v___x_972_, 0, v_l_959_);
lean_ctor_set(v___x_972_, 1, v_r_960_);
lean_ctor_set(v___x_972_, 2, v_w_961_);
lean_ctor_set(v___x_972_, 3, v_lhs_962_);
lean_ctor_set(v___x_972_, 4, v_rhs_963_);
lean_ctor_set_uint64(v___x_972_, sizeof(void*)*5, v___x_971_);
return v___x_972_;
}
v___jp_973_:
{
switch(lean_obj_tag(v_rhs_963_))
{
case 0:
{
uint64_t v_hashCode_975_; 
v_hashCode_975_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*2);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_975_;
goto v___jp_966_;
}
case 1:
{
uint64_t v_hashCode_976_; 
v_hashCode_976_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*2);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_976_;
goto v___jp_966_;
}
case 3:
{
uint64_t v_hashCode_977_; 
v_hashCode_977_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*3);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_977_;
goto v___jp_966_;
}
case 4:
{
uint64_t v_hashCode_978_; 
v_hashCode_978_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*3);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_978_;
goto v___jp_966_;
}
case 5:
{
uint64_t v_hashCode_979_; 
v_hashCode_979_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*5);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_979_;
goto v___jp_966_;
}
default: 
{
uint64_t v_hashCode_980_; 
v_hashCode_980_ = lean_ctor_get_uint64(v_rhs_963_, sizeof(void*)*4);
v___y_967_ = v___y_974_;
v___y_968_ = v_hashCode_980_;
goto v___jp_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* v_l_987_, lean_object* v_r_988_, lean_object* v_w_989_, lean_object* v_lhs_990_, lean_object* v_rhs_991_, lean_object* v_h_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_987_, v_r_988_, v_w_989_, v_lhs_990_, v_rhs_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* v_w_994_, lean_object* v_w_x27_995_, lean_object* v_n_996_, lean_object* v_expr_997_){
_start:
{
uint64_t v___x_998_; uint64_t v___x_999_; uint64_t v___x_1000_; uint64_t v___y_1002_; 
v___x_998_ = 23ULL;
v___x_999_ = lean_uint64_of_nat(v_w_x27_995_);
v___x_1000_ = lean_uint64_of_nat(v_n_996_);
switch(lean_obj_tag(v_expr_997_))
{
case 0:
{
uint64_t v_hashCode_1007_; 
v_hashCode_1007_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*2);
v___y_1002_ = v_hashCode_1007_;
goto v___jp_1001_;
}
case 1:
{
uint64_t v_hashCode_1008_; 
v_hashCode_1008_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*2);
v___y_1002_ = v_hashCode_1008_;
goto v___jp_1001_;
}
case 3:
{
uint64_t v_hashCode_1009_; 
v_hashCode_1009_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*3);
v___y_1002_ = v_hashCode_1009_;
goto v___jp_1001_;
}
case 4:
{
uint64_t v_hashCode_1010_; 
v_hashCode_1010_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*3);
v___y_1002_ = v_hashCode_1010_;
goto v___jp_1001_;
}
case 5:
{
uint64_t v_hashCode_1011_; 
v_hashCode_1011_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*5);
v___y_1002_ = v_hashCode_1011_;
goto v___jp_1001_;
}
default: 
{
uint64_t v_hashCode_1012_; 
v_hashCode_1012_ = lean_ctor_get_uint64(v_expr_997_, sizeof(void*)*4);
v___y_1002_ = v_hashCode_1012_;
goto v___jp_1001_;
}
}
v___jp_1001_:
{
uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = lean_uint64_mix_hash(v___x_1000_, v___y_1002_);
v___x_1004_ = lean_uint64_mix_hash(v___x_999_, v___x_1003_);
v___x_1005_ = lean_uint64_mix_hash(v___x_998_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(v___x_1006_, 0, v_w_994_);
lean_ctor_set(v___x_1006_, 1, v_w_x27_995_);
lean_ctor_set(v___x_1006_, 2, v_n_996_);
lean_ctor_set(v___x_1006_, 3, v_expr_997_);
lean_ctor_set_uint64(v___x_1006_, sizeof(void*)*4, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* v_w_1013_, lean_object* v_w_x27_1014_, lean_object* v_n_1015_, lean_object* v_expr_1016_, lean_object* v_h_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_1013_, v_w_x27_1014_, v_n_1015_, v_expr_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* v_m_1019_, lean_object* v_n_1020_, lean_object* v_lhs_1021_, lean_object* v_rhs_1022_){
_start:
{
uint64_t v___x_1023_; uint64_t v___x_1024_; uint64_t v___y_1026_; uint64_t v___y_1027_; uint64_t v___y_1033_; 
v___x_1023_ = 29ULL;
v___x_1024_ = lean_uint64_of_nat(v_m_1019_);
switch(lean_obj_tag(v_lhs_1021_))
{
case 0:
{
uint64_t v_hashCode_1040_; 
v_hashCode_1040_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*2);
v___y_1033_ = v_hashCode_1040_;
goto v___jp_1032_;
}
case 1:
{
uint64_t v_hashCode_1041_; 
v_hashCode_1041_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*2);
v___y_1033_ = v_hashCode_1041_;
goto v___jp_1032_;
}
case 3:
{
uint64_t v_hashCode_1042_; 
v_hashCode_1042_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*3);
v___y_1033_ = v_hashCode_1042_;
goto v___jp_1032_;
}
case 4:
{
uint64_t v_hashCode_1043_; 
v_hashCode_1043_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*3);
v___y_1033_ = v_hashCode_1043_;
goto v___jp_1032_;
}
case 5:
{
uint64_t v_hashCode_1044_; 
v_hashCode_1044_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*5);
v___y_1033_ = v_hashCode_1044_;
goto v___jp_1032_;
}
default: 
{
uint64_t v_hashCode_1045_; 
v_hashCode_1045_ = lean_ctor_get_uint64(v_lhs_1021_, sizeof(void*)*4);
v___y_1033_ = v_hashCode_1045_;
goto v___jp_1032_;
}
}
v___jp_1025_:
{
uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = lean_uint64_mix_hash(v___y_1026_, v___y_1027_);
v___x_1029_ = lean_uint64_mix_hash(v___x_1024_, v___x_1028_);
v___x_1030_ = lean_uint64_mix_hash(v___x_1023_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(v___x_1031_, 0, v_m_1019_);
lean_ctor_set(v___x_1031_, 1, v_n_1020_);
lean_ctor_set(v___x_1031_, 2, v_lhs_1021_);
lean_ctor_set(v___x_1031_, 3, v_rhs_1022_);
lean_ctor_set_uint64(v___x_1031_, sizeof(void*)*4, v___x_1030_);
return v___x_1031_;
}
v___jp_1032_:
{
switch(lean_obj_tag(v_rhs_1022_))
{
case 0:
{
uint64_t v_hashCode_1034_; 
v_hashCode_1034_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*2);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1034_;
goto v___jp_1025_;
}
case 1:
{
uint64_t v_hashCode_1035_; 
v_hashCode_1035_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*2);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1035_;
goto v___jp_1025_;
}
case 3:
{
uint64_t v_hashCode_1036_; 
v_hashCode_1036_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*3);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1036_;
goto v___jp_1025_;
}
case 4:
{
uint64_t v_hashCode_1037_; 
v_hashCode_1037_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*3);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1037_;
goto v___jp_1025_;
}
case 5:
{
uint64_t v_hashCode_1038_; 
v_hashCode_1038_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*5);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1038_;
goto v___jp_1025_;
}
default: 
{
uint64_t v_hashCode_1039_; 
v_hashCode_1039_ = lean_ctor_get_uint64(v_rhs_1022_, sizeof(void*)*4);
v___y_1026_ = v___y_1033_;
v___y_1027_ = v_hashCode_1039_;
goto v___jp_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* v_m_1046_, lean_object* v_n_1047_, lean_object* v_lhs_1048_, lean_object* v_rhs_1049_){
_start:
{
uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v___y_1053_; uint64_t v___y_1054_; uint64_t v___y_1060_; 
v___x_1050_ = 31ULL;
v___x_1051_ = lean_uint64_of_nat(v_m_1046_);
switch(lean_obj_tag(v_lhs_1048_))
{
case 0:
{
uint64_t v_hashCode_1067_; 
v_hashCode_1067_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*2);
v___y_1060_ = v_hashCode_1067_;
goto v___jp_1059_;
}
case 1:
{
uint64_t v_hashCode_1068_; 
v_hashCode_1068_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*2);
v___y_1060_ = v_hashCode_1068_;
goto v___jp_1059_;
}
case 3:
{
uint64_t v_hashCode_1069_; 
v_hashCode_1069_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*3);
v___y_1060_ = v_hashCode_1069_;
goto v___jp_1059_;
}
case 4:
{
uint64_t v_hashCode_1070_; 
v_hashCode_1070_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*3);
v___y_1060_ = v_hashCode_1070_;
goto v___jp_1059_;
}
case 5:
{
uint64_t v_hashCode_1071_; 
v_hashCode_1071_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*5);
v___y_1060_ = v_hashCode_1071_;
goto v___jp_1059_;
}
default: 
{
uint64_t v_hashCode_1072_; 
v_hashCode_1072_ = lean_ctor_get_uint64(v_lhs_1048_, sizeof(void*)*4);
v___y_1060_ = v_hashCode_1072_;
goto v___jp_1059_;
}
}
v___jp_1052_:
{
uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_uint64_mix_hash(v___y_1053_, v___y_1054_);
v___x_1056_ = lean_uint64_mix_hash(v___x_1051_, v___x_1055_);
v___x_1057_ = lean_uint64_mix_hash(v___x_1050_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(v___x_1058_, 0, v_m_1046_);
lean_ctor_set(v___x_1058_, 1, v_n_1047_);
lean_ctor_set(v___x_1058_, 2, v_lhs_1048_);
lean_ctor_set(v___x_1058_, 3, v_rhs_1049_);
lean_ctor_set_uint64(v___x_1058_, sizeof(void*)*4, v___x_1057_);
return v___x_1058_;
}
v___jp_1059_:
{
switch(lean_obj_tag(v_rhs_1049_))
{
case 0:
{
uint64_t v_hashCode_1061_; 
v_hashCode_1061_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*2);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1061_;
goto v___jp_1052_;
}
case 1:
{
uint64_t v_hashCode_1062_; 
v_hashCode_1062_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*2);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1062_;
goto v___jp_1052_;
}
case 3:
{
uint64_t v_hashCode_1063_; 
v_hashCode_1063_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*3);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1063_;
goto v___jp_1052_;
}
case 4:
{
uint64_t v_hashCode_1064_; 
v_hashCode_1064_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*3);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1064_;
goto v___jp_1052_;
}
case 5:
{
uint64_t v_hashCode_1065_; 
v_hashCode_1065_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*5);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1065_;
goto v___jp_1052_;
}
default: 
{
uint64_t v_hashCode_1066_; 
v_hashCode_1066_ = lean_ctor_get_uint64(v_rhs_1049_, sizeof(void*)*4);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v_hashCode_1066_;
goto v___jp_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* v_m_1073_, lean_object* v_n_1074_, lean_object* v_lhs_1075_, lean_object* v_rhs_1076_){
_start:
{
uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___y_1080_; uint64_t v___y_1081_; uint64_t v___y_1087_; 
v___x_1077_ = 37ULL;
v___x_1078_ = lean_uint64_of_nat(v_m_1073_);
switch(lean_obj_tag(v_lhs_1075_))
{
case 0:
{
uint64_t v_hashCode_1094_; 
v_hashCode_1094_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*2);
v___y_1087_ = v_hashCode_1094_;
goto v___jp_1086_;
}
case 1:
{
uint64_t v_hashCode_1095_; 
v_hashCode_1095_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*2);
v___y_1087_ = v_hashCode_1095_;
goto v___jp_1086_;
}
case 3:
{
uint64_t v_hashCode_1096_; 
v_hashCode_1096_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*3);
v___y_1087_ = v_hashCode_1096_;
goto v___jp_1086_;
}
case 4:
{
uint64_t v_hashCode_1097_; 
v_hashCode_1097_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*3);
v___y_1087_ = v_hashCode_1097_;
goto v___jp_1086_;
}
case 5:
{
uint64_t v_hashCode_1098_; 
v_hashCode_1098_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*5);
v___y_1087_ = v_hashCode_1098_;
goto v___jp_1086_;
}
default: 
{
uint64_t v_hashCode_1099_; 
v_hashCode_1099_ = lean_ctor_get_uint64(v_lhs_1075_, sizeof(void*)*4);
v___y_1087_ = v_hashCode_1099_;
goto v___jp_1086_;
}
}
v___jp_1079_:
{
uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = lean_uint64_mix_hash(v___y_1080_, v___y_1081_);
v___x_1083_ = lean_uint64_mix_hash(v___x_1078_, v___x_1082_);
v___x_1084_ = lean_uint64_mix_hash(v___x_1077_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(v___x_1085_, 0, v_m_1073_);
lean_ctor_set(v___x_1085_, 1, v_n_1074_);
lean_ctor_set(v___x_1085_, 2, v_lhs_1075_);
lean_ctor_set(v___x_1085_, 3, v_rhs_1076_);
lean_ctor_set_uint64(v___x_1085_, sizeof(void*)*4, v___x_1084_);
return v___x_1085_;
}
v___jp_1086_:
{
switch(lean_obj_tag(v_rhs_1076_))
{
case 0:
{
uint64_t v_hashCode_1088_; 
v_hashCode_1088_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*2);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1088_;
goto v___jp_1079_;
}
case 1:
{
uint64_t v_hashCode_1089_; 
v_hashCode_1089_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*2);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1089_;
goto v___jp_1079_;
}
case 3:
{
uint64_t v_hashCode_1090_; 
v_hashCode_1090_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*3);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1090_;
goto v___jp_1079_;
}
case 4:
{
uint64_t v_hashCode_1091_; 
v_hashCode_1091_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*3);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1091_;
goto v___jp_1079_;
}
case 5:
{
uint64_t v_hashCode_1092_; 
v_hashCode_1092_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*5);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1092_;
goto v___jp_1079_;
}
default: 
{
uint64_t v_hashCode_1093_; 
v_hashCode_1093_ = lean_ctor_get_uint64(v_rhs_1076_, sizeof(void*)*4);
v___y_1080_ = v___y_1087_;
v___y_1081_ = v_hashCode_1093_;
goto v___jp_1079_;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* v_x_1100_){
_start:
{
switch(lean_obj_tag(v_x_1100_))
{
case 0:
{
uint64_t v_hashCode_1101_; 
v_hashCode_1101_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*2);
return v_hashCode_1101_;
}
case 1:
{
uint64_t v_hashCode_1102_; 
v_hashCode_1102_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*2);
return v_hashCode_1102_;
}
case 3:
{
uint64_t v_hashCode_1103_; 
v_hashCode_1103_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*3);
return v_hashCode_1103_;
}
case 4:
{
uint64_t v_hashCode_1104_; 
v_hashCode_1104_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*3);
return v_hashCode_1104_;
}
case 5:
{
uint64_t v_hashCode_1105_; 
v_hashCode_1105_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*5);
return v_hashCode_1105_;
}
default: 
{
uint64_t v_hashCode_1106_; 
v_hashCode_1106_ = lean_ctor_get_uint64(v_x_1100_, sizeof(void*)*4);
return v_hashCode_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* v_x_1107_){
_start:
{
uint64_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_1107_);
lean_dec_ref(v_x_1107_);
v_r_1109_ = lean_box_uint64(v_res_1108_);
return v_r_1109_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
switch(lean_obj_tag(v_x_1111_))
{
case 0:
{
uint64_t v_hashCode_1112_; 
v_hashCode_1112_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*2);
return v_hashCode_1112_;
}
case 1:
{
uint64_t v_hashCode_1113_; 
v_hashCode_1113_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*2);
return v_hashCode_1113_;
}
case 3:
{
uint64_t v_hashCode_1114_; 
v_hashCode_1114_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*3);
return v_hashCode_1114_;
}
case 4:
{
uint64_t v_hashCode_1115_; 
v_hashCode_1115_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*3);
return v_hashCode_1115_;
}
case 5:
{
uint64_t v_hashCode_1116_; 
v_hashCode_1116_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*5);
return v_hashCode_1116_;
}
default: 
{
uint64_t v_hashCode_1117_; 
v_hashCode_1117_ = lean_ctor_get_uint64(v_x_1111_, sizeof(void*)*4);
return v_hashCode_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* v_a_1118_, lean_object* v_x_1119_){
_start:
{
uint64_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_1118_, v_x_1119_);
lean_dec_ref(v_x_1119_);
lean_dec(v_a_1118_);
v_r_1121_ = lean_box_uint64(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(lean_object* v_expr_1122_){
_start:
{
switch(lean_obj_tag(v_expr_1122_))
{
case 0:
{
uint64_t v_hashCode_1123_; 
v_hashCode_1123_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*2);
return v_hashCode_1123_;
}
case 1:
{
uint64_t v_hashCode_1124_; 
v_hashCode_1124_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*2);
return v_hashCode_1124_;
}
case 3:
{
uint64_t v_hashCode_1125_; 
v_hashCode_1125_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*3);
return v_hashCode_1125_;
}
case 4:
{
uint64_t v_hashCode_1126_; 
v_hashCode_1126_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*3);
return v_hashCode_1126_;
}
case 5:
{
uint64_t v_hashCode_1127_; 
v_hashCode_1127_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*5);
return v_hashCode_1127_;
}
default: 
{
uint64_t v_hashCode_1128_; 
v_hashCode_1128_ = lean_ctor_get_uint64(v_expr_1122_, sizeof(void*)*4);
return v_hashCode_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0___boxed(lean_object* v_expr_1129_){
_start:
{
uint64_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___lam__0(v_expr_1129_);
lean_dec_ref(v_expr_1129_);
v_r_1131_ = lean_box_uint64(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg(){
_start:
{
lean_object* v___f_1134_; 
v___f_1134_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___boxed(lean_object* v___dummy_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg();
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* v_w_1137_){
_start:
{
lean_object* v___f_1138_; 
v___f_1138_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___redArg___closed__0));
return v___f_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* v_w_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_1139_);
lean_dec(v_w_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(lean_object* v_a_1141_, lean_object* v_b_1142_, lean_object* v_k_1143_){
_start:
{
size_t v___x_1144_; size_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_ptr_addr(v_a_1141_);
v___x_1145_ = lean_ptr_addr(v_b_1142_);
v___x_1146_ = lean_usize_dec_eq(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_apply_1(v_k_1143_, v___x_1147_);
v___x_1149_ = lean_unbox(v___x_1148_);
return v___x_1149_;
}
else
{
lean_dec_ref(v_k_1143_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg___boxed(lean_object* v_a_1150_, lean_object* v_b_1151_, lean_object* v_k_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___redArg(v_a_1150_, v_b_1151_, v_k_1152_);
lean_dec_ref(v_b_1151_);
lean_dec_ref(v_a_1150_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(lean_object* v_w_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_, lean_object* v_k_1158_, lean_object* v_h_1159_){
_start:
{
size_t v___x_1160_; size_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = lean_ptr_addr(v_a_1156_);
v___x_1161_ = lean_ptr_addr(v_b_1157_);
v___x_1162_ = lean_usize_dec_eq(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_apply_1(v_k_1158_, v___x_1163_);
v___x_1165_ = lean_unbox(v___x_1164_);
return v___x_1165_;
}
else
{
lean_dec_ref(v_k_1158_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe___boxed(lean_object* v_w_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_, lean_object* v_k_1169_, lean_object* v_h_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_withPtrEqUnsafe(v_w_1166_, v_a_1167_, v_b_1168_, v_k_1169_, v_h_1170_);
lean_dec_ref(v_b_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_w_1166_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* v_l_1173_, lean_object* v_r_1174_){
_start:
{
size_t v___x_1175_; size_t v___x_1176_; uint8_t v___x_1177_; uint64_t v___y_1179_; uint64_t v___y_1180_; uint64_t v___y_1265_; 
v___x_1175_ = lean_ptr_addr(v_l_1173_);
v___x_1176_ = lean_ptr_addr(v_r_1174_);
v___x_1177_ = lean_usize_dec_eq(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
switch(lean_obj_tag(v_l_1173_))
{
case 0:
{
uint64_t v_hashCode_1272_; 
v_hashCode_1272_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*2);
v___y_1265_ = v_hashCode_1272_;
goto v___jp_1264_;
}
case 1:
{
uint64_t v_hashCode_1273_; 
v_hashCode_1273_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*2);
v___y_1265_ = v_hashCode_1273_;
goto v___jp_1264_;
}
case 3:
{
uint64_t v_hashCode_1274_; 
v_hashCode_1274_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*3);
v___y_1265_ = v_hashCode_1274_;
goto v___jp_1264_;
}
case 4:
{
uint64_t v_hashCode_1275_; 
v_hashCode_1275_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*3);
v___y_1265_ = v_hashCode_1275_;
goto v___jp_1264_;
}
case 5:
{
uint64_t v_hashCode_1276_; 
v_hashCode_1276_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*5);
v___y_1265_ = v_hashCode_1276_;
goto v___jp_1264_;
}
default: 
{
uint64_t v_hashCode_1277_; 
v_hashCode_1277_ = lean_ctor_get_uint64(v_l_1173_, sizeof(void*)*4);
v___y_1265_ = v_hashCode_1277_;
goto v___jp_1264_;
}
}
}
else
{
return v___x_1177_;
}
v___jp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_uint64_dec_eq(v___y_1179_, v___y_1180_);
if (v___x_1181_ == 0)
{
return v___x_1177_;
}
else
{
if (v___x_1177_ == 0)
{
switch(lean_obj_tag(v_l_1173_))
{
case 0:
{
if (lean_obj_tag(v_r_1174_) == 0)
{
lean_object* v_idx_1182_; lean_object* v_idx_1183_; uint8_t v___x_1184_; 
v_idx_1182_ = lean_ctor_get(v_l_1173_, 1);
v_idx_1183_ = lean_ctor_get(v_r_1174_, 1);
v___x_1184_ = lean_nat_dec_eq(v_idx_1182_, v_idx_1183_);
return v___x_1184_;
}
else
{
return v___x_1177_;
}
}
case 1:
{
if (lean_obj_tag(v_r_1174_) == 1)
{
lean_object* v_val_1185_; lean_object* v_val_1186_; uint8_t v___x_1187_; 
v_val_1185_ = lean_ctor_get(v_l_1173_, 1);
v_val_1186_ = lean_ctor_get(v_r_1174_, 1);
v___x_1187_ = lean_nat_dec_eq(v_val_1185_, v_val_1186_);
return v___x_1187_;
}
else
{
return v___x_1177_;
}
}
case 2:
{
if (lean_obj_tag(v_r_1174_) == 2)
{
lean_object* v_w_1188_; lean_object* v_start_1189_; lean_object* v_expr_1190_; lean_object* v_w_1191_; lean_object* v_start_1192_; lean_object* v_expr_1193_; uint8_t v___x_1194_; 
v_w_1188_ = lean_ctor_get(v_l_1173_, 0);
v_start_1189_ = lean_ctor_get(v_l_1173_, 1);
v_expr_1190_ = lean_ctor_get(v_l_1173_, 3);
v_w_1191_ = lean_ctor_get(v_r_1174_, 0);
v_start_1192_ = lean_ctor_get(v_r_1174_, 1);
v_expr_1193_ = lean_ctor_get(v_r_1174_, 3);
v___x_1194_ = lean_nat_dec_eq(v_w_1188_, v_w_1191_);
if (v___x_1194_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_nat_dec_eq(v_start_1189_, v_start_1192_);
if (v___x_1195_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v_decide_1196_; 
v_decide_1196_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1190_, v_expr_1193_);
if (v_decide_1196_ == 0)
{
return v___x_1177_;
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
return v___x_1177_;
}
}
case 3:
{
if (lean_obj_tag(v_r_1174_) == 3)
{
lean_object* v_lhs_1197_; uint8_t v_op_1198_; lean_object* v_rhs_1199_; lean_object* v_lhs_1200_; uint8_t v_op_1201_; lean_object* v_rhs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_lhs_1197_ = lean_ctor_get(v_l_1173_, 1);
v_op_1198_ = lean_ctor_get_uint8(v_l_1173_, sizeof(void*)*3 + 8);
v_rhs_1199_ = lean_ctor_get(v_l_1173_, 2);
v_lhs_1200_ = lean_ctor_get(v_r_1174_, 1);
v_op_1201_ = lean_ctor_get_uint8(v_r_1174_, sizeof(void*)*3 + 8);
v_rhs_1202_ = lean_ctor_get(v_r_1174_, 2);
v___x_1203_ = lean_box(v_op_1198_);
v___x_1204_ = lean_obj_tag_nat(v___x_1203_);
lean_dec(v___x_1203_);
v___x_1205_ = lean_box(v_op_1201_);
v___x_1206_ = lean_obj_tag_nat(v___x_1205_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_nat_dec_eq(v___x_1204_, v___x_1206_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
uint8_t v_decide_1208_; 
v_decide_1208_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1197_, v_lhs_1200_);
if (v_decide_1208_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v_decide_1209_; 
v_decide_1209_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1199_, v_rhs_1202_);
if (v_decide_1209_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1207_;
}
}
}
}
else
{
return v___x_1177_;
}
}
case 4:
{
if (lean_obj_tag(v_r_1174_) == 4)
{
lean_object* v_op_1210_; lean_object* v_operand_1211_; lean_object* v_op_1212_; lean_object* v_operand_1213_; uint8_t v___x_1214_; 
v_op_1210_ = lean_ctor_get(v_l_1173_, 1);
v_operand_1211_ = lean_ctor_get(v_l_1173_, 2);
v_op_1212_ = lean_ctor_get(v_r_1174_, 1);
v_operand_1213_ = lean_ctor_get(v_r_1174_, 2);
v___x_1214_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_op_1210_, v_op_1212_);
if (v___x_1214_ == 0)
{
return v___x_1214_;
}
else
{
uint8_t v_decide_1215_; 
v_decide_1215_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_operand_1211_, v_operand_1213_);
if (v_decide_1215_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1214_;
}
}
}
else
{
return v___x_1177_;
}
}
case 5:
{
if (lean_obj_tag(v_r_1174_) == 5)
{
lean_object* v_l_1216_; lean_object* v_r_1217_; lean_object* v_lhs_1218_; lean_object* v_rhs_1219_; lean_object* v_l_1220_; lean_object* v_r_1221_; lean_object* v_lhs_1222_; lean_object* v_rhs_1223_; uint8_t v___x_1224_; 
v_l_1216_ = lean_ctor_get(v_l_1173_, 0);
v_r_1217_ = lean_ctor_get(v_l_1173_, 1);
v_lhs_1218_ = lean_ctor_get(v_l_1173_, 3);
v_rhs_1219_ = lean_ctor_get(v_l_1173_, 4);
v_l_1220_ = lean_ctor_get(v_r_1174_, 0);
v_r_1221_ = lean_ctor_get(v_r_1174_, 1);
v_lhs_1222_ = lean_ctor_get(v_r_1174_, 3);
v_rhs_1223_ = lean_ctor_get(v_r_1174_, 4);
v___x_1224_ = lean_nat_dec_eq(v_l_1216_, v_l_1220_);
if (v___x_1224_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_eq(v_r_1217_, v_r_1221_);
if (v___x_1225_ == 0)
{
return v___x_1225_;
}
else
{
uint8_t v_decide_1226_; 
v_decide_1226_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1218_, v_lhs_1222_);
if (v_decide_1226_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v_decide_1227_; 
v_decide_1227_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1219_, v_rhs_1223_);
if (v_decide_1227_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1225_;
}
}
}
}
}
else
{
return v___x_1177_;
}
}
case 6:
{
if (lean_obj_tag(v_r_1174_) == 6)
{
lean_object* v_w_1228_; lean_object* v_n_1229_; lean_object* v_expr_1230_; lean_object* v_w_1231_; lean_object* v_n_1232_; lean_object* v_expr_1233_; uint8_t v___x_1234_; 
v_w_1228_ = lean_ctor_get(v_l_1173_, 0);
v_n_1229_ = lean_ctor_get(v_l_1173_, 2);
v_expr_1230_ = lean_ctor_get(v_l_1173_, 3);
v_w_1231_ = lean_ctor_get(v_r_1174_, 0);
v_n_1232_ = lean_ctor_get(v_r_1174_, 2);
v_expr_1233_ = lean_ctor_get(v_r_1174_, 3);
v___x_1234_ = lean_nat_dec_eq(v_n_1229_, v_n_1232_);
if (v___x_1234_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_eq(v_w_1228_, v_w_1231_);
if (v___x_1235_ == 0)
{
return v___x_1235_;
}
else
{
uint8_t v_decide_1236_; 
v_decide_1236_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1230_, v_expr_1233_);
if (v_decide_1236_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1235_;
}
}
}
}
else
{
return v___x_1177_;
}
}
case 7:
{
if (lean_obj_tag(v_r_1174_) == 7)
{
lean_object* v_n_1237_; lean_object* v_lhs_1238_; lean_object* v_rhs_1239_; lean_object* v_n_1240_; lean_object* v_lhs_1241_; lean_object* v_rhs_1242_; uint8_t v___x_1243_; 
v_n_1237_ = lean_ctor_get(v_l_1173_, 1);
v_lhs_1238_ = lean_ctor_get(v_l_1173_, 2);
v_rhs_1239_ = lean_ctor_get(v_l_1173_, 3);
v_n_1240_ = lean_ctor_get(v_r_1174_, 1);
v_lhs_1241_ = lean_ctor_get(v_r_1174_, 2);
v_rhs_1242_ = lean_ctor_get(v_r_1174_, 3);
v___x_1243_ = lean_nat_dec_eq(v_n_1237_, v_n_1240_);
if (v___x_1243_ == 0)
{
return v___x_1243_;
}
else
{
uint8_t v_decide_1244_; 
v_decide_1244_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1238_, v_lhs_1241_);
if (v_decide_1244_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v_decide_1245_; 
v_decide_1245_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1239_, v_rhs_1242_);
if (v_decide_1245_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1243_;
}
}
}
}
else
{
return v___x_1177_;
}
}
case 8:
{
if (lean_obj_tag(v_r_1174_) == 8)
{
lean_object* v_n_1246_; lean_object* v_lhs_1247_; lean_object* v_rhs_1248_; lean_object* v_n_1249_; lean_object* v_lhs_1250_; lean_object* v_rhs_1251_; uint8_t v___x_1252_; 
v_n_1246_ = lean_ctor_get(v_l_1173_, 1);
v_lhs_1247_ = lean_ctor_get(v_l_1173_, 2);
v_rhs_1248_ = lean_ctor_get(v_l_1173_, 3);
v_n_1249_ = lean_ctor_get(v_r_1174_, 1);
v_lhs_1250_ = lean_ctor_get(v_r_1174_, 2);
v_rhs_1251_ = lean_ctor_get(v_r_1174_, 3);
v___x_1252_ = lean_nat_dec_eq(v_n_1246_, v_n_1249_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
uint8_t v_decide_1253_; 
v_decide_1253_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1247_, v_lhs_1250_);
if (v_decide_1253_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v_decide_1254_; 
v_decide_1254_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1248_, v_rhs_1251_);
if (v_decide_1254_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1252_;
}
}
}
}
else
{
return v___x_1177_;
}
}
default: 
{
if (lean_obj_tag(v_r_1174_) == 9)
{
lean_object* v_n_1255_; lean_object* v_lhs_1256_; lean_object* v_rhs_1257_; lean_object* v_n_1258_; lean_object* v_lhs_1259_; lean_object* v_rhs_1260_; uint8_t v___x_1261_; 
v_n_1255_ = lean_ctor_get(v_l_1173_, 1);
v_lhs_1256_ = lean_ctor_get(v_l_1173_, 2);
v_rhs_1257_ = lean_ctor_get(v_l_1173_, 3);
v_n_1258_ = lean_ctor_get(v_r_1174_, 1);
v_lhs_1259_ = lean_ctor_get(v_r_1174_, 2);
v_rhs_1260_ = lean_ctor_get(v_r_1174_, 3);
v___x_1261_ = lean_nat_dec_eq(v_n_1255_, v_n_1258_);
if (v___x_1261_ == 0)
{
return v___x_1261_;
}
else
{
uint8_t v_decide_1262_; 
v_decide_1262_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1256_, v_lhs_1259_);
if (v_decide_1262_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v_decide_1263_; 
v_decide_1263_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1257_, v_rhs_1260_);
if (v_decide_1263_ == 0)
{
return v___x_1177_;
}
else
{
return v___x_1261_;
}
}
}
}
else
{
return v___x_1177_;
}
}
}
}
else
{
return v___x_1177_;
}
}
}
v___jp_1264_:
{
switch(lean_obj_tag(v_r_1174_))
{
case 0:
{
uint64_t v_hashCode_1266_; 
v_hashCode_1266_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*2);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1266_;
goto v___jp_1178_;
}
case 1:
{
uint64_t v_hashCode_1267_; 
v_hashCode_1267_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*2);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1267_;
goto v___jp_1178_;
}
case 3:
{
uint64_t v_hashCode_1268_; 
v_hashCode_1268_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*3);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1268_;
goto v___jp_1178_;
}
case 4:
{
uint64_t v_hashCode_1269_; 
v_hashCode_1269_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*3);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1269_;
goto v___jp_1178_;
}
case 5:
{
uint64_t v_hashCode_1270_; 
v_hashCode_1270_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*5);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1270_;
goto v___jp_1178_;
}
default: 
{
uint64_t v_hashCode_1271_; 
v_hashCode_1271_ = lean_ctor_get_uint64(v_r_1174_, sizeof(void*)*4);
v___y_1179_ = v___y_1265_;
v___y_1180_ = v_hashCode_1271_;
goto v___jp_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* v_l_1278_, lean_object* v_r_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1278_, v_r_1279_);
lean_dec_ref(v_r_1279_);
lean_dec_ref(v_l_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* v_w_1282_, lean_object* v_l_1283_, lean_object* v_r_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_1283_, v_r_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* v_w_1286_, lean_object* v_l_1287_, lean_object* v_r_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_1286_, v_l_1287_, v_r_1288_);
lean_dec_ref(v_r_1288_);
lean_dec_ref(v_l_1287_);
lean_dec(v_w_1286_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* v_w_1300_, lean_object* v_x_1301_){
_start:
{
switch(lean_obj_tag(v_x_1301_))
{
case 0:
{
lean_object* v_idx_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_w_1300_);
v_idx_1302_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_idx_1302_);
lean_dec_ref_known(v_x_1301_, 2);
v___x_1303_ = ((lean_object*)(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1));
v___x_1304_ = l_Nat_reprFast(v_idx_1302_);
v___x_1305_ = lean_string_append(v___x_1303_, v___x_1304_);
lean_dec_ref(v___x_1304_);
return v___x_1305_;
}
case 1:
{
lean_object* v_val_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_val_1306_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_val_1306_);
lean_dec_ref_known(v_x_1301_, 2);
v___x_1307_ = l_BitVec_repr(v_w_1300_, v_val_1306_);
v___x_1308_ = l_Std_Format_defWidth;
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = l_Std_Format_pretty(v___x_1307_, v___x_1308_, v___x_1309_, v___x_1309_);
return v___x_1310_;
}
case 2:
{
lean_object* v_w_1311_; lean_object* v_start_1312_; lean_object* v_expr_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_w_1311_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_w_1311_);
v_start_1312_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_start_1312_);
v_expr_1313_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_expr_1313_);
lean_dec_ref_known(v_x_1301_, 4);
v___x_1314_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1311_, v_expr_1313_);
v___x_1315_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
v___x_1317_ = l_Nat_reprFast(v_start_1312_);
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0));
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
v___x_1321_ = l_Nat_reprFast(v_w_1300_);
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
return v___x_1324_;
}
case 3:
{
lean_object* v_lhs_1325_; uint8_t v_op_1326_; lean_object* v_rhs_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_lhs_1325_ = lean_ctor_get(v_x_1301_, 1);
lean_inc_ref(v_lhs_1325_);
v_op_1326_ = lean_ctor_get_uint8(v_x_1301_, sizeof(void*)*3 + 8);
v_rhs_1327_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_rhs_1327_);
lean_dec_ref_known(v_x_1301_, 3);
v___x_1328_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
lean_inc(v_w_1300_);
v___x_1329_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_lhs_1325_);
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1332_ = lean_string_append(v___x_1330_, v___x_1331_);
v___x_1333_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_1326_);
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = lean_string_append(v___x_1334_, v___x_1331_);
v___x_1336_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_rhs_1327_);
v___x_1337_ = lean_string_append(v___x_1335_, v___x_1336_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
return v___x_1339_;
}
case 4:
{
lean_object* v_op_1340_; lean_object* v_operand_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_op_1340_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_op_1340_);
v_operand_1341_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_operand_1341_);
lean_dec_ref_known(v_x_1301_, 3);
v___x_1342_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1343_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_1340_);
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
v___x_1347_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_operand_1341_);
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
return v___x_1350_;
}
case 5:
{
lean_object* v_l_1351_; lean_object* v_r_1352_; lean_object* v_lhs_1353_; lean_object* v_rhs_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_w_1300_);
v_l_1351_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_l_1351_);
v_r_1352_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_r_1352_);
v_lhs_1353_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_lhs_1353_);
v_rhs_1354_ = lean_ctor_get(v_x_1301_, 4);
lean_inc_ref(v_rhs_1354_);
lean_dec_ref_known(v_x_1301_, 5);
v___x_1355_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1356_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_1351_, v_lhs_1353_);
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4));
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
v___x_1360_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_1352_, v_rhs_1354_);
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
return v___x_1363_;
}
case 6:
{
lean_object* v_w_1364_; lean_object* v_n_1365_; lean_object* v_expr_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v_w_1300_);
v_w_1364_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_w_1364_);
v_n_1365_ = lean_ctor_get(v_x_1301_, 2);
lean_inc(v_n_1365_);
v_expr_1366_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_expr_1366_);
lean_dec_ref_known(v_x_1301_, 4);
v___x_1367_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5));
v___x_1368_ = l_Nat_reprFast(v_n_1365_);
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v___x_1372_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1364_, v_expr_1366_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
return v___x_1375_;
}
case 7:
{
lean_object* v_n_1376_; lean_object* v_lhs_1377_; lean_object* v_rhs_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_n_1376_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_n_1376_);
v_lhs_1377_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_lhs_1377_);
v_rhs_1378_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_rhs_1378_);
lean_dec_ref_known(v_x_1301_, 4);
v___x_1379_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1380_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_lhs_1377_);
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6));
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
v___x_1384_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1376_, v_rhs_1378_);
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
return v___x_1387_;
}
case 8:
{
lean_object* v_n_1388_; lean_object* v_lhs_1389_; lean_object* v_rhs_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_n_1388_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_n_1388_);
v_lhs_1389_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_lhs_1389_);
v_rhs_1390_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_rhs_1390_);
lean_dec_ref_known(v_x_1301_, 4);
v___x_1391_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1392_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_lhs_1389_);
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7));
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
v___x_1396_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1388_, v_rhs_1390_);
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
return v___x_1399_;
}
default: 
{
lean_object* v_n_1400_; lean_object* v_lhs_1401_; lean_object* v_rhs_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_n_1400_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_n_1400_);
v_lhs_1401_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_lhs_1401_);
v_rhs_1402_ = lean_ctor_get(v_x_1301_, 3);
lean_inc_ref(v_rhs_1402_);
lean_dec_ref_known(v_x_1301_, 4);
v___x_1403_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1404_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1300_, v_lhs_1401_);
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8));
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
v___x_1408_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_1400_, v_rhs_1402_);
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
return v___x_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* v_w_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(v___x_1413_, 0, v_w_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(lean_object* v_x_1418_){
_start:
{
lean_object* v_w_1419_; lean_object* v_bv_1420_; uint64_t v___x_1421_; uint64_t v___x_1422_; uint64_t v___x_1423_; uint64_t v___x_1424_; uint64_t v___x_1425_; 
v_w_1419_ = lean_ctor_get(v_x_1418_, 0);
v_bv_1420_ = lean_ctor_get(v_x_1418_, 1);
v___x_1421_ = 0ULL;
v___x_1422_ = lean_uint64_of_nat(v_w_1419_);
v___x_1423_ = lean_uint64_mix_hash(v___x_1421_, v___x_1422_);
v___x_1424_ = l_BitVec_hash(v_w_1419_, v_bv_1420_);
v___x_1425_ = lean_uint64_mix_hash(v___x_1423_, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash___boxed(lean_object* v_x_1426_){
_start:
{
uint64_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Std_Tactic_BVDecide_BVExpr_instHashablePackedBitVec_hash(v_x_1426_);
lean_dec_ref(v_x_1426_);
v_r_1428_ = lean_box_uint64(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v_w_1433_; lean_object* v_bv_1434_; lean_object* v_w_1435_; lean_object* v_bv_1436_; uint8_t v___x_1437_; 
v_w_1433_ = lean_ctor_get(v_x_1431_, 0);
v_bv_1434_ = lean_ctor_get(v_x_1431_, 1);
v_w_1435_ = lean_ctor_get(v_x_1432_, 0);
v_bv_1436_ = lean_ctor_get(v_x_1432_, 1);
v___x_1437_ = lean_nat_dec_eq(v_w_1433_, v_w_1435_);
if (v___x_1437_ == 0)
{
return v___x_1437_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_eq(v_bv_1434_, v_bv_1436_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_x_1439_, v_x_1440_);
lean_dec_ref(v_x_1440_);
lean_dec_ref(v_x_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_x_1443_, v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec___boxed(lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec(v_x_1446_, v_x_1447_);
lean_dec_ref(v_x_1447_);
lean_dec_ref(v_x_1446_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* v_assign_1450_, lean_object* v_idx_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_RArray_getImpl___redArg(v_assign_1450_, v_idx_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* v_assign_1453_, lean_object* v_idx_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_1453_, v_idx_1454_);
lean_dec(v_idx_1454_);
lean_dec_ref(v_assign_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* v_w_1456_, lean_object* v_assign_1457_, lean_object* v_x_1458_){
_start:
{
switch(lean_obj_tag(v_x_1458_))
{
case 0:
{
lean_object* v_idx_1459_; lean_object* v_packedBv_1460_; lean_object* v_w_1461_; lean_object* v_bv_1462_; uint8_t v___x_1463_; 
v_idx_1459_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_idx_1459_);
lean_dec_ref_known(v_x_1458_, 2);
v_packedBv_1460_ = l_Lean_RArray_getImpl___redArg(v_assign_1457_, v_idx_1459_);
lean_dec(v_idx_1459_);
v_w_1461_ = lean_ctor_get(v_packedBv_1460_, 0);
lean_inc(v_w_1461_);
v_bv_1462_ = lean_ctor_get(v_packedBv_1460_, 1);
lean_inc(v_bv_1462_);
lean_dec(v_packedBv_1460_);
v___x_1463_ = lean_nat_dec_eq(v_w_1461_, v_w_1456_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = l_BitVec_setWidth(v_w_1461_, v_w_1456_, v_bv_1462_);
lean_dec(v_bv_1462_);
lean_dec(v_w_1456_);
lean_dec(v_w_1461_);
return v___x_1464_;
}
else
{
lean_dec(v_w_1461_);
lean_dec(v_w_1456_);
return v_bv_1462_;
}
}
case 1:
{
lean_object* v_val_1465_; 
lean_dec(v_w_1456_);
v_val_1465_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_x_1458_, 2);
return v_val_1465_;
}
case 2:
{
lean_object* v_w_1466_; lean_object* v_start_1467_; lean_object* v_expr_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_w_1466_ = lean_ctor_get(v_x_1458_, 0);
lean_inc(v_w_1466_);
v_start_1467_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_start_1467_);
v_expr_1468_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_expr_1468_);
lean_dec_ref_known(v_x_1458_, 4);
v___x_1469_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1466_, v_assign_1457_, v_expr_1468_);
v___x_1470_ = l_BitVec_extractLsb_x27___redArg(v_start_1467_, v_w_1456_, v___x_1469_);
lean_dec(v___x_1469_);
lean_dec(v_w_1456_);
lean_dec(v_start_1467_);
return v___x_1470_;
}
case 3:
{
lean_object* v_lhs_1471_; uint8_t v_op_1472_; lean_object* v_rhs_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_lhs_1471_ = lean_ctor_get(v_x_1458_, 1);
lean_inc_ref(v_lhs_1471_);
v_op_1472_ = lean_ctor_get_uint8(v_x_1458_, sizeof(void*)*3 + 8);
v_rhs_1473_ = lean_ctor_get(v_x_1458_, 2);
lean_inc_ref(v_rhs_1473_);
lean_dec_ref_known(v_x_1458_, 3);
lean_inc_n(v_w_1456_, 2);
v___x_1474_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_lhs_1471_);
v___x_1475_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_rhs_1473_);
v___x_1476_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_1456_, v_op_1472_, v___x_1474_, v___x_1475_);
lean_dec(v___x_1475_);
lean_dec(v___x_1474_);
lean_dec(v_w_1456_);
return v___x_1476_;
}
case 4:
{
lean_object* v_op_1477_; lean_object* v_operand_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_op_1477_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_op_1477_);
v_operand_1478_ = lean_ctor_get(v_x_1458_, 2);
lean_inc_ref(v_operand_1478_);
lean_dec_ref_known(v_x_1458_, 3);
lean_inc(v_w_1456_);
v___x_1479_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_operand_1478_);
v___x_1480_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_1456_, v_op_1477_, v___x_1479_);
lean_dec(v_op_1477_);
return v___x_1480_;
}
case 5:
{
lean_object* v_l_1481_; lean_object* v_r_1482_; lean_object* v_lhs_1483_; lean_object* v_rhs_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v_w_1456_);
v_l_1481_ = lean_ctor_get(v_x_1458_, 0);
lean_inc(v_l_1481_);
v_r_1482_ = lean_ctor_get(v_x_1458_, 1);
lean_inc_n(v_r_1482_, 2);
v_lhs_1483_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_lhs_1483_);
v_rhs_1484_ = lean_ctor_get(v_x_1458_, 4);
lean_inc_ref(v_rhs_1484_);
lean_dec_ref_known(v_x_1458_, 5);
v___x_1485_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_1481_, v_assign_1457_, v_lhs_1483_);
v___x_1486_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_1482_, v_assign_1457_, v_rhs_1484_);
v___x_1487_ = l_BitVec_append___redArg(v_r_1482_, v___x_1485_, v___x_1486_);
lean_dec(v___x_1486_);
lean_dec(v___x_1485_);
lean_dec(v_r_1482_);
return v___x_1487_;
}
case 6:
{
lean_object* v_w_1488_; lean_object* v_n_1489_; lean_object* v_expr_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_w_1456_);
v_w_1488_ = lean_ctor_get(v_x_1458_, 0);
lean_inc_n(v_w_1488_, 2);
v_n_1489_ = lean_ctor_get(v_x_1458_, 2);
lean_inc(v_n_1489_);
v_expr_1490_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_expr_1490_);
lean_dec_ref_known(v_x_1458_, 4);
v___x_1491_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1488_, v_assign_1457_, v_expr_1490_);
v___x_1492_ = l_BitVec_replicate(v_w_1488_, v_n_1489_, v___x_1491_);
lean_dec(v___x_1491_);
lean_dec(v_n_1489_);
lean_dec(v_w_1488_);
return v___x_1492_;
}
case 7:
{
lean_object* v_n_1493_; lean_object* v_lhs_1494_; lean_object* v_rhs_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_n_1493_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_n_1493_);
v_lhs_1494_ = lean_ctor_get(v_x_1458_, 2);
lean_inc_ref(v_lhs_1494_);
v_rhs_1495_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_rhs_1495_);
lean_dec_ref_known(v_x_1458_, 4);
lean_inc(v_w_1456_);
v___x_1496_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_lhs_1494_);
v___x_1497_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1493_, v_assign_1457_, v_rhs_1495_);
v___x_1498_ = l_BitVec_shiftLeft(v_w_1456_, v___x_1496_, v___x_1497_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec(v_w_1456_);
return v___x_1498_;
}
case 8:
{
lean_object* v_n_1499_; lean_object* v_lhs_1500_; lean_object* v_rhs_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_n_1499_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_n_1499_);
v_lhs_1500_ = lean_ctor_get(v_x_1458_, 2);
lean_inc_ref(v_lhs_1500_);
v_rhs_1501_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_rhs_1501_);
lean_dec_ref_known(v_x_1458_, 4);
v___x_1502_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_lhs_1500_);
v___x_1503_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1499_, v_assign_1457_, v_rhs_1501_);
v___x_1504_ = lean_nat_shiftr(v___x_1502_, v___x_1503_);
lean_dec(v___x_1503_);
lean_dec(v___x_1502_);
return v___x_1504_;
}
default: 
{
lean_object* v_n_1505_; lean_object* v_lhs_1506_; lean_object* v_rhs_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_n_1505_ = lean_ctor_get(v_x_1458_, 1);
lean_inc(v_n_1505_);
v_lhs_1506_ = lean_ctor_get(v_x_1458_, 2);
lean_inc_ref(v_lhs_1506_);
v_rhs_1507_ = lean_ctor_get(v_x_1458_, 3);
lean_inc_ref(v_rhs_1507_);
lean_dec_ref_known(v_x_1458_, 4);
lean_inc(v_w_1456_);
v___x_1508_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1456_, v_assign_1457_, v_lhs_1506_);
v___x_1509_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_1505_, v_assign_1457_, v_rhs_1507_);
v___x_1510_ = l_BitVec_sshiftRight(v_w_1456_, v___x_1508_, v___x_1509_);
lean_dec(v___x_1509_);
lean_dec(v_w_1456_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* v_w_1511_, lean_object* v_assign_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1511_, v_assign_1512_, v_x_1513_);
lean_dec_ref(v_assign_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* v_w_1515_, lean_object* v_x_1516_, lean_object* v_h__1_1517_, lean_object* v_h__2_1518_, lean_object* v_h__3_1519_, lean_object* v_h__4_1520_, lean_object* v_h__5_1521_, lean_object* v_h__6_1522_, lean_object* v_h__7_1523_, lean_object* v_h__8_1524_, lean_object* v_h__9_1525_, lean_object* v_h__10_1526_){
_start:
{
switch(lean_obj_tag(v_x_1516_))
{
case 0:
{
lean_object* v_idx_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
v_idx_1527_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_idx_1527_);
lean_dec_ref_known(v_x_1516_, 2);
v___x_1528_ = lean_apply_2(v_h__1_1517_, v_w_1515_, v_idx_1527_);
return v___x_1528_;
}
case 1:
{
lean_object* v_val_1529_; lean_object* v___x_1530_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__1_1517_);
v_val_1529_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_val_1529_);
lean_dec_ref_known(v_x_1516_, 2);
v___x_1530_ = lean_apply_2(v_h__2_1518_, v_w_1515_, v_val_1529_);
return v___x_1530_;
}
case 2:
{
lean_object* v_w_1531_; lean_object* v_start_1532_; lean_object* v_expr_1533_; lean_object* v___x_1534_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_w_1531_ = lean_ctor_get(v_x_1516_, 0);
lean_inc(v_w_1531_);
v_start_1532_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_start_1532_);
v_expr_1533_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_expr_1533_);
lean_dec_ref_known(v_x_1516_, 4);
v___x_1534_ = lean_apply_4(v_h__3_1519_, v_w_1515_, v_w_1531_, v_start_1532_, v_expr_1533_);
return v___x_1534_;
}
case 3:
{
lean_object* v_lhs_1535_; uint8_t v_op_1536_; lean_object* v_rhs_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_lhs_1535_ = lean_ctor_get(v_x_1516_, 1);
lean_inc_ref(v_lhs_1535_);
v_op_1536_ = lean_ctor_get_uint8(v_x_1516_, sizeof(void*)*3 + 8);
v_rhs_1537_ = lean_ctor_get(v_x_1516_, 2);
lean_inc_ref(v_rhs_1537_);
lean_dec_ref_known(v_x_1516_, 3);
v___x_1538_ = lean_box(v_op_1536_);
v___x_1539_ = lean_apply_4(v_h__4_1520_, v_w_1515_, v_lhs_1535_, v___x_1538_, v_rhs_1537_);
return v___x_1539_;
}
case 4:
{
lean_object* v_op_1540_; lean_object* v_operand_1541_; lean_object* v___x_1542_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_op_1540_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_op_1540_);
v_operand_1541_ = lean_ctor_get(v_x_1516_, 2);
lean_inc_ref(v_operand_1541_);
lean_dec_ref_known(v_x_1516_, 3);
v___x_1542_ = lean_apply_3(v_h__5_1521_, v_w_1515_, v_op_1540_, v_operand_1541_);
return v___x_1542_;
}
case 5:
{
lean_object* v_l_1543_; lean_object* v_r_1544_; lean_object* v_lhs_1545_; lean_object* v_rhs_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_l_1543_ = lean_ctor_get(v_x_1516_, 0);
lean_inc(v_l_1543_);
v_r_1544_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_r_1544_);
v_lhs_1545_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_lhs_1545_);
v_rhs_1546_ = lean_ctor_get(v_x_1516_, 4);
lean_inc_ref(v_rhs_1546_);
lean_dec_ref_known(v_x_1516_, 5);
v___x_1547_ = lean_apply_6(v_h__6_1522_, v_w_1515_, v_l_1543_, v_r_1544_, v_lhs_1545_, v_rhs_1546_, lean_box(0));
return v___x_1547_;
}
case 6:
{
lean_object* v_w_1548_; lean_object* v_n_1549_; lean_object* v_expr_1550_; lean_object* v___x_1551_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_w_1548_ = lean_ctor_get(v_x_1516_, 0);
lean_inc(v_w_1548_);
v_n_1549_ = lean_ctor_get(v_x_1516_, 2);
lean_inc(v_n_1549_);
v_expr_1550_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_expr_1550_);
lean_dec_ref_known(v_x_1516_, 4);
v___x_1551_ = lean_apply_5(v_h__7_1523_, v_w_1515_, v_w_1548_, v_n_1549_, v_expr_1550_, lean_box(0));
return v___x_1551_;
}
case 7:
{
lean_object* v_n_1552_; lean_object* v_lhs_1553_; lean_object* v_rhs_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__9_1525_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_n_1552_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_n_1552_);
v_lhs_1553_ = lean_ctor_get(v_x_1516_, 2);
lean_inc_ref(v_lhs_1553_);
v_rhs_1554_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_rhs_1554_);
lean_dec_ref_known(v_x_1516_, 4);
v___x_1555_ = lean_apply_4(v_h__8_1524_, v_w_1515_, v_n_1552_, v_lhs_1553_, v_rhs_1554_);
return v___x_1555_;
}
case 8:
{
lean_object* v_n_1556_; lean_object* v_lhs_1557_; lean_object* v_rhs_1558_; lean_object* v___x_1559_; 
lean_dec(v_h__10_1526_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_n_1556_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_n_1556_);
v_lhs_1557_ = lean_ctor_get(v_x_1516_, 2);
lean_inc_ref(v_lhs_1557_);
v_rhs_1558_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_rhs_1558_);
lean_dec_ref_known(v_x_1516_, 4);
v___x_1559_ = lean_apply_4(v_h__9_1525_, v_w_1515_, v_n_1556_, v_lhs_1557_, v_rhs_1558_);
return v___x_1559_;
}
default: 
{
lean_object* v_n_1560_; lean_object* v_lhs_1561_; lean_object* v_rhs_1562_; lean_object* v___x_1563_; 
lean_dec(v_h__9_1525_);
lean_dec(v_h__8_1524_);
lean_dec(v_h__7_1523_);
lean_dec(v_h__6_1522_);
lean_dec(v_h__5_1521_);
lean_dec(v_h__4_1520_);
lean_dec(v_h__3_1519_);
lean_dec(v_h__2_1518_);
lean_dec(v_h__1_1517_);
v_n_1560_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_n_1560_);
v_lhs_1561_ = lean_ctor_get(v_x_1516_, 2);
lean_inc_ref(v_lhs_1561_);
v_rhs_1562_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_rhs_1562_);
lean_dec_ref_known(v_x_1516_, 4);
v___x_1563_ = lean_apply_4(v_h__10_1526_, v_w_1515_, v_n_1560_, v_lhs_1561_, v_rhs_1562_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* v_motive_1564_, lean_object* v_w_1565_, lean_object* v_x_1566_, lean_object* v_h__1_1567_, lean_object* v_h__2_1568_, lean_object* v_h__3_1569_, lean_object* v_h__4_1570_, lean_object* v_h__5_1571_, lean_object* v_h__6_1572_, lean_object* v_h__7_1573_, lean_object* v_h__8_1574_, lean_object* v_h__9_1575_, lean_object* v_h__10_1576_){
_start:
{
switch(lean_obj_tag(v_x_1566_))
{
case 0:
{
lean_object* v_idx_1577_; lean_object* v___x_1578_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
v_idx_1577_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_idx_1577_);
lean_dec_ref_known(v_x_1566_, 2);
v___x_1578_ = lean_apply_2(v_h__1_1567_, v_w_1565_, v_idx_1577_);
return v___x_1578_;
}
case 1:
{
lean_object* v_val_1579_; lean_object* v___x_1580_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__1_1567_);
v_val_1579_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_x_1566_, 2);
v___x_1580_ = lean_apply_2(v_h__2_1568_, v_w_1565_, v_val_1579_);
return v___x_1580_;
}
case 2:
{
lean_object* v_w_1581_; lean_object* v_start_1582_; lean_object* v_expr_1583_; lean_object* v___x_1584_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_w_1581_ = lean_ctor_get(v_x_1566_, 0);
lean_inc(v_w_1581_);
v_start_1582_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_start_1582_);
v_expr_1583_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_expr_1583_);
lean_dec_ref_known(v_x_1566_, 4);
v___x_1584_ = lean_apply_4(v_h__3_1569_, v_w_1565_, v_w_1581_, v_start_1582_, v_expr_1583_);
return v___x_1584_;
}
case 3:
{
lean_object* v_lhs_1585_; uint8_t v_op_1586_; lean_object* v_rhs_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_lhs_1585_ = lean_ctor_get(v_x_1566_, 1);
lean_inc_ref(v_lhs_1585_);
v_op_1586_ = lean_ctor_get_uint8(v_x_1566_, sizeof(void*)*3 + 8);
v_rhs_1587_ = lean_ctor_get(v_x_1566_, 2);
lean_inc_ref(v_rhs_1587_);
lean_dec_ref_known(v_x_1566_, 3);
v___x_1588_ = lean_box(v_op_1586_);
v___x_1589_ = lean_apply_4(v_h__4_1570_, v_w_1565_, v_lhs_1585_, v___x_1588_, v_rhs_1587_);
return v___x_1589_;
}
case 4:
{
lean_object* v_op_1590_; lean_object* v_operand_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_op_1590_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_op_1590_);
v_operand_1591_ = lean_ctor_get(v_x_1566_, 2);
lean_inc_ref(v_operand_1591_);
lean_dec_ref_known(v_x_1566_, 3);
v___x_1592_ = lean_apply_3(v_h__5_1571_, v_w_1565_, v_op_1590_, v_operand_1591_);
return v___x_1592_;
}
case 5:
{
lean_object* v_l_1593_; lean_object* v_r_1594_; lean_object* v_lhs_1595_; lean_object* v_rhs_1596_; lean_object* v___x_1597_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_l_1593_ = lean_ctor_get(v_x_1566_, 0);
lean_inc(v_l_1593_);
v_r_1594_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_r_1594_);
v_lhs_1595_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_lhs_1595_);
v_rhs_1596_ = lean_ctor_get(v_x_1566_, 4);
lean_inc_ref(v_rhs_1596_);
lean_dec_ref_known(v_x_1566_, 5);
v___x_1597_ = lean_apply_6(v_h__6_1572_, v_w_1565_, v_l_1593_, v_r_1594_, v_lhs_1595_, v_rhs_1596_, lean_box(0));
return v___x_1597_;
}
case 6:
{
lean_object* v_w_1598_; lean_object* v_n_1599_; lean_object* v_expr_1600_; lean_object* v___x_1601_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_w_1598_ = lean_ctor_get(v_x_1566_, 0);
lean_inc(v_w_1598_);
v_n_1599_ = lean_ctor_get(v_x_1566_, 2);
lean_inc(v_n_1599_);
v_expr_1600_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_expr_1600_);
lean_dec_ref_known(v_x_1566_, 4);
v___x_1601_ = lean_apply_5(v_h__7_1573_, v_w_1565_, v_w_1598_, v_n_1599_, v_expr_1600_, lean_box(0));
return v___x_1601_;
}
case 7:
{
lean_object* v_n_1602_; lean_object* v_lhs_1603_; lean_object* v_rhs_1604_; lean_object* v___x_1605_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__9_1575_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_n_1602_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_n_1602_);
v_lhs_1603_ = lean_ctor_get(v_x_1566_, 2);
lean_inc_ref(v_lhs_1603_);
v_rhs_1604_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_rhs_1604_);
lean_dec_ref_known(v_x_1566_, 4);
v___x_1605_ = lean_apply_4(v_h__8_1574_, v_w_1565_, v_n_1602_, v_lhs_1603_, v_rhs_1604_);
return v___x_1605_;
}
case 8:
{
lean_object* v_n_1606_; lean_object* v_lhs_1607_; lean_object* v_rhs_1608_; lean_object* v___x_1609_; 
lean_dec(v_h__10_1576_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_n_1606_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_n_1606_);
v_lhs_1607_ = lean_ctor_get(v_x_1566_, 2);
lean_inc_ref(v_lhs_1607_);
v_rhs_1608_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_rhs_1608_);
lean_dec_ref_known(v_x_1566_, 4);
v___x_1609_ = lean_apply_4(v_h__9_1575_, v_w_1565_, v_n_1606_, v_lhs_1607_, v_rhs_1608_);
return v___x_1609_;
}
default: 
{
lean_object* v_n_1610_; lean_object* v_lhs_1611_; lean_object* v_rhs_1612_; lean_object* v___x_1613_; 
lean_dec(v_h__9_1575_);
lean_dec(v_h__8_1574_);
lean_dec(v_h__7_1573_);
lean_dec(v_h__6_1572_);
lean_dec(v_h__5_1571_);
lean_dec(v_h__4_1570_);
lean_dec(v_h__3_1569_);
lean_dec(v_h__2_1568_);
lean_dec(v_h__1_1567_);
v_n_1610_ = lean_ctor_get(v_x_1566_, 1);
lean_inc(v_n_1610_);
v_lhs_1611_ = lean_ctor_get(v_x_1566_, 2);
lean_inc_ref(v_lhs_1611_);
v_rhs_1612_ = lean_ctor_get(v_x_1566_, 3);
lean_inc_ref(v_rhs_1612_);
lean_dec_ref_known(v_x_1566_, 4);
v___x_1613_ = lean_apply_4(v_h__10_1576_, v_w_1565_, v_n_1610_, v_lhs_1611_, v_rhs_1612_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(uint8_t v_x_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_box(v_x_1614_);
v___x_1616_ = lean_obj_tag_nat(v___x_1615_);
lean_dec(v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl___boxed(lean_object* v_x_1617_){
_start:
{
uint8_t v_x_4__boxed_1618_; lean_object* v_res_1619_; 
v_x_4__boxed_1618_ = lean_unbox(v_x_1617_);
v_res_1619_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___impl(v_x_4__boxed_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(lean_object* v_k_1620_){
_start:
{
lean_inc(v_k_1620_);
return v_k_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(lean_object* v_k_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_1621_);
lean_dec(v_k_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim(lean_object* v_motive_1623_, lean_object* v_ctorIdx_1624_, uint8_t v_t_1625_, lean_object* v_h_1626_, lean_object* v_k_1627_){
_start:
{
lean_inc(v_k_1627_);
return v_k_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(lean_object* v_motive_1628_, lean_object* v_ctorIdx_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_k_1632_){
_start:
{
uint8_t v_t_boxed_1633_; lean_object* v_res_1634_; 
v_t_boxed_1633_ = lean_unbox(v_t_1630_);
v_res_1634_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(v_motive_1628_, v_ctorIdx_1629_, v_t_boxed_1633_, v_h_1631_, v_k_1632_);
lean_dec(v_k_1632_);
lean_dec(v_ctorIdx_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(lean_object* v_eq_1635_){
_start:
{
lean_inc(v_eq_1635_);
return v_eq_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(lean_object* v_eq_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_1636_);
lean_dec(v_eq_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim(lean_object* v_motive_1638_, uint8_t v_t_1639_, lean_object* v_h_1640_, lean_object* v_eq_1641_){
_start:
{
lean_inc(v_eq_1641_);
return v_eq_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_eq_1645_){
_start:
{
uint8_t v_t_boxed_1646_; lean_object* v_res_1647_; 
v_t_boxed_1646_ = lean_unbox(v_t_1643_);
v_res_1647_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(v_motive_1642_, v_t_boxed_1646_, v_h_1644_, v_eq_1645_);
lean_dec(v_eq_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(lean_object* v_ult_1648_){
_start:
{
lean_inc(v_ult_1648_);
return v_ult_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(lean_object* v_ult_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_1649_);
lean_dec(v_ult_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim(lean_object* v_motive_1651_, uint8_t v_t_1652_, lean_object* v_h_1653_, lean_object* v_ult_1654_){
_start:
{
lean_inc(v_ult_1654_);
return v_ult_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(lean_object* v_motive_1655_, lean_object* v_t_1656_, lean_object* v_h_1657_, lean_object* v_ult_1658_){
_start:
{
uint8_t v_t_boxed_1659_; lean_object* v_res_1660_; 
v_t_boxed_1659_ = lean_unbox(v_t_1656_);
v_res_1660_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(v_motive_1655_, v_t_boxed_1659_, v_h_1657_, v_ult_1658_);
lean_dec(v_ult_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_ofNat(lean_object* v_n_1661_){
_start:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_nat_dec_le(v_n_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
uint8_t v___x_1664_; 
v___x_1664_ = 1;
return v___x_1664_;
}
else
{
uint8_t v___x_1665_; 
v___x_1665_ = 0;
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_ofNat___boxed(lean_object* v_n_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Std_Tactic_BVDecide_BVBinPred_ofNat(v_n_1666_);
lean_dec(v_n_1666_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(uint8_t v_x_1669_, uint8_t v_y_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1671_ = lean_box(v_x_1669_);
v___x_1672_ = lean_obj_tag_nat(v___x_1671_);
lean_dec(v___x_1671_);
v___x_1673_ = lean_box(v_y_1670_);
v___x_1674_ = lean_obj_tag_nat(v___x_1673_);
lean_dec(v___x_1673_);
v___x_1675_ = lean_nat_dec_eq(v___x_1672_, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinPred___boxed(lean_object* v_x_1676_, lean_object* v_y_1677_){
_start:
{
uint8_t v_x_23__boxed_1678_; uint8_t v_y_24__boxed_1679_; uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_x_23__boxed_1678_ = lean_unbox(v_x_1676_);
v_y_24__boxed_1679_ = lean_unbox(v_y_1677_);
v_res_1680_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinPred(v_x_23__boxed_1678_, v_y_24__boxed_1679_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(uint8_t v_x_1682_){
_start:
{
if (v_x_1682_ == 0)
{
uint64_t v___x_1683_; 
v___x_1683_ = 0ULL;
return v___x_1683_;
}
else
{
uint64_t v___x_1684_; 
v___x_1684_ = 1ULL;
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinPred_hash___boxed(lean_object* v_x_1685_){
_start:
{
uint8_t v_x_28__boxed_1686_; uint64_t v_res_1687_; lean_object* v_r_1688_; 
v_x_28__boxed_1686_ = lean_unbox(v_x_1685_);
v_res_1687_ = l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(v_x_28__boxed_1686_);
v_r_1688_ = lean_box_uint64(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t v_x_1693_){
_start:
{
if (v_x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0));
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1));
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* v_x_1696_){
_start:
{
uint8_t v_x_22__boxed_1697_; lean_object* v_res_1698_; 
v_x_22__boxed_1697_ = lean_unbox(v_x_1696_);
v_res_1698_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t v_x_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
if (v_x_1701_ == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_nat_dec_eq(v_a_1702_, v_a_1703_);
return v___x_1704_;
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_lt(v_a_1702_, v_a_1703_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(lean_object* v_x_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_x_70__boxed_1709_; uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_x_70__boxed_1709_ = lean_unbox(v_x_1706_);
v_res_1710_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_70__boxed_1709_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* v_w_1712_, uint8_t v_x_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_1713_, v_a_1714_, v_a_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* v_w_1717_, lean_object* v_x_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
uint8_t v_x_83__boxed_1721_; uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_x_83__boxed_1721_ = lean_unbox(v_x_1718_);
v_res_1722_ = l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_1717_, v_x_83__boxed_1721_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec(v_w_1717_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl(lean_object* v_x_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_obj_tag_nat(v_x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl___boxed(lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx___impl(v_x_1726_);
lean_dec_ref(v_x_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(lean_object* v_t_1728_, lean_object* v_k_1729_){
_start:
{
if (lean_obj_tag(v_t_1728_) == 0)
{
lean_object* v_w_1730_; lean_object* v_lhs_1731_; uint8_t v_op_1732_; lean_object* v_rhs_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_w_1730_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_w_1730_);
v_lhs_1731_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_lhs_1731_);
v_op_1732_ = lean_ctor_get_uint8(v_t_1728_, sizeof(void*)*3);
v_rhs_1733_ = lean_ctor_get(v_t_1728_, 2);
lean_inc_ref(v_rhs_1733_);
lean_dec_ref_known(v_t_1728_, 3);
v___x_1734_ = lean_box(v_op_1732_);
v___x_1735_ = lean_apply_4(v_k_1729_, v_w_1730_, v_lhs_1731_, v___x_1734_, v_rhs_1733_);
return v___x_1735_;
}
else
{
lean_object* v_w_1736_; lean_object* v_expr_1737_; lean_object* v_idx_1738_; lean_object* v___x_1739_; 
v_w_1736_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_w_1736_);
v_expr_1737_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_expr_1737_);
v_idx_1738_ = lean_ctor_get(v_t_1728_, 2);
lean_inc(v_idx_1738_);
lean_dec_ref_known(v_t_1728_, 3);
v___x_1739_ = lean_apply_3(v_k_1729_, v_w_1736_, v_expr_1737_, v_idx_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim(lean_object* v_motive_1740_, lean_object* v_ctorIdx_1741_, lean_object* v_t_1742_, lean_object* v_h_1743_, lean_object* v_k_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1742_, v_k_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(lean_object* v_motive_1746_, lean_object* v_ctorIdx_1747_, lean_object* v_t_1748_, lean_object* v_h_1749_, lean_object* v_k_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(v_motive_1746_, v_ctorIdx_1747_, v_t_1748_, v_h_1749_, v_k_1750_);
lean_dec(v_ctorIdx_1747_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(lean_object* v_t_1752_, lean_object* v_bin_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1752_, v_bin_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bin_elim(lean_object* v_motive_1755_, lean_object* v_t_1756_, lean_object* v_h_1757_, lean_object* v_bin_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1756_, v_bin_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(lean_object* v_t_1760_, lean_object* v_getLsbD_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1760_, v_getLsbD_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(lean_object* v_motive_1763_, lean_object* v_t_1764_, lean_object* v_h_1765_, lean_object* v_getLsbD_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_1764_, v_getLsbD_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
if (lean_obj_tag(v_x_1768_) == 0)
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v_w_1770_; lean_object* v_lhs_1771_; uint8_t v_op_1772_; lean_object* v_rhs_1773_; lean_object* v_w_1774_; lean_object* v_lhs_1775_; uint8_t v_op_1776_; lean_object* v_rhs_1777_; uint8_t v___x_1778_; 
v_w_1770_ = lean_ctor_get(v_x_1768_, 0);
v_lhs_1771_ = lean_ctor_get(v_x_1768_, 1);
v_op_1772_ = lean_ctor_get_uint8(v_x_1768_, sizeof(void*)*3);
v_rhs_1773_ = lean_ctor_get(v_x_1768_, 2);
v_w_1774_ = lean_ctor_get(v_x_1769_, 0);
v_lhs_1775_ = lean_ctor_get(v_x_1769_, 1);
v_op_1776_ = lean_ctor_get_uint8(v_x_1769_, sizeof(void*)*3);
v_rhs_1777_ = lean_ctor_get(v_x_1769_, 2);
v___x_1778_ = lean_nat_dec_eq(v_w_1770_, v_w_1774_);
if (v___x_1778_ == 0)
{
return v___x_1778_;
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_lhs_1771_, v_lhs_1775_);
if (v___x_1779_ == 0)
{
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1780_ = lean_box(v_op_1772_);
v___x_1781_ = lean_obj_tag_nat(v___x_1780_);
lean_dec(v___x_1780_);
v___x_1782_ = lean_box(v_op_1776_);
v___x_1783_ = lean_obj_tag_nat(v___x_1782_);
lean_dec(v___x_1782_);
v___x_1784_ = lean_nat_dec_eq(v___x_1781_, v___x_1783_);
if (v___x_1784_ == 0)
{
return v___x_1784_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_rhs_1773_, v_rhs_1777_);
return v___x_1785_;
}
}
}
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = 0;
return v___x_1786_;
}
}
else
{
if (lean_obj_tag(v_x_1769_) == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = 0;
return v___x_1787_;
}
else
{
lean_object* v_w_1788_; lean_object* v_expr_1789_; lean_object* v_idx_1790_; lean_object* v_w_1791_; lean_object* v_expr_1792_; lean_object* v_idx_1793_; uint8_t v___x_1794_; 
v_w_1788_ = lean_ctor_get(v_x_1768_, 0);
v_expr_1789_ = lean_ctor_get(v_x_1768_, 1);
v_idx_1790_ = lean_ctor_get(v_x_1768_, 2);
v_w_1791_ = lean_ctor_get(v_x_1769_, 0);
v_expr_1792_ = lean_ctor_get(v_x_1769_, 1);
v_idx_1793_ = lean_ctor_get(v_x_1769_, 2);
v___x_1794_ = lean_nat_dec_eq(v_w_1788_, v_w_1791_);
if (v___x_1794_ == 0)
{
return v___x_1794_;
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_expr_1789_, v_expr_1792_);
if (v___x_1795_ == 0)
{
return v___x_1795_;
}
else
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_nat_dec_eq(v_idx_1790_, v_idx_1793_);
return v___x_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq___boxed(lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(v_x_1797_, v_x_1798_);
lean_dec_ref(v_x_1798_);
lean_dec_ref(v_x_1797_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVPred(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred_decEq(v_x_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVPred___boxed(lean_object* v_x_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_res_1806_ = l_Std_Tactic_BVDecide_instDecidableEqBVPred(v_x_1804_, v_x_1805_);
lean_dec_ref(v_x_1805_);
lean_dec_ref(v_x_1804_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_instHashableBVPred_hash(lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 0)
{
lean_object* v_w_1809_; lean_object* v_lhs_1810_; uint8_t v_op_1811_; lean_object* v_rhs_1812_; uint64_t v___x_1813_; uint64_t v___x_1814_; uint64_t v___x_1815_; uint64_t v___y_1817_; 
v_w_1809_ = lean_ctor_get(v_x_1808_, 0);
v_lhs_1810_ = lean_ctor_get(v_x_1808_, 1);
v_op_1811_ = lean_ctor_get_uint8(v_x_1808_, sizeof(void*)*3);
v_rhs_1812_ = lean_ctor_get(v_x_1808_, 2);
v___x_1813_ = 0ULL;
v___x_1814_ = lean_uint64_of_nat(v_w_1809_);
v___x_1815_ = lean_uint64_mix_hash(v___x_1813_, v___x_1814_);
switch(lean_obj_tag(v_lhs_1810_))
{
case 0:
{
uint64_t v_hashCode_1833_; 
v_hashCode_1833_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*2);
v___y_1817_ = v_hashCode_1833_;
goto v___jp_1816_;
}
case 1:
{
uint64_t v_hashCode_1834_; 
v_hashCode_1834_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*2);
v___y_1817_ = v_hashCode_1834_;
goto v___jp_1816_;
}
case 3:
{
uint64_t v_hashCode_1835_; 
v_hashCode_1835_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*3);
v___y_1817_ = v_hashCode_1835_;
goto v___jp_1816_;
}
case 4:
{
uint64_t v_hashCode_1836_; 
v_hashCode_1836_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*3);
v___y_1817_ = v_hashCode_1836_;
goto v___jp_1816_;
}
case 5:
{
uint64_t v_hashCode_1837_; 
v_hashCode_1837_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*5);
v___y_1817_ = v_hashCode_1837_;
goto v___jp_1816_;
}
default: 
{
uint64_t v_hashCode_1838_; 
v_hashCode_1838_ = lean_ctor_get_uint64(v_lhs_1810_, sizeof(void*)*4);
v___y_1817_ = v_hashCode_1838_;
goto v___jp_1816_;
}
}
v___jp_1816_:
{
uint64_t v___x_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; 
v___x_1818_ = lean_uint64_mix_hash(v___x_1815_, v___y_1817_);
v___x_1819_ = l_Std_Tactic_BVDecide_instHashableBVBinPred_hash(v_op_1811_);
v___x_1820_ = lean_uint64_mix_hash(v___x_1818_, v___x_1819_);
switch(lean_obj_tag(v_rhs_1812_))
{
case 0:
{
uint64_t v_hashCode_1821_; uint64_t v___x_1822_; 
v_hashCode_1821_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*2);
v___x_1822_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1821_);
return v___x_1822_;
}
case 1:
{
uint64_t v_hashCode_1823_; uint64_t v___x_1824_; 
v_hashCode_1823_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*2);
v___x_1824_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1823_);
return v___x_1824_;
}
case 3:
{
uint64_t v_hashCode_1825_; uint64_t v___x_1826_; 
v_hashCode_1825_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*3);
v___x_1826_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1825_);
return v___x_1826_;
}
case 4:
{
uint64_t v_hashCode_1827_; uint64_t v___x_1828_; 
v_hashCode_1827_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*3);
v___x_1828_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1827_);
return v___x_1828_;
}
case 5:
{
uint64_t v_hashCode_1829_; uint64_t v___x_1830_; 
v_hashCode_1829_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*5);
v___x_1830_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1829_);
return v___x_1830_;
}
default: 
{
uint64_t v_hashCode_1831_; uint64_t v___x_1832_; 
v_hashCode_1831_ = lean_ctor_get_uint64(v_rhs_1812_, sizeof(void*)*4);
v___x_1832_ = lean_uint64_mix_hash(v___x_1820_, v_hashCode_1831_);
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_w_1839_; lean_object* v_expr_1840_; lean_object* v_idx_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v___y_1846_; 
v_w_1839_ = lean_ctor_get(v_x_1808_, 0);
v_expr_1840_ = lean_ctor_get(v_x_1808_, 1);
v_idx_1841_ = lean_ctor_get(v_x_1808_, 2);
v___x_1842_ = 1ULL;
v___x_1843_ = lean_uint64_of_nat(v_w_1839_);
v___x_1844_ = lean_uint64_mix_hash(v___x_1842_, v___x_1843_);
switch(lean_obj_tag(v_expr_1840_))
{
case 0:
{
uint64_t v_hashCode_1850_; 
v_hashCode_1850_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*2);
v___y_1846_ = v_hashCode_1850_;
goto v___jp_1845_;
}
case 1:
{
uint64_t v_hashCode_1851_; 
v_hashCode_1851_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*2);
v___y_1846_ = v_hashCode_1851_;
goto v___jp_1845_;
}
case 3:
{
uint64_t v_hashCode_1852_; 
v_hashCode_1852_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*3);
v___y_1846_ = v_hashCode_1852_;
goto v___jp_1845_;
}
case 4:
{
uint64_t v_hashCode_1853_; 
v_hashCode_1853_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*3);
v___y_1846_ = v_hashCode_1853_;
goto v___jp_1845_;
}
case 5:
{
uint64_t v_hashCode_1854_; 
v_hashCode_1854_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*5);
v___y_1846_ = v_hashCode_1854_;
goto v___jp_1845_;
}
default: 
{
uint64_t v_hashCode_1855_; 
v_hashCode_1855_ = lean_ctor_get_uint64(v_expr_1840_, sizeof(void*)*4);
v___y_1846_ = v_hashCode_1855_;
goto v___jp_1845_;
}
}
v___jp_1845_:
{
uint64_t v___x_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; 
v___x_1847_ = lean_uint64_mix_hash(v___x_1844_, v___y_1846_);
v___x_1848_ = lean_uint64_of_nat(v_idx_1841_);
v___x_1849_ = lean_uint64_mix_hash(v___x_1847_, v___x_1848_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVPred_hash___boxed(lean_object* v_x_1856_){
_start:
{
uint64_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Std_Tactic_BVDecide_instHashableBVPred_hash(v_x_1856_);
lean_dec_ref(v_x_1856_);
v_r_1858_ = lean_box_uint64(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v_w_1862_; lean_object* v_lhs_1863_; uint8_t v_op_1864_; lean_object* v_rhs_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_w_1862_ = lean_ctor_get(v_x_1861_, 0);
lean_inc_n(v_w_1862_, 2);
v_lhs_1863_ = lean_ctor_get(v_x_1861_, 1);
lean_inc_ref(v_lhs_1863_);
v_op_1864_ = lean_ctor_get_uint8(v_x_1861_, sizeof(void*)*3);
v_rhs_1865_ = lean_ctor_get(v_x_1861_, 2);
lean_inc_ref(v_rhs_1865_);
lean_dec_ref_known(v_x_1861_, 3);
v___x_1866_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1));
v___x_1867_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1862_, v_lhs_1863_);
v___x_1868_ = lean_string_append(v___x_1866_, v___x_1867_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2));
v___x_1870_ = lean_string_append(v___x_1868_, v___x_1869_);
v___x_1871_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_1864_);
v___x_1872_ = lean_string_append(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = lean_string_append(v___x_1872_, v___x_1869_);
v___x_1874_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1862_, v_rhs_1865_);
v___x_1875_ = lean_string_append(v___x_1873_, v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3));
v___x_1877_ = lean_string_append(v___x_1875_, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v_w_1878_; lean_object* v_expr_1879_; lean_object* v_idx_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_w_1878_ = lean_ctor_get(v_x_1861_, 0);
lean_inc(v_w_1878_);
v_expr_1879_ = lean_ctor_get(v_x_1861_, 1);
lean_inc_ref(v_expr_1879_);
v_idx_1880_ = lean_ctor_get(v_x_1861_, 2);
lean_inc(v_idx_1880_);
lean_dec_ref_known(v_x_1861_, 3);
v___x_1881_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_1878_, v_expr_1879_);
v___x_1882_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1));
v___x_1883_ = lean_string_append(v___x_1881_, v___x_1882_);
v___x_1884_ = l_Nat_reprFast(v_idx_1880_);
v___x_1885_ = lean_string_append(v___x_1883_, v___x_1884_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2));
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* v_assign_1890_, lean_object* v_x_1891_){
_start:
{
if (lean_obj_tag(v_x_1891_) == 0)
{
lean_object* v_w_1892_; lean_object* v_lhs_1893_; uint8_t v_op_1894_; lean_object* v_rhs_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_w_1892_ = lean_ctor_get(v_x_1891_, 0);
lean_inc_n(v_w_1892_, 2);
v_lhs_1893_ = lean_ctor_get(v_x_1891_, 1);
lean_inc_ref(v_lhs_1893_);
v_op_1894_ = lean_ctor_get_uint8(v_x_1891_, sizeof(void*)*3);
v_rhs_1895_ = lean_ctor_get(v_x_1891_, 2);
lean_inc_ref(v_rhs_1895_);
lean_dec_ref_known(v_x_1891_, 3);
v___x_1896_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1892_, v_assign_1890_, v_lhs_1893_);
v___x_1897_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1892_, v_assign_1890_, v_rhs_1895_);
v___x_1898_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_1894_, v___x_1896_, v___x_1897_);
lean_dec(v___x_1897_);
lean_dec(v___x_1896_);
return v___x_1898_;
}
else
{
lean_object* v_w_1899_; lean_object* v_expr_1900_; lean_object* v_idx_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_w_1899_ = lean_ctor_get(v_x_1891_, 0);
lean_inc(v_w_1899_);
v_expr_1900_ = lean_ctor_get(v_x_1891_, 1);
lean_inc_ref(v_expr_1900_);
v_idx_1901_ = lean_ctor_get(v_x_1891_, 2);
lean_inc(v_idx_1901_);
lean_dec_ref_known(v_x_1891_, 3);
v___x_1902_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_1899_, v_assign_1890_, v_expr_1900_);
v___x_1903_ = l_Nat_testBit(v___x_1902_, v_idx_1901_);
lean_dec(v_idx_1901_);
lean_dec(v___x_1902_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* v_assign_1904_, lean_object* v_x_1905_){
_start:
{
uint8_t v_res_1906_; lean_object* v_r_1907_; 
v_res_1906_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1904_, v_x_1905_);
lean_dec_ref(v_assign_1904_);
v_r_1907_ = lean_box(v_res_1906_);
return v_r_1907_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* v_assign_1908_, lean_object* v_x_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_1908_, v_x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* v_assign_1911_, lean_object* v_x_1912_){
_start:
{
uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_res_1913_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_1911_, v_x_1912_);
lean_dec_ref(v_assign_1911_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* v_assign_1915_, lean_object* v_expr_1916_){
_start:
{
lean_object* v___f_1917_; uint8_t v___x_1918_; 
v___f_1917_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1917_, 0, v_assign_1915_);
v___x_1918_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_1917_, v_expr_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* v_assign_1919_, lean_object* v_expr_1920_){
_start:
{
uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_res_1921_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_1919_, v_expr_1920_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
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
