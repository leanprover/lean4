// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Clause
// Imports: public import Std.Data.HashMap public import Std.Sat.CNF.Basic public import Std.Tactic.BVDecide.LRAT.Internal.Assignment import Init.Data.List.Erase import Init.Data.List.Pairwise
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
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_Literal_negate(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntailsLiteral(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value;
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam;
LEAN_EXPORT uint8_t l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringProd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_Literal_negate, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0;
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_instClausePosFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(lean_object* v_x_1_){
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
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___boxed(lean_object* v_00_u03b1_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx(v_00_u03b1_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
if (lean_obj_tag(v_t_14_) == 2)
{
lean_object* v_l_16_; lean_object* v___x_17_; 
v_l_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc_ref(v_l_16_);
lean_dec_ref_known(v_t_14_, 1);
v___x_17_ = lean_apply_1(v_k_15_, v_l_16_);
return v___x_17_;
}
else
{
lean_dec(v_t_14_);
return v_k_15_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim(v_00_u03b1_25_, v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim___redArg(lean_object* v_t_32_, lean_object* v_encounteredBoth_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_32_, v_encounteredBoth_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_encounteredBoth_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_37_, v_encounteredBoth_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim___redArg(lean_object* v_t_41_, lean_object* v_reducedToEmpty_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_41_, v_reducedToEmpty_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_reducedToEmpty_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_46_, v_reducedToEmpty_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim___redArg(lean_object* v_t_50_, lean_object* v_reducedToUnit_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_50_, v_reducedToUnit_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim(lean_object* v_00_u03b1_53_, lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_reducedToUnit_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_55_, v_reducedToUnit_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim___redArg(lean_object* v_t_59_, lean_object* v_reducedToNonunit_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_59_, v_reducedToNonunit_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim(lean_object* v_00_u03b1_62_, lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_reducedToNonunit_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_64_, v_reducedToNonunit_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntailsLiteral(lean_object* v_00_u03b1_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(lean_object* v_p_70_, lean_object* v_l_71_){
_start:
{
lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_fst_72_ = lean_ctor_get(v_l_71_, 0);
lean_inc(v_fst_72_);
v_snd_73_ = lean_ctor_get(v_l_71_, 1);
lean_inc(v_snd_73_);
lean_dec_ref(v_l_71_);
v___x_74_ = lean_apply_1(v_p_70_, v_fst_72_);
v___x_75_ = lean_unbox(v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = lean_unbox(v_snd_73_);
lean_dec(v_snd_73_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = lean_unbox(v___x_74_);
return v___x_78_;
}
}
else
{
uint8_t v___x_79_; 
v___x_79_ = lean_unbox(v_snd_73_);
lean_dec(v_snd_73_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg___boxed(lean_object* v_p_80_, lean_object* v_l_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(v_p_80_, v_l_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral(lean_object* v_00_u03b1_84_, lean_object* v_p_85_, lean_object* v_l_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(v_p_85_, v_l_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___boxed(lean_object* v_00_u03b1_88_, lean_object* v_p_89_, lean_object* v_l_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral(v_00_u03b1_88_, v_p_89_, v_l_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0(lean_object* v_a_93_, lean_object* v_l_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(v_a_93_, v_l_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0___boxed(lean_object* v_a_96_, lean_object* v_l_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0(v_a_96_, v_l_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(lean_object* v_inst_100_, lean_object* v_a_101_, lean_object* v_c_102_){
_start:
{
lean_object* v_toList_103_; lean_object* v___f_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_toList_103_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_ref(v_toList_103_);
lean_dec_ref(v_inst_100_);
v___f_104_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_104_, 0, v_a_101_);
v___x_105_ = lean_apply_1(v_toList_103_, v_c_102_);
v___x_106_ = l_List_any___redArg(v___x_105_, v___f_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___boxed(lean_object* v_inst_107_, lean_object* v_a_108_, lean_object* v_c_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_107_, v_a_108_, v_c_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_inst_114_, lean_object* v_a_115_, lean_object* v_c_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_114_, v_a_115_, v_c_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_inst_120_, lean_object* v_a_121_, lean_object* v_c_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval(v_00_u03b1_118_, v_00_u03b2_119_, v_inst_120_, v_a_121_, v_c_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails(v_00_u03b1_129_, v_00_u03b2_130_, v_inst_131_);
lean_dec_ref(v_inst_131_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg(lean_object* v_inst_133_, lean_object* v_p_134_, lean_object* v_c_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_133_, v_p_134_, v_c_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg___boxed(lean_object* v_inst_137_, lean_object* v_p_138_, lean_object* v_c_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg(v_inst_137_, v_p_138_, v_c_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_inst_144_, lean_object* v_p_145_, lean_object* v_c_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_144_, v_p_145_, v_c_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_p_151_, lean_object* v_c_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval(v_00_u03b1_148_, v_00_u03b2_149_, v_inst_150_, v_p_151_, v_c_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10));
v___x_182_ = l_Lean_mkAtom(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12);
v___x_184_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5));
v___x_185_ = lean_array_push(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16));
v___x_197_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5));
v___x_198_ = lean_array_push(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17);
v___x_200_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15));
v___x_201_ = lean_box(2);
v___x_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
return v___x_202_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18);
v___x_204_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13);
v___x_205_ = lean_array_push(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16));
v___x_207_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19);
v___x_208_ = lean_array_push(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16));
v___x_210_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20);
v___x_211_ = lean_array_push(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16));
v___x_213_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21);
v___x_214_ = lean_array_push(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22);
v___x_216_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11));
v___x_217_ = lean_box(2);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
lean_ctor_set(v___x_218_, 2, v___x_215_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23);
v___x_220_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5));
v___x_221_ = lean_array_push(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24);
v___x_223_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9));
v___x_224_ = lean_box(2);
v___x_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25);
v___x_227_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5));
v___x_228_ = lean_array_push(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26);
v___x_230_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7));
v___x_231_ = lean_box(2);
v___x_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27);
v___x_234_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5));
v___x_235_ = lean_array_push(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28);
v___x_237_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4));
v___x_238_ = lean_box(2);
v___x_239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29);
return v___x_241_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 1;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
else
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
else
{
lean_object* v_head_247_; lean_object* v_tail_248_; lean_object* v_head_249_; lean_object* v_tail_250_; uint8_t v___y_252_; lean_object* v_fst_254_; lean_object* v_snd_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; uint8_t v___x_258_; 
v_head_247_ = lean_ctor_get(v_x_242_, 0);
v_tail_248_ = lean_ctor_get(v_x_242_, 1);
v_head_249_ = lean_ctor_get(v_x_243_, 0);
v_tail_250_ = lean_ctor_get(v_x_243_, 1);
v_fst_254_ = lean_ctor_get(v_head_247_, 0);
v_snd_255_ = lean_ctor_get(v_head_247_, 1);
v_fst_256_ = lean_ctor_get(v_head_249_, 0);
v_snd_257_ = lean_ctor_get(v_head_249_, 1);
v___x_258_ = lean_nat_dec_eq(v_fst_254_, v_fst_256_);
if (v___x_258_ == 0)
{
v___y_252_ = v___x_258_;
goto v___jp_251_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = lean_unbox(v_snd_255_);
if (v___x_259_ == 0)
{
uint8_t v___x_260_; 
v___x_260_ = lean_unbox(v_snd_257_);
if (v___x_260_ == 0)
{
v___y_252_ = v___x_258_;
goto v___jp_251_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = lean_unbox(v_snd_255_);
return v___x_261_;
}
}
else
{
uint8_t v___x_262_; 
v___x_262_ = lean_unbox(v_snd_257_);
v___y_252_ = v___x_262_;
goto v___jp_251_;
}
}
v___jp_251_:
{
if (v___y_252_ == 0)
{
return v___y_252_;
}
else
{
v_x_242_ = v_tail_248_;
v_x_243_ = v_tail_250_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg___boxed(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_263_, v_x_264_);
lean_dec(v_x_264_);
lean_dec(v_x_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq(lean_object* v_numVarsSucc_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_268_, v_x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq___boxed(lean_object* v_numVarsSucc_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq(v_numVarsSucc_271_, v_x_272_, v_x_273_);
lean_dec(v_x_273_);
lean_dec(v_x_272_);
lean_dec(v_numVarsSucc_271_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0(lean_object* v_numVarsSucc_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_277_, v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___boxed(lean_object* v_numVarsSucc_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0(v_numVarsSucc_280_, v_x_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec(v_x_281_);
lean_dec(v_numVarsSucc_280_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause(lean_object* v_numVarsSucc_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq___boxed), 3, 1);
lean_closure_set(v___x_286_, 0, v_numVarsSucc_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___lam__0(lean_object* v___f_287_, lean_object* v_c_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = l_List_reverse___redArg(v_c_288_);
v___x_290_ = l_List_toString___redArg(v___f_287_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause(lean_object* v_n_298_){
_start:
{
lean_object* v___f_299_; 
v___f_299_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3));
return v___f_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___boxed(lean_object* v_n_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause(v_n_300_);
lean_dec(v_n_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg(lean_object* v_c_302_){
_start:
{
lean_inc(v_c_302_);
return v_c_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg___boxed(lean_object* v_c_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg(v_c_303_);
lean_dec(v_c_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList(lean_object* v_n_305_, lean_object* v_c_306_){
_start:
{
lean_inc(v_c_306_);
return v_c_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed(lean_object* v_n_307_, lean_object* v_c_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList(v_n_307_, v_c_308_);
lean_dec(v_c_308_);
lean_dec(v_n_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty(lean_object* v_n_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty___boxed(lean_object* v_n_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty(v_n_312_);
lean_dec(v_n_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___redArg(lean_object* v_l_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_l_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit(lean_object* v_n_317_, lean_object* v_l_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v_l_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed(lean_object* v_n_321_, lean_object* v_l_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit(v_n_321_, v_l_322_);
lean_dec(v_n_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg(lean_object* v_c_324_){
_start:
{
if (lean_obj_tag(v_c_324_) == 1)
{
lean_object* v_tail_325_; 
v_tail_325_ = lean_ctor_get(v_c_324_, 1);
if (lean_obj_tag(v_tail_325_) == 0)
{
lean_object* v_head_326_; lean_object* v___x_327_; 
v_head_326_ = lean_ctor_get(v_c_324_, 0);
lean_inc(v_head_326_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_head_326_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg___boxed(lean_object* v_c_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg(v_c_330_);
lean_dec(v_c_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit(lean_object* v_n_332_, lean_object* v_c_333_){
_start:
{
if (lean_obj_tag(v_c_333_) == 1)
{
lean_object* v_tail_334_; 
v_tail_334_ = lean_ctor_get(v_c_333_, 1);
if (lean_obj_tag(v_tail_334_) == 0)
{
lean_object* v_head_335_; lean_object* v___x_336_; 
v_head_335_ = lean_ctor_get(v_c_333_, 0);
lean_inc(v_head_335_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_head_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed(lean_object* v_n_339_, lean_object* v_c_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit(v_n_339_, v_c_340_);
lean_dec(v_c_340_);
lean_dec(v_n_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___redArg(lean_object* v_x_342_, lean_object* v_h__1_343_, lean_object* v_h__2_344_){
_start:
{
if (lean_obj_tag(v_x_342_) == 1)
{
lean_object* v_tail_345_; 
v_tail_345_ = lean_ctor_get(v_x_342_, 1);
if (lean_obj_tag(v_tail_345_) == 0)
{
lean_object* v_head_346_; lean_object* v___x_347_; 
lean_dec(v_h__2_344_);
v_head_346_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_head_346_);
lean_dec_ref_known(v_x_342_, 2);
v___x_347_ = lean_apply_1(v_h__1_343_, v_head_346_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_dec(v_h__1_343_);
v___x_348_ = lean_apply_2(v_h__2_344_, v_x_342_, lean_box(0));
return v___x_348_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v_h__1_343_);
v___x_349_ = lean_apply_2(v_h__2_344_, v_x_342_, lean_box(0));
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter(lean_object* v_n_350_, lean_object* v_motive_351_, lean_object* v_x_352_, lean_object* v_h__1_353_, lean_object* v_h__2_354_){
_start:
{
if (lean_obj_tag(v_x_352_) == 1)
{
lean_object* v_tail_355_; 
v_tail_355_ = lean_ctor_get(v_x_352_, 1);
if (lean_obj_tag(v_tail_355_) == 0)
{
lean_object* v_head_356_; lean_object* v___x_357_; 
lean_dec(v_h__2_354_);
v_head_356_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_head_356_);
lean_dec_ref_known(v_x_352_, 2);
v___x_357_ = lean_apply_1(v_h__1_353_, v_head_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
lean_dec(v_h__1_353_);
v___x_358_ = lean_apply_2(v_h__2_354_, v_x_352_, lean_box(0));
return v___x_358_;
}
}
else
{
lean_object* v___x_359_; 
lean_dec(v_h__1_353_);
v___x_359_ = lean_apply_2(v_h__2_354_, v_x_352_, lean_box(0));
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___boxed(lean_object* v_n_360_, lean_object* v_motive_361_, lean_object* v_x_362_, lean_object* v_h__1_363_, lean_object* v_h__2_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter(v_n_360_, v_motive_361_, v_x_362_, v_h__1_363_, v_h__2_364_);
lean_dec(v_n_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg(lean_object* v_c_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0));
v___x_369_ = lean_box(0);
v___x_370_ = l_List_mapTR_loop___redArg(v___x_368_, v_c_367_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate(lean_object* v_n_371_, lean_object* v_c_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0));
v___x_374_ = lean_box(0);
v___x_375_ = l_List_mapTR_loop___redArg(v___x_373_, v_c_372_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed(lean_object* v_n_376_, lean_object* v_c_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate(v_n_376_, v_c_377_);
lean_dec(v_n_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg(lean_object* v_m_379_, lean_object* v_query_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_zero_384_; uint8_t v_isZero_385_; 
v_zero_384_ = lean_unsigned_to_nat(0u);
v_isZero_385_ = lean_nat_dec_eq(v_x_382_, v_zero_384_);
if (v_isZero_385_ == 1)
{
lean_dec(v_x_383_);
lean_dec(v_x_382_);
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(2);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_val_387_ = lean_ctor_get(v_x_381_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v_x_381_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v_x_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_val_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_keyArray_395_; lean_object* v_valueArray_396_; lean_object* v___x_397_; uint8_t v_isSome_398_; 
v_keyArray_395_ = lean_ctor_get(v_m_379_, 1);
v_valueArray_396_ = lean_ctor_get(v_m_379_, 2);
v___x_397_ = lean_array_fget_borrowed(v_keyArray_395_, v_x_383_);
v_isSome_398_ = lean_noption_is_some(v___x_397_);
if (v_isSome_398_ == 0)
{
lean_dec(v_x_382_);
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_x_383_);
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_x_383_);
v_val_400_ = lean_ctor_get(v_x_381_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v_x_381_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v_x_381_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_val_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_one_408_; lean_object* v_n_409_; lean_object* v___y_411_; 
v_one_408_ = lean_unsigned_to_nat(1u);
v_n_409_ = lean_nat_sub(v_x_382_, v_one_408_);
lean_dec(v_x_382_);
if (v_isSome_398_ == 0)
{
goto v___jp_417_;
}
else
{
lean_object* v___x_419_; uint8_t v_isSome_420_; 
v___x_419_ = lean_array_fget_borrowed(v_valueArray_396_, v_x_383_);
v_isSome_420_ = lean_noption_is_some(v___x_419_);
if (v_isSome_420_ == 0)
{
goto v___jp_417_;
}
else
{
lean_object* v_val_421_; uint8_t v___x_422_; 
lean_inc(v___x_397_);
v_val_421_ = lean_noption_get(v___x_397_);
v___x_422_ = lean_nat_dec_eq(v_val_421_, v_query_380_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
lean_dec(v_val_421_);
v___x_423_ = lean_array_get_size(v_keyArray_395_);
v___x_424_ = lean_nat_add(v_x_383_, v_one_408_);
lean_dec(v_x_383_);
v___x_425_ = lean_nat_dec_lt(v___x_424_, v___x_423_);
if (v___x_425_ == 0)
{
lean_dec(v___x_424_);
v_x_382_ = v_n_409_;
v_x_383_ = v_zero_384_;
goto _start;
}
else
{
v_x_382_ = v_n_409_;
v_x_383_ = v___x_424_;
goto _start;
}
}
else
{
lean_object* v_val_428_; lean_object* v___x_429_; 
lean_dec(v_n_409_);
lean_dec(v_x_381_);
lean_inc(v___x_419_);
v_val_428_ = lean_noption_get(v___x_419_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v_x_383_);
lean_ctor_set(v___x_429_, 1, v_val_421_);
lean_ctor_set(v___x_429_, 2, v_val_428_);
return v___x_429_;
}
}
}
v___jp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_array_get_size(v_keyArray_395_);
v___x_413_ = lean_nat_add(v_x_383_, v_one_408_);
lean_dec(v_x_383_);
v___x_414_ = lean_nat_dec_lt(v___x_413_, v___x_412_);
if (v___x_414_ == 0)
{
lean_dec(v___x_413_);
v_x_381_ = v___y_411_;
v_x_382_ = v_n_409_;
v_x_383_ = v_zero_384_;
goto _start;
}
else
{
v_x_381_ = v___y_411_;
v_x_382_ = v_n_409_;
v_x_383_ = v___x_413_;
goto _start;
}
}
v___jp_417_:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v___x_418_; 
lean_inc(v_x_383_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_x_383_);
v___y_411_ = v___x_418_;
goto v___jp_410_;
}
else
{
v___y_411_ = v_x_381_;
goto v___jp_410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg___boxed(lean_object* v_m_430_, lean_object* v_query_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg(v_m_430_, v_query_431_, v_x_432_, v_x_433_, v_x_434_);
lean_dec(v_query_431_);
lean_dec_ref(v_m_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(lean_object* v_n_436_, lean_object* v_m_437_, lean_object* v_query_438_){
_start:
{
lean_object* v_keyArray_439_; lean_object* v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v_fold_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_keyArray_439_ = lean_ctor_get(v_m_437_, 1);
v___x_440_ = lean_array_get_size(v_keyArray_439_);
v___x_441_ = lean_uint64_of_nat(v_query_438_);
v___x_442_ = 32ULL;
v___x_443_ = lean_uint64_shift_right(v___x_441_, v___x_442_);
v_fold_444_ = lean_uint64_xor(v___x_441_, v___x_443_);
v___x_445_ = 16ULL;
v___x_446_ = lean_uint64_shift_right(v_fold_444_, v___x_445_);
v___x_447_ = lean_uint64_xor(v_fold_444_, v___x_446_);
v___x_448_ = lean_uint64_to_usize(v___x_447_);
v___x_449_ = lean_usize_of_nat(v___x_440_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_sub(v___x_449_, v___x_450_);
v___x_452_ = lean_usize_land(v___x_448_, v___x_451_);
v___x_453_ = lean_usize_to_nat(v___x_452_);
v___x_454_ = lean_box(0);
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg(v_m_437_, v_query_438_, v___x_454_, v___x_440_, v___x_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg___boxed(lean_object* v_n_456_, lean_object* v_m_457_, lean_object* v_query_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_456_, v_m_457_, v_query_458_);
lean_dec(v_query_458_);
lean_dec_ref(v_m_457_);
lean_dec(v_n_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg(lean_object* v_n_460_, lean_object* v_b_461_, lean_object* v_acc_462_, lean_object* v_i_463_){
_start:
{
lean_object* v___y_465_; lean_object* v_keyArray_473_; lean_object* v_valueArray_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_keyArray_473_ = lean_ctor_get(v_b_461_, 1);
v_valueArray_474_ = lean_ctor_get(v_b_461_, 2);
v___x_475_ = lean_array_get_size(v_keyArray_473_);
v___x_476_ = lean_nat_dec_lt(v_i_463_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v_i_463_);
return v_acc_462_;
}
else
{
lean_object* v___x_477_; uint8_t v_isSome_478_; 
v___x_477_ = lean_array_fget_borrowed(v_keyArray_473_, v_i_463_);
v_isSome_478_ = lean_noption_is_some(v___x_477_);
if (v_isSome_478_ == 0)
{
goto v___jp_469_;
}
else
{
lean_object* v___x_479_; uint8_t v_isSome_480_; 
v___x_479_ = lean_array_fget_borrowed(v_valueArray_474_, v_i_463_);
v_isSome_480_ = lean_noption_is_some(v___x_479_);
if (v_isSome_480_ == 0)
{
goto v___jp_469_;
}
else
{
lean_object* v_val_481_; lean_object* v_val_482_; lean_object* v_i_484_; lean_object* v___x_489_; 
lean_inc(v___x_477_);
v_val_481_ = lean_noption_get(v___x_477_);
lean_inc(v___x_479_);
v_val_482_ = lean_noption_get(v___x_479_);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_460_, v_acc_462_, v_val_481_);
switch(lean_obj_tag(v___x_489_))
{
case 0:
{
lean_object* v_index_490_; lean_object* v_size_491_; lean_object* v___x_492_; 
v_index_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_index_490_);
lean_dec_ref_known(v___x_489_, 3);
v_size_491_ = lean_ctor_get(v_acc_462_, 0);
lean_inc(v_size_491_);
v___x_492_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_462_, v_size_491_, v_index_490_, v_val_481_, v_val_482_);
lean_dec(v_index_490_);
v___y_465_ = v___x_492_;
goto v___jp_464_;
}
case 1:
{
lean_object* v_index_493_; 
v_index_493_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_index_493_);
lean_dec_ref_known(v___x_489_, 1);
v_i_484_ = v_index_493_;
goto v___jp_483_;
}
default: 
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_462_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_index_496_; 
v_index_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_index_496_);
lean_dec_ref_known(v___x_495_, 1);
v_i_484_ = v_index_496_;
goto v___jp_483_;
}
else
{
lean_dec(v_val_482_);
lean_dec(v_val_481_);
v___y_465_ = v_acc_462_;
goto v___jp_464_;
}
}
}
v___jp_483_:
{
lean_object* v_size_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_size_485_ = lean_ctor_get(v_acc_462_, 0);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_size_485_, v___x_486_);
v___x_488_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_462_, v___x_487_, v_i_484_, v_val_481_, v_val_482_);
lean_dec(v_i_484_);
v___y_465_ = v___x_488_;
goto v___jp_464_;
}
}
}
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_463_, v___x_466_);
lean_dec(v_i_463_);
v_acc_462_ = v___y_465_;
v_i_463_ = v___x_467_;
goto _start;
}
v___jp_469_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v_i_463_, v___x_470_);
lean_dec(v_i_463_);
v_i_463_ = v___x_471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_n_497_, lean_object* v_b_498_, lean_object* v_acc_499_, lean_object* v_i_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg(v_n_497_, v_b_498_, v_acc_499_, v_i_500_);
lean_dec_ref(v_b_498_);
lean_dec(v_n_497_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg(lean_object* v_n_502_, lean_object* v_init_503_, lean_object* v_b_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg(v_n_502_, v_b_504_, v_init_503_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg___boxed(lean_object* v_n_507_, lean_object* v_init_508_, lean_object* v_b_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg(v_n_507_, v_init_508_, v_b_509_);
lean_dec_ref(v_b_509_);
lean_dec(v_n_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(lean_object* v_n_511_, lean_object* v_m_512_){
_start:
{
lean_object* v_keyArray_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_cellCount_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_target_520_; lean_object* v___x_521_; 
v_keyArray_513_ = lean_ctor_get(v_m_512_, 1);
v___x_514_ = lean_array_get_size(v_keyArray_513_);
v___x_515_ = lean_unsigned_to_nat(2u);
v_cellCount_516_ = lean_nat_mul(v___x_514_, v___x_515_);
v___x_517_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_516_);
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_516_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_516_);
v_target_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_520_, 0, v___x_517_);
lean_ctor_set(v_target_520_, 1, v___x_518_);
lean_ctor_set(v_target_520_, 2, v___x_519_);
v___x_521_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg(v_n_511_, v_target_520_, v_m_512_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg___boxed(lean_object* v_n_522_, lean_object* v_m_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_522_, v_m_523_);
lean_dec_ref(v_m_523_);
lean_dec(v_n_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(lean_object* v_n_525_, lean_object* v_acc_526_, lean_object* v_l_527_){
_start:
{
if (lean_obj_tag(v_acc_526_) == 0)
{
lean_dec_ref(v_l_527_);
return v_acc_526_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_619_; 
v_val_528_ = lean_ctor_get(v_acc_526_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_acc_526_);
if (v_isSharedCheck_619_ == 0)
{
v___x_530_ = v_acc_526_;
v_isShared_531_ = v_isSharedCheck_619_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v_acc_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_619_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___y_535_; lean_object* v_i_536_; lean_object* v___y_545_; lean_object* v___y_557_; lean_object* v_i_558_; lean_object* v___x_576_; 
v_fst_532_ = lean_ctor_get(v_l_527_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v_l_527_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v_l_527_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_525_, v_val_528_, v_fst_532_);
switch(lean_obj_tag(v___x_576_))
{
case 0:
{
uint8_t v___x_577_; 
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
v___x_577_ = lean_unbox(v_snd_533_);
lean_dec(v_snd_533_);
if (v___x_577_ == 0)
{
lean_object* v_value_578_; uint8_t v___x_579_; 
v_value_578_ = lean_ctor_get(v___x_576_, 2);
lean_inc(v_value_578_);
lean_dec_ref_known(v___x_576_, 3);
v___x_579_ = lean_unbox(v_value_578_);
lean_dec(v_value_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_val_528_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v_val_528_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
}
else
{
lean_object* v_value_582_; uint8_t v___x_583_; 
v_value_582_ = lean_ctor_get(v___x_576_, 2);
lean_inc(v_value_582_);
lean_dec_ref_known(v___x_576_, 3);
v___x_583_ = lean_unbox(v_value_582_);
lean_dec(v_value_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec(v_val_528_);
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_val_528_);
return v___x_585_;
}
}
}
case 1:
{
lean_object* v_index_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_530_);
v_index_586_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_605_ == 0)
{
v___x_588_ = v___x_576_;
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_index_586_);
lean_dec(v___x_576_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_size_590_; lean_object* v_keyArray_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_size_590_ = lean_ctor_get(v_val_528_, 0);
v_keyArray_591_ = lean_ctor_get(v_val_528_, 1);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_size_590_, v___x_592_);
v___x_594_ = lean_array_get_size(v_keyArray_591_);
v___x_595_ = lean_nat_dec_lt(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec(v___x_593_);
lean_del_object(v___x_588_);
lean_dec(v_index_586_);
goto v___jp_564_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_596_ = lean_unsigned_to_nat(4u);
v___x_597_ = lean_nat_mul(v___x_593_, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(3u);
v___x_599_ = lean_nat_mul(v___x_594_, v___x_598_);
v___x_600_ = lean_nat_dec_le(v___x_597_, v___x_599_);
lean_dec(v___x_599_);
lean_dec(v___x_597_);
if (v___x_600_ == 0)
{
lean_dec(v___x_593_);
lean_del_object(v___x_588_);
lean_dec(v_index_586_);
goto v___jp_564_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = l_Std_DHashMap_Raw_setEntry___redArg(v_val_528_, v___x_593_, v_index_586_, v_fst_532_, v_snd_533_);
lean_dec(v_index_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_601_);
v___x_603_ = v___x_588_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
default: 
{
lean_object* v_size_606_; lean_object* v_keyArray_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_size_606_ = lean_ctor_get(v_val_528_, 0);
v_keyArray_607_ = lean_ctor_get(v_val_528_, 1);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_size_606_, v___x_608_);
v___x_610_ = lean_array_get_size(v_keyArray_607_);
v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v___x_609_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_525_, v_val_528_);
lean_dec(v_val_528_);
v___y_545_ = v___x_612_;
goto v___jp_544_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_mul(v___x_609_, v___x_613_);
lean_dec(v___x_609_);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_nat_mul(v___x_610_, v___x_615_);
v___x_617_ = lean_nat_dec_le(v___x_614_, v___x_616_);
lean_dec(v___x_616_);
lean_dec(v___x_614_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_525_, v_val_528_);
lean_dec(v_val_528_);
v___y_545_ = v___x_618_;
goto v___jp_544_;
}
else
{
v___y_545_ = v_val_528_;
goto v___jp_544_;
}
}
}
}
v___jp_534_:
{
lean_object* v_size_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v_size_537_ = lean_ctor_get(v___y_535_, 0);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_size_537_, v___x_538_);
v___x_540_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_535_, v___x_539_, v_i_536_, v_fst_532_, v_snd_533_);
lean_dec(v_i_536_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_540_);
v___x_542_ = v___x_530_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
v___jp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_525_, v___y_545_, v_fst_532_);
switch(lean_obj_tag(v___x_546_))
{
case 0:
{
lean_object* v_index_547_; lean_object* v_size_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_del_object(v___x_530_);
v_index_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_index_547_);
lean_dec_ref_known(v___x_546_, 3);
v_size_548_ = lean_ctor_get(v___y_545_, 0);
lean_inc(v_size_548_);
v___x_549_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_545_, v_size_548_, v_index_547_, v_fst_532_, v_snd_533_);
lean_dec(v_index_547_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
case 1:
{
lean_object* v_index_551_; 
v_index_551_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_index_551_);
lean_dec_ref_known(v___x_546_, 1);
v___y_535_ = v___y_545_;
v_i_536_ = v_index_551_;
goto v___jp_534_;
}
default: 
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_545_, v___x_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_index_554_; 
v_index_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_index_554_);
lean_dec_ref_known(v___x_553_, 1);
v___y_535_ = v___y_545_;
v_i_536_ = v_index_554_;
goto v___jp_534_;
}
else
{
lean_object* v___x_555_; 
lean_dec(v_snd_533_);
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___y_545_);
return v___x_555_;
}
}
}
}
v___jp_556_:
{
lean_object* v_size_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_size_559_ = lean_ctor_get(v___y_557_, 0);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_size_559_, v___x_560_);
v___x_562_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_557_, v___x_561_, v_i_558_, v_fst_532_, v_snd_533_);
lean_dec(v_i_558_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_525_, v_val_528_);
lean_dec(v_val_528_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_525_, v___x_565_, v_fst_532_);
switch(lean_obj_tag(v___x_566_))
{
case 0:
{
lean_object* v_index_567_; lean_object* v_size_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_index_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_index_567_);
lean_dec_ref_known(v___x_566_, 3);
v_size_568_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_size_568_);
v___x_569_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_565_, v_size_568_, v_index_567_, v_fst_532_, v_snd_533_);
lean_dec(v_index_567_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
case 1:
{
lean_object* v_index_571_; 
v_index_571_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_index_571_);
lean_dec_ref_known(v___x_566_, 1);
v___y_557_ = v___x_565_;
v_i_558_ = v_index_571_;
goto v___jp_556_;
}
default: 
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_565_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_index_574_; 
v_index_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_index_574_);
lean_dec_ref_known(v___x_573_, 1);
v___y_557_ = v___x_565_;
v_i_558_ = v_index_574_;
goto v___jp_556_;
}
else
{
lean_object* v___x_575_; 
lean_dec(v_snd_533_);
lean_dec(v_fst_532_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_565_);
return v___x_575_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(lean_object* v_n_620_, lean_object* v_acc_621_, lean_object* v_l_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_620_, v_acc_621_, v_l_622_);
lean_dec(v_n_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(lean_object* v_n_624_, lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_query_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_n_624_, v_m_626_, v_query_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(lean_object* v_n_629_, lean_object* v_00_u03b2_630_, lean_object* v_m_631_, lean_object* v_query_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(v_n_629_, v_00_u03b2_630_, v_m_631_, v_query_632_);
lean_dec(v_query_632_);
lean_dec_ref(v_m_631_);
lean_dec(v_n_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(lean_object* v_n_634_, lean_object* v_00_u03b2_635_, lean_object* v_m_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_634_, v_m_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(lean_object* v_n_638_, lean_object* v_00_u03b2_639_, lean_object* v_m_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(v_n_638_, v_00_u03b2_639_, v_m_640_);
lean_dec_ref(v_m_640_);
lean_dec(v_n_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0(lean_object* v_n_642_, lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_query_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___redArg(v_m_644_, v_query_645_, v_x_646_, v_x_647_, v_x_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0___boxed(lean_object* v_n_651_, lean_object* v_00_u03b2_652_, lean_object* v_m_653_, lean_object* v_query_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0_spec__0(v_n_651_, v_00_u03b2_652_, v_m_653_, v_query_654_, v_x_655_, v_x_656_, v_x_657_, v_x_658_);
lean_dec(v_query_654_);
lean_dec_ref(v_m_653_);
lean_dec(v_n_651_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2(lean_object* v_00_u03b2_660_, lean_object* v_n_661_, lean_object* v_init_662_, lean_object* v_b_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___redArg(v_n_661_, v_init_662_, v_b_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2___boxed(lean_object* v_00_u03b2_665_, lean_object* v_n_666_, lean_object* v_init_667_, lean_object* v_b_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2(v_00_u03b2_665_, v_n_666_, v_init_667_, v_b_668_);
lean_dec_ref(v_b_668_);
lean_dec(v_n_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_670_, lean_object* v_n_671_, lean_object* v_b_672_, lean_object* v_acc_673_, lean_object* v_i_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___redArg(v_n_671_, v_b_672_, v_acc_673_, v_i_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_676_, lean_object* v_n_677_, lean_object* v_b_678_, lean_object* v_acc_679_, lean_object* v_i_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__2_spec__3(v_00_u03b2_676_, v_n_677_, v_b_678_, v_acc_679_, v_i_680_);
lean_dec_ref(v_b_678_);
lean_dec(v_n_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object* v_acc_682_, lean_object* v_h__1_683_, lean_object* v_h__2_684_){
_start:
{
if (lean_obj_tag(v_acc_682_) == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_h__2_684_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_apply_1(v_h__1_683_, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; lean_object* v___x_688_; 
lean_dec(v_h__1_683_);
v_val_687_ = lean_ctor_get(v_acc_682_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_acc_682_, 1);
v___x_688_ = lean_apply_1(v_h__2_684_, v_val_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object* v_n_689_, lean_object* v_motive_690_, lean_object* v_acc_691_, lean_object* v_h__1_692_, lean_object* v_h__2_693_){
_start:
{
if (lean_obj_tag(v_acc_691_) == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec(v_h__2_693_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_apply_1(v_h__1_692_, v___x_694_);
return v___x_695_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_697_; 
lean_dec(v_h__1_692_);
v_val_696_ = lean_ctor_get(v_acc_691_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_acc_691_, 1);
v___x_697_ = lean_apply_1(v_h__2_693_, v_val_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object* v_n_698_, lean_object* v_motive_699_, lean_object* v_acc_700_, lean_object* v_h__1_701_, lean_object* v_h__2_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_698_, v_motive_699_, v_acc_700_, v_h__1_701_, v_h__2_702_);
lean_dec(v_n_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(lean_object* v_n_704_, lean_object* v_as_705_, size_t v_i_706_, size_t v_stop_707_, lean_object* v_b_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_eq(v_i_706_, v_stop_707_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; size_t v___x_712_; size_t v___x_713_; 
v___x_710_ = lean_array_uget_borrowed(v_as_705_, v_i_706_);
lean_inc(v___x_710_);
v___x_711_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_704_, v_b_708_, v___x_710_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_706_, v___x_712_);
v_i_706_ = v___x_713_;
v_b_708_ = v___x_711_;
goto _start;
}
else
{
return v_b_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(lean_object* v_n_715_, lean_object* v_as_716_, lean_object* v_i_717_, lean_object* v_stop_718_, lean_object* v_b_719_){
_start:
{
size_t v_i_boxed_720_; size_t v_stop_boxed_721_; lean_object* v_res_722_; 
v_i_boxed_720_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_stop_boxed_721_ = lean_unbox_usize(v_stop_718_);
lean_dec(v_stop_718_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_n_715_, v_as_716_, v_i_boxed_720_, v_stop_boxed_721_, v_b_719_);
lean_dec_ref(v_as_716_);
lean_dec(v_n_715_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(lean_object* v_b_723_, lean_object* v_acc_724_, lean_object* v_i_725_){
_start:
{
lean_object* v_keyArray_730_; lean_object* v_valueArray_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_keyArray_730_ = lean_ctor_get(v_b_723_, 1);
v_valueArray_731_ = lean_ctor_get(v_b_723_, 2);
v___x_732_ = lean_array_get_size(v_keyArray_730_);
v___x_733_ = lean_nat_dec_lt(v_i_725_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v_i_725_);
lean_inc(v_acc_724_);
return v_acc_724_;
}
else
{
lean_object* v___x_734_; uint8_t v_isSome_735_; 
v___x_734_ = lean_array_fget_borrowed(v_keyArray_730_, v_i_725_);
v_isSome_735_ = lean_noption_is_some(v___x_734_);
if (v_isSome_735_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_736_; uint8_t v_isSome_737_; 
v___x_736_ = lean_array_fget_borrowed(v_valueArray_731_, v_i_725_);
v_isSome_737_ = lean_noption_is_some(v___x_736_);
if (v_isSome_737_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v_val_738_; lean_object* v_val_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_inc(v___x_734_);
v_val_738_ = lean_noption_get(v___x_734_);
lean_inc(v___x_736_);
v_val_739_ = lean_noption_get(v___x_736_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_i_725_, v___x_740_);
lean_dec(v_i_725_);
v___x_742_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_b_723_, v_acc_724_, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_val_738_);
lean_ctor_set(v___x_743_, 1, v_val_739_);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_i_725_, v___x_727_);
lean_dec(v_i_725_);
v_i_725_ = v___x_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(lean_object* v_b_745_, lean_object* v_acc_746_, lean_object* v_i_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_b_745_, v_acc_746_, v_i_747_);
lean_dec(v_acc_746_);
lean_dec_ref(v_b_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object* v_n_749_, lean_object* v_ls_750_){
_start:
{
lean_object* v_val_752_; lean_object* v___y_758_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_cellCount_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_761_ = lean_array_get_size(v_ls_750_);
v___x_762_ = lean_unsigned_to_nat(4u);
v___x_763_ = lean_nat_mul(v___x_761_, v___x_762_);
v___x_764_ = lean_unsigned_to_nat(2u);
v___x_765_ = lean_nat_add(v___x_763_, v___x_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_unsigned_to_nat(3u);
v___x_767_ = lean_nat_div(v___x_765_, v___x_766_);
lean_dec(v___x_765_);
v_cellCount_768_ = l_Nat_nextPowerOfTwo(v___x_767_);
lean_dec(v___x_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_768_);
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_768_);
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_768_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___x_769_);
lean_ctor_set(v___x_772_, 1, v___x_770_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = lean_nat_dec_lt(v___x_769_, v___x_761_);
if (v___x_773_ == 0)
{
v_val_752_ = v___x_772_;
goto v___jp_751_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
lean_inc_ref(v___x_772_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
v___x_775_ = lean_nat_dec_le(v___x_761_, v___x_761_);
if (v___x_775_ == 0)
{
if (v___x_773_ == 0)
{
lean_dec_ref_known(v___x_774_, 1);
v_val_752_ = v___x_772_;
goto v___jp_751_;
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_dec_ref_known(v___x_772_, 3);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_of_nat(v___x_761_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_n_749_, v_ls_750_, v___x_776_, v___x_777_, v___x_774_);
v___y_758_ = v___x_778_;
goto v___jp_757_;
}
}
else
{
size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_772_, 3);
v___x_779_ = ((size_t)0ULL);
v___x_780_ = lean_usize_of_nat(v___x_761_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_n_749_, v_ls_750_, v___x_779_, v___x_780_, v___x_774_);
v___y_758_ = v___x_781_;
goto v___jp_757_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_box(0);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_val_752_, v___x_753_, v___x_754_);
lean_dec_ref(v_val_752_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
v___jp_757_:
{
if (lean_obj_tag(v___y_758_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v___y_758_, 1);
v_val_752_ = v_val_760_;
goto v___jp_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed(lean_object* v_n_782_, lean_object* v_ls_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_782_, v_ls_783_);
lean_dec_ref(v_ls_783_);
lean_dec(v_n_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter___redArg(lean_object* v_val_x3f_785_, lean_object* v_h__1_786_, lean_object* v_h__2_787_){
_start:
{
if (lean_obj_tag(v_val_x3f_785_) == 1)
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec(v_h__2_787_);
v_val_788_ = lean_ctor_get(v_val_x3f_785_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_val_x3f_785_, 1);
v___x_789_ = lean_apply_1(v_h__1_786_, v_val_788_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; 
lean_dec(v_h__1_786_);
v___x_790_ = lean_apply_2(v_h__2_787_, v_val_x3f_785_, lean_box(0));
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter(lean_object* v_motive_791_, lean_object* v_val_x3f_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_){
_start:
{
if (lean_obj_tag(v_val_x3f_792_) == 1)
{
lean_object* v_val_795_; lean_object* v___x_796_; 
lean_dec(v_h__2_794_);
v_val_795_ = lean_ctor_get(v_val_x3f_792_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_val_x3f_792_, 1);
v___x_796_ = lean_apply_1(v_h__1_793_, v_val_795_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; 
lean_dec(v_h__1_793_);
v___x_797_ = lean_apply_2(v_h__2_794_, v_val_x3f_792_, lean_box(0));
return v___x_797_;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0(void){
_start:
{
lean_object* v___x_798_; lean_object* v___f_799_; 
v___x_798_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_799_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_799_, 0, v___x_798_);
return v___f_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete(lean_object* v_n_802_, lean_object* v_c_803_, lean_object* v_l_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_805_, 0, v_n_802_);
v___f_806_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_806_, 0, v___x_805_);
v___f_807_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_808_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_808_, 0, v___f_806_);
lean_closure_set(v___f_808_, 1, v___f_807_);
v___x_809_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1));
lean_inc(v_c_803_);
v___x_810_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_box(0), v___f_808_, v_c_803_, v_l_804_, v_c_803_, v___x_809_);
lean_dec(v_c_803_);
return v___x_810_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(lean_object* v_n_811_, lean_object* v_c_812_, lean_object* v_l_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___f_817_; uint8_t v___x_818_; 
v___x_814_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_814_, 0, v_n_811_);
v___f_815_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_815_, 0, v___x_814_);
v___f_816_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_817_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_817_, 0, v___f_815_);
lean_closure_set(v___f_817_, 1, v___f_816_);
v___x_818_ = l_List_elem___redArg(v___f_817_, v_l_813_, v_c_812_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed(lean_object* v_n_819_, lean_object* v_c_820_, lean_object* v_l_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(v_n_819_, v_c_820_, v_l_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(lean_object* v_assignments_824_, lean_object* v_acc_825_, lean_object* v_l_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = 0;
switch(lean_obj_tag(v_acc_825_))
{
case 1:
{
lean_object* v_fst_828_; lean_object* v_snd_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_fst_828_ = lean_ctor_get(v_l_826_, 0);
v_snd_829_ = lean_ctor_get(v_l_826_, 1);
v___x_830_ = lean_box(v___x_827_);
v___x_831_ = lean_array_get(v___x_830_, v_assignments_824_, v_fst_828_);
lean_dec(v___x_830_);
v___x_832_ = lean_unbox(v___x_831_);
lean_dec(v___x_831_);
switch(v___x_832_)
{
case 0:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_snd_829_);
if (v___x_833_ == 0)
{
lean_dec_ref(v_l_826_);
return v_acc_825_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_834_, 0, v_l_826_);
return v___x_834_;
}
}
case 1:
{
uint8_t v___x_835_; 
v___x_835_ = lean_unbox(v_snd_829_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_836_, 0, v_l_826_);
return v___x_836_;
}
else
{
lean_dec_ref(v_l_826_);
return v_acc_825_;
}
}
case 2:
{
lean_object* v___x_837_; 
lean_dec_ref(v_l_826_);
v___x_837_ = lean_box(0);
return v___x_837_;
}
default: 
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_838_, 0, v_l_826_);
return v___x_838_;
}
}
}
case 2:
{
lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_fst_839_ = lean_ctor_get(v_l_826_, 0);
lean_inc(v_fst_839_);
v_snd_840_ = lean_ctor_get(v_l_826_, 1);
lean_inc(v_snd_840_);
lean_dec_ref(v_l_826_);
v___x_841_ = lean_box(v___x_827_);
v___x_842_ = lean_array_get(v___x_841_, v_assignments_824_, v_fst_839_);
lean_dec(v_fst_839_);
lean_dec(v___x_841_);
v___x_843_ = lean_unbox(v___x_842_);
lean_dec(v___x_842_);
switch(v___x_843_)
{
case 0:
{
uint8_t v___x_844_; 
v___x_844_ = lean_unbox(v_snd_840_);
lean_dec(v_snd_840_);
if (v___x_844_ == 0)
{
lean_inc_ref(v_acc_825_);
return v_acc_825_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_box(3);
return v___x_845_;
}
}
case 1:
{
uint8_t v___x_846_; 
v___x_846_ = lean_unbox(v_snd_840_);
lean_dec(v_snd_840_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(3);
return v___x_847_;
}
else
{
lean_inc_ref(v_acc_825_);
return v_acc_825_;
}
}
case 2:
{
lean_object* v___x_848_; 
lean_dec(v_snd_840_);
v___x_848_ = lean_box(0);
return v___x_848_;
}
default: 
{
lean_object* v___x_849_; 
lean_dec(v_snd_840_);
v___x_849_ = lean_box(3);
return v___x_849_;
}
}
}
default: 
{
lean_dec_ref(v_l_826_);
lean_inc(v_acc_825_);
return v_acc_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg___boxed(lean_object* v_assignments_850_, lean_object* v_acc_851_, lean_object* v_l_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_850_, v_acc_851_, v_l_852_);
lean_dec(v_acc_851_);
lean_dec_ref(v_assignments_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(lean_object* v_n_854_, lean_object* v_assignments_855_, lean_object* v_acc_856_, lean_object* v_l_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_855_, v_acc_856_, v_l_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___boxed(lean_object* v_n_859_, lean_object* v_assignments_860_, lean_object* v_acc_861_, lean_object* v_l_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(v_n_859_, v_assignments_860_, v_acc_861_, v_l_862_);
lean_dec(v_acc_861_);
lean_dec_ref(v_assignments_860_);
lean_dec(v_n_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(lean_object* v_assignments_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
return v_x_865_;
}
else
{
lean_object* v_head_867_; lean_object* v_tail_868_; lean_object* v___x_869_; 
v_head_867_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_head_867_);
v_tail_868_ = lean_ctor_get(v_x_866_, 1);
lean_inc(v_tail_868_);
lean_dec_ref_known(v_x_866_, 2);
v___x_869_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_864_, v_x_865_, v_head_867_);
lean_dec(v_x_865_);
v_x_865_ = v___x_869_;
v_x_866_ = v_tail_868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg___boxed(lean_object* v_assignments_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_871_, v_x_872_, v_x_873_);
lean_dec_ref(v_assignments_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object* v_n_875_, lean_object* v_c_876_, lean_object* v_assignments_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_box(1);
v___x_879_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_877_, v___x_878_, v_c_876_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed(lean_object* v_n_880_, lean_object* v_c_881_, lean_object* v_assignments_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(v_n_880_, v_c_881_, v_assignments_882_);
lean_dec_ref(v_assignments_882_);
lean_dec(v_n_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(lean_object* v_n_884_, lean_object* v_assignments_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_885_, v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___boxed(lean_object* v_n_889_, lean_object* v_assignments_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(v_n_889_, v_assignments_890_, v_x_891_, v_x_892_);
lean_dec_ref(v_assignments_890_);
lean_dec(v_n_889_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_instClausePosFin(lean_object* v_n_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
lean_inc_n(v_n_894_, 7);
v___x_895_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed), 2, 1);
lean_closure_set(v___x_895_, 0, v_n_894_);
v___x_896_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed), 2, 1);
lean_closure_set(v___x_896_, 0, v_n_894_);
v___x_897_ = lean_box(0);
v___x_898_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed), 2, 1);
lean_closure_set(v___x_898_, 0, v_n_894_);
v___x_899_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed), 2, 1);
lean_closure_set(v___x_899_, 0, v_n_894_);
v___x_900_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed), 2, 1);
lean_closure_set(v___x_900_, 0, v_n_894_);
v___x_901_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete), 3, 1);
lean_closure_set(v___x_901_, 0, v_n_894_);
v___x_902_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed), 3, 1);
lean_closure_set(v___x_902_, 0, v_n_894_);
v___x_903_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed), 3, 1);
lean_closure_set(v___x_903_, 0, v_n_894_);
v___x_904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_904_, 0, v___x_895_);
lean_ctor_set(v___x_904_, 1, v___x_896_);
lean_ctor_set(v___x_904_, 2, v___x_897_);
lean_ctor_set(v___x_904_, 3, v___x_898_);
lean_ctor_set(v___x_904_, 4, v___x_899_);
lean_ctor_set(v___x_904_, 5, v___x_900_);
lean_ctor_set(v___x_904_, 6, v___x_901_);
lean_ctor_set(v___x_904_, 7, v___x_902_);
lean_ctor_set(v___x_904_, 8, v___x_903_);
return v___x_904_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
}
#ifdef __cplusplus
}
#endif
