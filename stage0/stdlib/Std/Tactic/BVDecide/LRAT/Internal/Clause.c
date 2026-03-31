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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Sat_Literal_negate(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0_value;
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
lean_dec_ref(v_t_14_);
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
lean_dec_ref(v_x_342_);
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
lean_dec_ref(v_x_352_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(lean_object* v_a_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; uint8_t v___x_385_; 
v_key_382_ = lean_ctor_get(v_x_380_, 0);
v_value_383_ = lean_ctor_get(v_x_380_, 1);
v_tail_384_ = lean_ctor_get(v_x_380_, 2);
v___x_385_ = lean_nat_dec_eq(v_key_382_, v_a_379_);
if (v___x_385_ == 0)
{
v_x_380_ = v_tail_384_;
goto _start;
}
else
{
lean_object* v___x_387_; 
lean_inc(v_value_383_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v_value_383_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg___boxed(lean_object* v_a_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_a_388_, v_x_389_);
lean_dec(v_x_389_);
lean_dec(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
return v_x_391_;
}
else
{
lean_object* v_key_393_; lean_object* v_value_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_418_; 
v_key_393_ = lean_ctor_get(v_x_392_, 0);
v_value_394_ = lean_ctor_get(v_x_392_, 1);
v_tail_395_ = lean_ctor_get(v_x_392_, 2);
v_isSharedCheck_418_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_418_ == 0)
{
v___x_397_ = v_x_392_;
v_isShared_398_ = v_isSharedCheck_418_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_value_394_);
lean_inc(v_key_393_);
lean_dec(v_x_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_418_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v_fold_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_399_ = lean_array_get_size(v_x_391_);
v___x_400_ = lean_uint64_of_nat(v_key_393_);
v___x_401_ = 32ULL;
v___x_402_ = lean_uint64_shift_right(v___x_400_, v___x_401_);
v_fold_403_ = lean_uint64_xor(v___x_400_, v___x_402_);
v___x_404_ = 16ULL;
v___x_405_ = lean_uint64_shift_right(v_fold_403_, v___x_404_);
v___x_406_ = lean_uint64_xor(v_fold_403_, v___x_405_);
v___x_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = lean_usize_of_nat(v___x_399_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_sub(v___x_408_, v___x_409_);
v___x_411_ = lean_usize_land(v___x_407_, v___x_410_);
v___x_412_ = lean_array_uget_borrowed(v_x_391_, v___x_411_);
lean_inc(v___x_412_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_412_);
v___x_414_ = v___x_397_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_key_393_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_value_394_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v___x_412_);
v___x_414_ = v_reuseFailAlloc_417_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_array_uset(v_x_391_, v___x_411_, v___x_414_);
v_x_391_ = v___x_415_;
v_x_392_ = v_tail_395_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(lean_object* v_i_419_, lean_object* v_source_420_, lean_object* v_target_421_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_array_get_size(v_source_420_);
v___x_423_ = lean_nat_dec_lt(v_i_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec_ref(v_source_420_);
lean_dec(v_i_419_);
return v_target_421_;
}
else
{
lean_object* v_es_424_; lean_object* v___x_425_; lean_object* v_source_426_; lean_object* v_target_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_es_424_ = lean_array_fget(v_source_420_, v_i_419_);
v___x_425_ = lean_box(0);
v_source_426_ = lean_array_fset(v_source_420_, v_i_419_, v___x_425_);
v_target_427_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(v_target_421_, v_es_424_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_i_419_, v___x_428_);
lean_dec(v_i_419_);
v_i_419_ = v___x_429_;
v_source_420_ = v_source_426_;
v_target_421_ = v_target_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(lean_object* v_n_431_, lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_nbuckets_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_433_ = lean_array_get_size(v_data_432_);
v___x_434_ = lean_unsigned_to_nat(2u);
v_nbuckets_435_ = lean_nat_mul(v___x_433_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_box(0);
v___x_438_ = lean_mk_array(v_nbuckets_435_, v___x_437_);
v___x_439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(v___x_436_, v_data_432_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg___boxed(lean_object* v_n_440_, lean_object* v_data_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_440_, v_data_441_);
lean_dec(v_n_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(lean_object* v_n_443_, lean_object* v_acc_444_, lean_object* v_l_445_){
_start:
{
if (lean_obj_tag(v_acc_444_) == 0)
{
return v_acc_444_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_519_; 
v_val_446_ = lean_ctor_get(v_acc_444_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_acc_444_);
if (v_isSharedCheck_519_ == 0)
{
v___x_448_ = v_acc_444_;
v_isShared_449_ = v_isSharedCheck_519_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_acc_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_519_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_size_450_; lean_object* v_buckets_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v_fst_455_; lean_object* v_snd_456_; lean_object* v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v_fold_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v_bkt_494_; lean_object* v___x_495_; 
v_size_450_ = lean_ctor_get(v_val_446_, 0);
v_buckets_451_ = lean_ctor_get(v_val_446_, 1);
v_fst_452_ = lean_ctor_get(v_l_445_, 0);
v_snd_453_ = lean_ctor_get(v_l_445_, 1);
v___x_481_ = lean_array_get_size(v_buckets_451_);
v___x_482_ = lean_uint64_of_nat(v_fst_452_);
v___x_483_ = 32ULL;
v___x_484_ = lean_uint64_shift_right(v___x_482_, v___x_483_);
v_fold_485_ = lean_uint64_xor(v___x_482_, v___x_484_);
v___x_486_ = 16ULL;
v___x_487_ = lean_uint64_shift_right(v_fold_485_, v___x_486_);
v___x_488_ = lean_uint64_xor(v_fold_485_, v___x_487_);
v___x_489_ = lean_uint64_to_usize(v___x_488_);
v___x_490_ = lean_usize_of_nat(v___x_481_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_sub(v___x_490_, v___x_491_);
v___x_493_ = lean_usize_land(v___x_489_, v___x_492_);
v_bkt_494_ = lean_array_uget_borrowed(v_buckets_451_, v___x_493_);
v___x_495_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_fst_452_, v_bkt_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_516_; 
lean_inc_ref(v_buckets_451_);
lean_inc(v_size_450_);
v_isSharedCheck_516_ = !lean_is_exclusive(v_val_446_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_517_ = lean_ctor_get(v_val_446_, 1);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_val_446_, 0);
lean_dec(v_unused_518_);
v___x_497_ = v_val_446_;
v_isShared_498_ = v_isSharedCheck_516_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_val_446_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_516_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v_size_x27_500_; lean_object* v___x_501_; lean_object* v_buckets_x27_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v_size_x27_500_ = lean_nat_add(v_size_450_, v___x_499_);
lean_dec(v_size_450_);
lean_inc(v_bkt_494_);
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
v___x_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_501_, 0, v_fst_452_);
lean_ctor_set(v___x_501_, 1, v_snd_453_);
lean_ctor_set(v___x_501_, 2, v_bkt_494_);
v_buckets_x27_502_ = lean_array_uset(v_buckets_451_, v___x_493_, v___x_501_);
v___x_503_ = lean_unsigned_to_nat(4u);
v___x_504_ = lean_nat_mul(v_size_x27_500_, v___x_503_);
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_nat_div(v___x_504_, v___x_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_array_get_size(v_buckets_x27_502_);
v___x_508_ = lean_nat_dec_le(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
if (v___x_508_ == 0)
{
lean_object* v_val_509_; lean_object* v___x_511_; 
v_val_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_443_, v_buckets_x27_502_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_val_509_);
lean_ctor_set(v___x_497_, 0, v_size_x27_500_);
v___x_511_ = v___x_497_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_size_x27_500_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_val_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
v_fst_455_ = v___x_495_;
v_snd_456_ = v___x_511_;
goto v___jp_454_;
}
}
else
{
lean_object* v___x_514_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_buckets_x27_502_);
lean_ctor_set(v___x_497_, 0, v_size_x27_500_);
v___x_514_ = v___x_497_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_size_x27_500_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_buckets_x27_502_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v_fst_455_ = v___x_495_;
v_snd_456_ = v___x_514_;
goto v___jp_454_;
}
}
}
}
else
{
v_fst_455_ = v___x_495_;
v_snd_456_ = v_val_446_;
goto v___jp_454_;
}
v___jp_454_:
{
if (lean_obj_tag(v_fst_455_) == 1)
{
uint8_t v___x_457_; 
lean_del_object(v___x_448_);
v___x_457_ = lean_unbox(v_snd_453_);
if (v___x_457_ == 0)
{
lean_object* v_val_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v_val_458_ = lean_ctor_get(v_fst_455_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_fst_455_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v_fst_455_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_val_458_);
lean_dec(v_fst_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = lean_unbox(v_val_458_);
lean_dec(v_val_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_snd_456_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_snd_456_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_object* v___x_466_; 
lean_del_object(v___x_460_);
lean_dec(v_snd_456_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
}
else
{
lean_object* v_val_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_val_468_ = lean_ctor_get(v_fst_455_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_fst_455_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_fst_455_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_val_468_);
lean_dec(v_fst_455_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; 
v___x_472_ = lean_unbox(v_val_468_);
lean_dec(v_val_468_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_del_object(v___x_470_);
lean_dec(v_snd_456_);
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v___x_475_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_snd_456_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_snd_456_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v_fst_455_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_snd_456_);
v___x_479_ = v___x_448_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_snd_456_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(lean_object* v_n_520_, lean_object* v_acc_521_, lean_object* v_l_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_520_, v_acc_521_, v_l_522_);
lean_dec_ref(v_l_522_);
lean_dec(v_n_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(lean_object* v_n_524_, lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(lean_object* v_n_529_, lean_object* v_00_u03b2_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(v_n_529_, v_00_u03b2_530_, v_a_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_a_531_);
lean_dec(v_n_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(lean_object* v_n_534_, lean_object* v_00_u03b2_535_, lean_object* v_data_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_534_, v_data_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(lean_object* v_n_538_, lean_object* v_00_u03b2_539_, lean_object* v_data_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(v_n_538_, v_00_u03b2_539_, v_data_540_);
lean_dec(v_n_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(lean_object* v_n_542_, lean_object* v_00_u03b2_543_, lean_object* v_i_544_, lean_object* v_source_545_, lean_object* v_target_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(v_i_544_, v_source_545_, v_target_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___boxed(lean_object* v_n_548_, lean_object* v_00_u03b2_549_, lean_object* v_i_550_, lean_object* v_source_551_, lean_object* v_target_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(v_n_548_, v_00_u03b2_549_, v_i_550_, v_source_551_, v_target_552_);
lean_dec(v_n_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(v_x_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object* v_acc_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
if (lean_obj_tag(v_acc_558_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_h__2_560_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_1(v_h__1_559_, v___x_561_);
return v___x_562_;
}
else
{
lean_object* v_val_563_; lean_object* v___x_564_; 
lean_dec(v_h__1_559_);
v_val_563_ = lean_ctor_get(v_acc_558_, 0);
lean_inc(v_val_563_);
lean_dec_ref(v_acc_558_);
v___x_564_ = lean_apply_1(v_h__2_560_, v_val_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object* v_n_565_, lean_object* v_motive_566_, lean_object* v_acc_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_){
_start:
{
if (lean_obj_tag(v_acc_567_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_h__2_569_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v_h__1_568_, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_573_; 
lean_dec(v_h__1_568_);
v_val_572_ = lean_ctor_get(v_acc_567_, 0);
lean_inc(v_val_572_);
lean_dec_ref(v_acc_567_);
v___x_573_ = lean_apply_1(v_h__2_569_, v_val_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object* v_n_574_, lean_object* v_motive_575_, lean_object* v_acc_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_574_, v_motive_575_, v_acc_576_, v_h__1_577_, v_h__2_578_);
lean_dec(v_n_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_inc(v_x_580_);
return v_x_580_;
}
else
{
lean_object* v_key_582_; lean_object* v_value_583_; lean_object* v_tail_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_key_582_ = lean_ctor_get(v_x_581_, 0);
v_value_583_ = lean_ctor_get(v_x_581_, 1);
v_tail_584_ = lean_ctor_get(v_x_581_, 2);
v___x_585_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_580_, v_tail_584_);
lean_inc(v_value_583_);
lean_inc(v_key_582_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_key_582_);
lean_ctor_set(v___x_586_, 1, v_value_583_);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_588_, v_x_589_);
lean_dec(v_x_589_);
lean_dec(v_x_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_, lean_object* v_b_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_eq(v_i_592_, v_stop_593_);
if (v___x_595_ == 0)
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_sub(v_i_592_, v___x_596_);
v___x_598_ = lean_array_uget_borrowed(v_as_591_, v___x_597_);
v___x_599_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_b_594_, v___x_598_);
lean_dec(v_b_594_);
v_i_592_ = v___x_597_;
v_b_594_ = v___x_599_;
goto _start;
}
else
{
return v_b_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_stop_603_, lean_object* v_b_604_){
_start:
{
size_t v_i_boxed_605_; size_t v_stop_boxed_606_; lean_object* v_res_607_; 
v_i_boxed_605_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_stop_boxed_606_ = lean_unbox_usize(v_stop_603_);
lean_dec(v_stop_603_);
v_res_607_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_as_601_, v_i_boxed_605_, v_stop_boxed_606_, v_b_604_);
lean_dec_ref(v_as_601_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(lean_object* v_n_608_, lean_object* v_as_609_, size_t v_i_610_, size_t v_stop_611_, lean_object* v_b_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_eq(v_i_610_, v_stop_611_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; size_t v___x_616_; size_t v___x_617_; 
v___x_614_ = lean_array_uget_borrowed(v_as_609_, v_i_610_);
v___x_615_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_608_, v_b_612_, v___x_614_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_610_, v___x_616_);
v_i_610_ = v___x_617_;
v_b_612_ = v___x_615_;
goto _start;
}
else
{
return v_b_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2___boxed(lean_object* v_n_619_, lean_object* v_as_620_, lean_object* v_i_621_, lean_object* v_stop_622_, lean_object* v_b_623_){
_start:
{
size_t v_i_boxed_624_; size_t v_stop_boxed_625_; lean_object* v_res_626_; 
v_i_boxed_624_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_stop_boxed_625_ = lean_unbox_usize(v_stop_622_);
lean_dec(v_stop_622_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_619_, v_as_620_, v_i_boxed_624_, v_stop_boxed_625_, v_b_623_);
lean_dec_ref(v_as_620_);
lean_dec(v_n_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object* v_n_629_, lean_object* v_ls_630_){
_start:
{
lean_object* v_buckets_632_; lean_object* v___y_643_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_647_ = lean_array_get_size(v_ls_630_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_mul(v___x_647_, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(3u);
v___x_652_ = lean_nat_div(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = l_Nat_nextPowerOfTwo(v___x_652_);
lean_dec(v___x_652_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_mk_array(v___x_653_, v___x_654_);
v___x_656_ = lean_nat_dec_lt(v___x_648_, v___x_647_);
if (v___x_656_ == 0)
{
v_buckets_632_ = v___x_655_;
goto v___jp_631_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
lean_inc_ref(v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_648_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = lean_nat_dec_le(v___x_647_, v___x_647_);
if (v___x_659_ == 0)
{
if (v___x_656_ == 0)
{
lean_dec_ref(v___x_658_);
v_buckets_632_ = v___x_655_;
goto v___jp_631_;
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v___x_655_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_647_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_629_, v_ls_630_, v___x_660_, v___x_661_, v___x_658_);
v___y_643_ = v___x_662_;
goto v___jp_642_;
}
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v___x_655_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_647_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_629_, v_ls_630_, v___x_663_, v___x_664_, v___x_658_);
v___y_643_ = v___x_665_;
goto v___jp_642_;
}
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_box(0);
v___x_634_ = lean_array_get_size(v_buckets_632_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_nat_dec_lt(v___x_635_, v___x_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec_ref(v_buckets_632_);
v___x_637_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0));
return v___x_637_;
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_usize_of_nat(v___x_634_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_buckets_632_, v___x_638_, v___x_639_, v___x_633_);
lean_dec_ref(v_buckets_632_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
v___jp_642_:
{
if (lean_obj_tag(v___y_643_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_box(0);
return v___x_644_;
}
else
{
lean_object* v_val_645_; lean_object* v_buckets_646_; 
v_val_645_ = lean_ctor_get(v___y_643_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v___y_643_);
v_buckets_646_ = lean_ctor_get(v_val_645_, 1);
lean_inc_ref(v_buckets_646_);
lean_dec(v_val_645_);
v_buckets_632_ = v_buckets_646_;
goto v___jp_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed(lean_object* v_n_666_, lean_object* v_ls_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_666_, v_ls_667_);
lean_dec_ref(v_ls_667_);
lean_dec(v_n_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter___redArg(lean_object* v_val_x3f_669_, lean_object* v_h__1_670_, lean_object* v_h__2_671_){
_start:
{
if (lean_obj_tag(v_val_x3f_669_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; 
lean_dec(v_h__2_671_);
v_val_672_ = lean_ctor_get(v_val_x3f_669_, 0);
lean_inc(v_val_672_);
lean_dec_ref(v_val_x3f_669_);
v___x_673_ = lean_apply_1(v_h__1_670_, v_val_672_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
lean_dec(v_h__1_670_);
v___x_674_ = lean_apply_2(v_h__2_671_, v_val_x3f_669_, lean_box(0));
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter(lean_object* v_motive_675_, lean_object* v_val_x3f_676_, lean_object* v_h__1_677_, lean_object* v_h__2_678_){
_start:
{
if (lean_obj_tag(v_val_x3f_676_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; 
lean_dec(v_h__2_678_);
v_val_679_ = lean_ctor_get(v_val_x3f_676_, 0);
lean_inc(v_val_679_);
lean_dec_ref(v_val_x3f_676_);
v___x_680_ = lean_apply_1(v_h__1_677_, v_val_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
lean_dec(v_h__1_677_);
v___x_681_ = lean_apply_2(v_h__2_678_, v_val_x3f_676_, lean_box(0));
return v___x_681_;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0(void){
_start:
{
lean_object* v___x_682_; lean_object* v___f_683_; 
v___x_682_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_683_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_683_, 0, v___x_682_);
return v___f_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete(lean_object* v_n_686_, lean_object* v_c_687_, lean_object* v_l_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_689_, 0, v_n_686_);
v___f_690_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_690_, 0, v___x_689_);
v___f_691_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_692_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_692_, 0, v___f_690_);
lean_closure_set(v___f_692_, 1, v___f_691_);
v___x_693_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1));
lean_inc(v_c_687_);
v___x_694_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_box(0), v___f_692_, v_c_687_, v_l_688_, v_c_687_, v___x_693_);
lean_dec(v_c_687_);
return v___x_694_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(lean_object* v_n_695_, lean_object* v_c_696_, lean_object* v_l_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___f_701_; uint8_t v___x_702_; 
v___x_698_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_698_, 0, v_n_695_);
v___f_699_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_699_, 0, v___x_698_);
v___f_700_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_701_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_701_, 0, v___f_699_);
lean_closure_set(v___f_701_, 1, v___f_700_);
v___x_702_ = l_List_elem___redArg(v___f_701_, v_l_697_, v_c_696_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed(lean_object* v_n_703_, lean_object* v_c_704_, lean_object* v_l_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(v_n_703_, v_c_704_, v_l_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(lean_object* v_assignments_708_, lean_object* v_acc_709_, lean_object* v_l_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = 0;
switch(lean_obj_tag(v_acc_709_))
{
case 1:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_fst_712_ = lean_ctor_get(v_l_710_, 0);
v_snd_713_ = lean_ctor_get(v_l_710_, 1);
v___x_714_ = lean_box(v___x_711_);
v___x_715_ = lean_array_get(v___x_714_, v_assignments_708_, v_fst_712_);
lean_dec(v___x_714_);
v___x_716_ = lean_unbox(v___x_715_);
lean_dec(v___x_715_);
switch(v___x_716_)
{
case 0:
{
uint8_t v___x_717_; 
v___x_717_ = lean_unbox(v_snd_713_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_l_710_);
return v_acc_709_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_718_, 0, v_l_710_);
return v___x_718_;
}
}
case 1:
{
uint8_t v___x_719_; 
v___x_719_ = lean_unbox(v_snd_713_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_720_, 0, v_l_710_);
return v___x_720_;
}
else
{
lean_dec_ref(v_l_710_);
return v_acc_709_;
}
}
case 2:
{
lean_object* v___x_721_; 
lean_dec_ref(v_l_710_);
v___x_721_ = lean_box(0);
return v___x_721_;
}
default: 
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_722_, 0, v_l_710_);
return v___x_722_;
}
}
}
case 2:
{
lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_fst_723_ = lean_ctor_get(v_l_710_, 0);
lean_inc(v_fst_723_);
v_snd_724_ = lean_ctor_get(v_l_710_, 1);
lean_inc(v_snd_724_);
lean_dec_ref(v_l_710_);
v___x_725_ = lean_box(v___x_711_);
v___x_726_ = lean_array_get(v___x_725_, v_assignments_708_, v_fst_723_);
lean_dec(v_fst_723_);
lean_dec(v___x_725_);
v___x_727_ = lean_unbox(v___x_726_);
lean_dec(v___x_726_);
switch(v___x_727_)
{
case 0:
{
uint8_t v___x_728_; 
v___x_728_ = lean_unbox(v_snd_724_);
lean_dec(v_snd_724_);
if (v___x_728_ == 0)
{
lean_inc_ref(v_acc_709_);
return v_acc_709_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = lean_box(3);
return v___x_729_;
}
}
case 1:
{
uint8_t v___x_730_; 
v___x_730_ = lean_unbox(v_snd_724_);
lean_dec(v_snd_724_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(3);
return v___x_731_;
}
else
{
lean_inc_ref(v_acc_709_);
return v_acc_709_;
}
}
case 2:
{
lean_object* v___x_732_; 
lean_dec(v_snd_724_);
v___x_732_ = lean_box(0);
return v___x_732_;
}
default: 
{
lean_object* v___x_733_; 
lean_dec(v_snd_724_);
v___x_733_ = lean_box(3);
return v___x_733_;
}
}
}
default: 
{
lean_dec_ref(v_l_710_);
lean_inc(v_acc_709_);
return v_acc_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg___boxed(lean_object* v_assignments_734_, lean_object* v_acc_735_, lean_object* v_l_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_734_, v_acc_735_, v_l_736_);
lean_dec(v_acc_735_);
lean_dec_ref(v_assignments_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(lean_object* v_n_738_, lean_object* v_assignments_739_, lean_object* v_acc_740_, lean_object* v_l_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_739_, v_acc_740_, v_l_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___boxed(lean_object* v_n_743_, lean_object* v_assignments_744_, lean_object* v_acc_745_, lean_object* v_l_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(v_n_743_, v_assignments_744_, v_acc_745_, v_l_746_);
lean_dec(v_acc_745_);
lean_dec_ref(v_assignments_744_);
lean_dec(v_n_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(lean_object* v_assignments_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
return v_x_749_;
}
else
{
lean_object* v_head_751_; lean_object* v_tail_752_; lean_object* v___x_753_; 
v_head_751_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_head_751_);
v_tail_752_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_tail_752_);
lean_dec_ref(v_x_750_);
v___x_753_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_748_, v_x_749_, v_head_751_);
lean_dec(v_x_749_);
v_x_749_ = v___x_753_;
v_x_750_ = v_tail_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg___boxed(lean_object* v_assignments_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_755_, v_x_756_, v_x_757_);
lean_dec_ref(v_assignments_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object* v_n_759_, lean_object* v_c_760_, lean_object* v_assignments_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(1);
v___x_763_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_761_, v___x_762_, v_c_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed(lean_object* v_n_764_, lean_object* v_c_765_, lean_object* v_assignments_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(v_n_764_, v_c_765_, v_assignments_766_);
lean_dec_ref(v_assignments_766_);
lean_dec(v_n_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(lean_object* v_n_768_, lean_object* v_assignments_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_769_, v_x_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___boxed(lean_object* v_n_773_, lean_object* v_assignments_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(v_n_773_, v_assignments_774_, v_x_775_, v_x_776_);
lean_dec_ref(v_assignments_774_);
lean_dec(v_n_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_instClausePosFin(lean_object* v_n_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_n(v_n_778_, 7);
v___x_779_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed), 2, 1);
lean_closure_set(v___x_779_, 0, v_n_778_);
v___x_780_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed), 2, 1);
lean_closure_set(v___x_780_, 0, v_n_778_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed), 2, 1);
lean_closure_set(v___x_782_, 0, v_n_778_);
v___x_783_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed), 2, 1);
lean_closure_set(v___x_783_, 0, v_n_778_);
v___x_784_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed), 2, 1);
lean_closure_set(v___x_784_, 0, v_n_778_);
v___x_785_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete), 3, 1);
lean_closure_set(v___x_785_, 0, v_n_778_);
v___x_786_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed), 3, 1);
lean_closure_set(v___x_786_, 0, v_n_778_);
v___x_787_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed), 3, 1);
lean_closure_set(v___x_787_, 0, v_n_778_);
v___x_788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_788_, 0, v___x_779_);
lean_ctor_set(v___x_788_, 1, v___x_780_);
lean_ctor_set(v___x_788_, 2, v___x_781_);
lean_ctor_set(v___x_788_, 3, v___x_782_);
lean_ctor_set(v___x_788_, 4, v___x_783_);
lean_ctor_set(v___x_788_, 5, v___x_784_);
lean_ctor_set(v___x_788_, 6, v___x_785_);
lean_ctor_set(v___x_788_, 7, v___x_786_);
lean_ctor_set(v___x_788_, 8, v___x_787_);
return v___x_788_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
