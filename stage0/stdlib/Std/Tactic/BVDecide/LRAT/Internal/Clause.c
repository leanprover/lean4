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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___y_447_; uint8_t v___y_448_; 
if (lean_obj_tag(v_acc_444_) == 0)
{
return v_acc_444_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_511_; 
v_val_452_ = lean_ctor_get(v_acc_444_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_acc_444_);
if (v_isSharedCheck_511_ == 0)
{
v___x_454_ = v_acc_444_;
v_isShared_455_ = v_isSharedCheck_511_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_acc_444_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_511_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_size_456_; lean_object* v_buckets_457_; lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v_bkt_486_; lean_object* v___x_487_; 
v_size_456_ = lean_ctor_get(v_val_452_, 0);
v_buckets_457_ = lean_ctor_get(v_val_452_, 1);
v_fst_458_ = lean_ctor_get(v_l_445_, 0);
v_snd_459_ = lean_ctor_get(v_l_445_, 1);
v___x_473_ = lean_array_get_size(v_buckets_457_);
v___x_474_ = lean_uint64_of_nat(v_fst_458_);
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___x_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___x_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_473_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v_bkt_486_ = lean_array_uget_borrowed(v_buckets_457_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_fst_458_, v_bkt_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_508_; 
lean_inc_ref(v_buckets_457_);
lean_inc(v_size_456_);
v_isSharedCheck_508_ = !lean_is_exclusive(v_val_452_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; lean_object* v_unused_510_; 
v_unused_509_ = lean_ctor_get(v_val_452_, 1);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_val_452_, 0);
lean_dec(v_unused_510_);
v___x_489_ = v_val_452_;
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_val_452_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v_size_x27_492_; lean_object* v___x_493_; lean_object* v_buckets_x27_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v_size_x27_492_ = lean_nat_add(v_size_456_, v___x_491_);
lean_dec(v_size_456_);
lean_inc(v_bkt_486_);
lean_inc(v_snd_459_);
lean_inc(v_fst_458_);
v___x_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_493_, 0, v_fst_458_);
lean_ctor_set(v___x_493_, 1, v_snd_459_);
lean_ctor_set(v___x_493_, 2, v_bkt_486_);
v_buckets_x27_494_ = lean_array_uset(v_buckets_457_, v___x_485_, v___x_493_);
v___x_495_ = lean_unsigned_to_nat(4u);
v___x_496_ = lean_nat_mul(v_size_x27_492_, v___x_495_);
v___x_497_ = lean_unsigned_to_nat(3u);
v___x_498_ = lean_nat_div(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_array_get_size(v_buckets_x27_494_);
v___x_500_ = lean_nat_dec_le(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
if (v___x_500_ == 0)
{
lean_object* v_val_501_; lean_object* v___x_503_; 
v_val_501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_443_, v_buckets_x27_494_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_val_501_);
lean_ctor_set(v___x_489_, 0, v_size_x27_492_);
v___x_503_ = v___x_489_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_size_x27_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_val_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v_fst_461_ = v___x_487_;
v_snd_462_ = v___x_503_;
goto v___jp_460_;
}
}
else
{
lean_object* v___x_506_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_buckets_x27_494_);
lean_ctor_set(v___x_489_, 0, v_size_x27_492_);
v___x_506_ = v___x_489_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_size_x27_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_buckets_x27_494_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_fst_461_ = v___x_487_;
v_snd_462_ = v___x_506_;
goto v___jp_460_;
}
}
}
}
else
{
v_fst_461_ = v___x_487_;
v_snd_462_ = v_val_452_;
goto v___jp_460_;
}
v___jp_460_:
{
if (lean_obj_tag(v_fst_461_) == 1)
{
uint8_t v___x_463_; 
lean_del_object(v___x_454_);
v___x_463_ = lean_unbox(v_snd_459_);
if (v___x_463_ == 0)
{
lean_object* v_val_464_; uint8_t v___x_465_; 
v_val_464_ = lean_ctor_get(v_fst_461_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v_fst_461_, 1);
v___x_465_ = lean_unbox(v_val_464_);
lean_dec(v_val_464_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 1;
v___y_447_ = v_snd_462_;
v___y_448_ = v___x_466_;
goto v___jp_446_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = lean_unbox(v_snd_459_);
v___y_447_ = v_snd_462_;
v___y_448_ = v___x_467_;
goto v___jp_446_;
}
}
else
{
lean_object* v_val_468_; uint8_t v___x_469_; 
v_val_468_ = lean_ctor_get(v_fst_461_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v_fst_461_, 1);
v___x_469_ = lean_unbox(v_val_468_);
lean_dec(v_val_468_);
v___y_447_ = v_snd_462_;
v___y_448_ = v___x_469_;
goto v___jp_446_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_fst_461_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_snd_462_);
v___x_471_ = v___x_454_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_snd_462_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
v___jp_446_:
{
uint8_t v___x_449_; 
v___x_449_ = lean_bool_not(v___y_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___y_447_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; 
lean_dec(v___y_447_);
v___x_451_ = lean_box(0);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(lean_object* v_n_512_, lean_object* v_acc_513_, lean_object* v_l_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_512_, v_acc_513_, v_l_514_);
lean_dec_ref(v_l_514_);
lean_dec(v_n_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(lean_object* v_n_516_, lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_a_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(lean_object* v_n_521_, lean_object* v_00_u03b2_522_, lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(v_n_521_, v_00_u03b2_522_, v_a_523_, v_x_524_);
lean_dec(v_x_524_);
lean_dec(v_a_523_);
lean_dec(v_n_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(lean_object* v_n_526_, lean_object* v_00_u03b2_527_, lean_object* v_data_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_526_, v_data_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(lean_object* v_n_530_, lean_object* v_00_u03b2_531_, lean_object* v_data_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(v_n_530_, v_00_u03b2_531_, v_data_532_);
lean_dec(v_n_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(lean_object* v_n_534_, lean_object* v_00_u03b2_535_, lean_object* v_i_536_, lean_object* v_source_537_, lean_object* v_target_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(v_i_536_, v_source_537_, v_target_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___boxed(lean_object* v_n_540_, lean_object* v_00_u03b2_541_, lean_object* v_i_542_, lean_object* v_source_543_, lean_object* v_target_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(v_n_540_, v_00_u03b2_541_, v_i_542_, v_source_543_, v_target_544_);
lean_dec(v_n_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(v_x_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object* v_acc_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
if (lean_obj_tag(v_acc_550_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_h__2_552_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_h__1_551_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_556_; 
lean_dec(v_h__1_551_);
v_val_555_ = lean_ctor_get(v_acc_550_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_acc_550_, 1);
v___x_556_ = lean_apply_1(v_h__2_552_, v_val_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object* v_n_557_, lean_object* v_motive_558_, lean_object* v_acc_559_, lean_object* v_h__1_560_, lean_object* v_h__2_561_){
_start:
{
if (lean_obj_tag(v_acc_559_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_561_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_apply_1(v_h__1_560_, v___x_562_);
return v___x_563_;
}
else
{
lean_object* v_val_564_; lean_object* v___x_565_; 
lean_dec(v_h__1_560_);
v_val_564_ = lean_ctor_get(v_acc_559_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v_acc_559_, 1);
v___x_565_ = lean_apply_1(v_h__2_561_, v_val_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object* v_n_566_, lean_object* v_motive_567_, lean_object* v_acc_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_566_, v_motive_567_, v_acc_568_, v_h__1_569_, v_h__2_570_);
lean_dec(v_n_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_inc(v_x_572_);
return v_x_572_;
}
else
{
lean_object* v_key_574_; lean_object* v_value_575_; lean_object* v_tail_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_key_574_ = lean_ctor_get(v_x_573_, 0);
v_value_575_ = lean_ctor_get(v_x_573_, 1);
v_tail_576_ = lean_ctor_get(v_x_573_, 2);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_572_, v_tail_576_);
lean_inc(v_value_575_);
lean_inc(v_key_574_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_key_574_);
lean_ctor_set(v___x_578_, 1, v_value_575_);
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec(v_x_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(lean_object* v_as_583_, size_t v_i_584_, size_t v_stop_585_, lean_object* v_b_586_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_eq(v_i_584_, v_stop_585_);
if (v___x_587_ == 0)
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_sub(v_i_584_, v___x_588_);
v___x_590_ = lean_array_uget_borrowed(v_as_583_, v___x_589_);
v___x_591_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_b_586_, v___x_590_);
lean_dec(v_b_586_);
v_i_584_ = v___x_589_;
v_b_586_ = v___x_591_;
goto _start;
}
else
{
return v_b_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_, lean_object* v_b_596_){
_start:
{
size_t v_i_boxed_597_; size_t v_stop_boxed_598_; lean_object* v_res_599_; 
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_as_593_, v_i_boxed_597_, v_stop_boxed_598_, v_b_596_);
lean_dec_ref(v_as_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(lean_object* v_n_600_, lean_object* v_as_601_, size_t v_i_602_, size_t v_stop_603_, lean_object* v_b_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_602_, v_stop_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; 
v___x_606_ = lean_array_uget_borrowed(v_as_601_, v_i_602_);
v___x_607_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(v_n_600_, v_b_604_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_602_, v___x_608_);
v_i_602_ = v___x_609_;
v_b_604_ = v___x_607_;
goto _start;
}
else
{
return v_b_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2___boxed(lean_object* v_n_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_){
_start:
{
size_t v_i_boxed_616_; size_t v_stop_boxed_617_; lean_object* v_res_618_; 
v_i_boxed_616_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_617_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_611_, v_as_612_, v_i_boxed_616_, v_stop_boxed_617_, v_b_615_);
lean_dec_ref(v_as_612_);
lean_dec(v_n_611_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object* v_n_621_, lean_object* v_ls_622_){
_start:
{
lean_object* v_buckets_624_; lean_object* v___y_635_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_639_ = lean_array_get_size(v_ls_622_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_unsigned_to_nat(4u);
v___x_642_ = lean_nat_mul(v___x_639_, v___x_641_);
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = lean_nat_div(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
v___x_645_ = l_Nat_nextPowerOfTwo(v___x_644_);
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_mk_array(v___x_645_, v___x_646_);
v___x_648_ = lean_nat_dec_lt(v___x_640_, v___x_639_);
if (v___x_648_ == 0)
{
v_buckets_624_ = v___x_647_;
goto v___jp_623_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
lean_inc_ref(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_640_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_nat_dec_le(v___x_639_, v___x_639_);
if (v___x_651_ == 0)
{
if (v___x_648_ == 0)
{
lean_dec_ref_known(v___x_650_, 1);
v_buckets_624_ = v___x_647_;
goto v___jp_623_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
lean_dec_ref(v___x_647_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_639_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_621_, v_ls_622_, v___x_652_, v___x_653_, v___x_650_);
v___y_635_ = v___x_654_;
goto v___jp_634_;
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v___x_647_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_639_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_621_, v_ls_622_, v___x_655_, v___x_656_, v___x_650_);
v___y_635_ = v___x_657_;
goto v___jp_634_;
}
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_array_get_size(v_buckets_624_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_lt(v___x_627_, v___x_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec_ref(v_buckets_624_);
v___x_629_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0));
return v___x_629_;
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_usize_of_nat(v___x_626_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_buckets_624_, v___x_630_, v___x_631_, v___x_625_);
lean_dec_ref(v_buckets_624_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
v___jp_634_:
{
if (lean_obj_tag(v___y_635_) == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_box(0);
return v___x_636_;
}
else
{
lean_object* v_val_637_; lean_object* v_buckets_638_; 
v_val_637_ = lean_ctor_get(v___y_635_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___y_635_, 1);
v_buckets_638_ = lean_ctor_get(v_val_637_, 1);
lean_inc_ref(v_buckets_638_);
lean_dec(v_val_637_);
v_buckets_624_ = v_buckets_638_;
goto v___jp_623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed(lean_object* v_n_658_, lean_object* v_ls_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_658_, v_ls_659_);
lean_dec_ref(v_ls_659_);
lean_dec(v_n_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter___redArg(lean_object* v_val_x3f_661_, lean_object* v_h__1_662_, lean_object* v_h__2_663_){
_start:
{
if (lean_obj_tag(v_val_x3f_661_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_663_);
v_val_664_ = lean_ctor_get(v_val_x3f_661_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_val_x3f_661_, 1);
v___x_665_ = lean_apply_1(v_h__1_662_, v_val_664_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; 
lean_dec(v_h__1_662_);
v___x_666_ = lean_apply_2(v_h__2_663_, v_val_x3f_661_, lean_box(0));
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter(lean_object* v_motive_667_, lean_object* v_val_x3f_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_){
_start:
{
if (lean_obj_tag(v_val_x3f_668_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; 
lean_dec(v_h__2_670_);
v_val_671_ = lean_ctor_get(v_val_x3f_668_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_val_x3f_668_, 1);
v___x_672_ = lean_apply_1(v_h__1_669_, v_val_671_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; 
lean_dec(v_h__1_669_);
v___x_673_ = lean_apply_2(v_h__2_670_, v_val_x3f_668_, lean_box(0));
return v___x_673_;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___f_675_; 
v___x_674_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_675_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_675_, 0, v___x_674_);
return v___f_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete(lean_object* v_n_678_, lean_object* v_c_679_, lean_object* v_l_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_681_, 0, v_n_678_);
v___f_682_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_682_, 0, v___x_681_);
v___f_683_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_684_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_684_, 0, v___f_682_);
lean_closure_set(v___f_684_, 1, v___f_683_);
v___x_685_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1));
lean_inc(v_c_679_);
v___x_686_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_box(0), v___f_684_, v_c_679_, v_l_680_, v_c_679_, v___x_685_);
lean_dec(v_c_679_);
return v___x_686_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(lean_object* v_n_687_, lean_object* v_c_688_, lean_object* v_l_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___f_693_; uint8_t v___x_694_; 
v___x_690_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_690_, 0, v_n_687_);
v___f_691_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_691_, 0, v___x_690_);
v___f_692_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0);
v___f_693_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_693_, 0, v___f_691_);
lean_closure_set(v___f_693_, 1, v___f_692_);
v___x_694_ = l_List_elem___redArg(v___f_693_, v_l_689_, v_c_688_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed(lean_object* v_n_695_, lean_object* v_c_696_, lean_object* v_l_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(v_n_695_, v_c_696_, v_l_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(lean_object* v_assignments_700_, lean_object* v_acc_701_, lean_object* v_l_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = 0;
switch(lean_obj_tag(v_acc_701_))
{
case 1:
{
lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_fst_704_ = lean_ctor_get(v_l_702_, 0);
v_snd_705_ = lean_ctor_get(v_l_702_, 1);
v___x_706_ = lean_box(v___x_703_);
v___x_707_ = lean_array_get(v___x_706_, v_assignments_700_, v_fst_704_);
lean_dec(v___x_706_);
v___x_708_ = lean_unbox(v___x_707_);
lean_dec(v___x_707_);
switch(v___x_708_)
{
case 0:
{
uint8_t v___x_709_; 
v___x_709_ = lean_unbox(v_snd_705_);
if (v___x_709_ == 0)
{
lean_dec_ref(v_l_702_);
return v_acc_701_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_710_, 0, v_l_702_);
return v___x_710_;
}
}
case 1:
{
uint8_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_unbox(v_snd_705_);
v___x_712_ = lean_bool_not(v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_l_702_);
return v_acc_701_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_713_, 0, v_l_702_);
return v___x_713_;
}
}
case 2:
{
lean_object* v___x_714_; 
lean_dec_ref(v_l_702_);
v___x_714_ = lean_box(0);
return v___x_714_;
}
default: 
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_715_, 0, v_l_702_);
return v___x_715_;
}
}
}
case 2:
{
lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_fst_716_ = lean_ctor_get(v_l_702_, 0);
lean_inc(v_fst_716_);
v_snd_717_ = lean_ctor_get(v_l_702_, 1);
lean_inc(v_snd_717_);
lean_dec_ref(v_l_702_);
v___x_718_ = lean_box(v___x_703_);
v___x_719_ = lean_array_get(v___x_718_, v_assignments_700_, v_fst_716_);
lean_dec(v_fst_716_);
lean_dec(v___x_718_);
v___x_720_ = lean_unbox(v___x_719_);
lean_dec(v___x_719_);
switch(v___x_720_)
{
case 0:
{
uint8_t v___x_721_; 
v___x_721_ = lean_unbox(v_snd_717_);
lean_dec(v_snd_717_);
if (v___x_721_ == 0)
{
lean_inc_ref(v_acc_701_);
return v_acc_701_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(3);
return v___x_722_;
}
}
case 1:
{
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_unbox(v_snd_717_);
lean_dec(v_snd_717_);
v___x_724_ = lean_bool_not(v___x_723_);
if (v___x_724_ == 0)
{
lean_inc_ref(v_acc_701_);
return v_acc_701_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(3);
return v___x_725_;
}
}
case 2:
{
lean_object* v___x_726_; 
lean_dec(v_snd_717_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
default: 
{
lean_object* v___x_727_; 
lean_dec(v_snd_717_);
v___x_727_ = lean_box(3);
return v___x_727_;
}
}
}
default: 
{
lean_dec_ref(v_l_702_);
lean_inc(v_acc_701_);
return v_acc_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg___boxed(lean_object* v_assignments_728_, lean_object* v_acc_729_, lean_object* v_l_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_728_, v_acc_729_, v_l_730_);
lean_dec(v_acc_729_);
lean_dec_ref(v_assignments_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(lean_object* v_n_732_, lean_object* v_assignments_733_, lean_object* v_acc_734_, lean_object* v_l_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_733_, v_acc_734_, v_l_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___boxed(lean_object* v_n_737_, lean_object* v_assignments_738_, lean_object* v_acc_739_, lean_object* v_l_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(v_n_737_, v_assignments_738_, v_acc_739_, v_l_740_);
lean_dec(v_acc_739_);
lean_dec_ref(v_assignments_738_);
lean_dec(v_n_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(lean_object* v_assignments_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
return v_x_743_;
}
else
{
lean_object* v_head_745_; lean_object* v_tail_746_; lean_object* v___x_747_; 
v_head_745_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_head_745_);
v_tail_746_ = lean_ctor_get(v_x_744_, 1);
lean_inc(v_tail_746_);
lean_dec_ref_known(v_x_744_, 2);
v___x_747_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(v_assignments_742_, v_x_743_, v_head_745_);
lean_dec(v_x_743_);
v_x_743_ = v___x_747_;
v_x_744_ = v_tail_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg___boxed(lean_object* v_assignments_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_749_, v_x_750_, v_x_751_);
lean_dec_ref(v_assignments_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object* v_n_753_, lean_object* v_c_754_, lean_object* v_assignments_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_box(1);
v___x_757_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_755_, v___x_756_, v_c_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed(lean_object* v_n_758_, lean_object* v_c_759_, lean_object* v_assignments_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(v_n_758_, v_c_759_, v_assignments_760_);
lean_dec_ref(v_assignments_760_);
lean_dec(v_n_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(lean_object* v_n_762_, lean_object* v_assignments_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_763_, v_x_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___boxed(lean_object* v_n_767_, lean_object* v_assignments_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(v_n_767_, v_assignments_768_, v_x_769_, v_x_770_);
lean_dec_ref(v_assignments_768_);
lean_dec(v_n_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_instClausePosFin(lean_object* v_n_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_n(v_n_772_, 7);
v___x_773_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed), 2, 1);
lean_closure_set(v___x_773_, 0, v_n_772_);
v___x_774_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed), 2, 1);
lean_closure_set(v___x_774_, 0, v_n_772_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed), 2, 1);
lean_closure_set(v___x_776_, 0, v_n_772_);
v___x_777_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed), 2, 1);
lean_closure_set(v___x_777_, 0, v_n_772_);
v___x_778_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed), 2, 1);
lean_closure_set(v___x_778_, 0, v_n_772_);
v___x_779_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete), 3, 1);
lean_closure_set(v___x_779_, 0, v_n_772_);
v___x_780_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed), 3, 1);
lean_closure_set(v___x_780_, 0, v_n_772_);
v___x_781_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed), 3, 1);
lean_closure_set(v___x_781_, 0, v_n_772_);
v___x_782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_782_, 0, v___x_773_);
lean_ctor_set(v___x_782_, 1, v___x_774_);
lean_ctor_set(v___x_782_, 2, v___x_775_);
lean_ctor_set(v___x_782_, 3, v___x_776_);
lean_ctor_set(v___x_782_, 4, v___x_777_);
lean_ctor_set(v___x_782_, 5, v___x_778_);
lean_ctor_set(v___x_782_, 6, v___x_779_);
lean_ctor_set(v___x_782_, 7, v___x_780_);
lean_ctor_set(v___x_782_, 8, v___x_781_);
return v___x_782_;
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
