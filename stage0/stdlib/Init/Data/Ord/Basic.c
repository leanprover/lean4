// Lean compiler output
// Module: Init.Data.Ord.Basic
// Imports: import Init.ByCases import Init.Ext public import Init.PropLemmas public import Init.Data.Char.Basic import Init.Classical
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instInhabitedOrdering_default;
LEAN_EXPORT uint8_t l_instInhabitedOrdering;
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object*, lean_object*);
static const lean_string_object l_instReprOrdering_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.lt"};
static const lean_object* l_instReprOrdering_repr___closed__0 = (const lean_object*)&l_instReprOrdering_repr___closed__0_value;
static const lean_ctor_object l_instReprOrdering_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprOrdering_repr___closed__0_value)}};
static const lean_object* l_instReprOrdering_repr___closed__1 = (const lean_object*)&l_instReprOrdering_repr___closed__1_value;
static const lean_string_object l_instReprOrdering_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.eq"};
static const lean_object* l_instReprOrdering_repr___closed__2 = (const lean_object*)&l_instReprOrdering_repr___closed__2_value;
static const lean_ctor_object l_instReprOrdering_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprOrdering_repr___closed__2_value)}};
static const lean_object* l_instReprOrdering_repr___closed__3 = (const lean_object*)&l_instReprOrdering_repr___closed__3_value;
static const lean_string_object l_instReprOrdering_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.gt"};
static const lean_object* l_instReprOrdering_repr___closed__4 = (const lean_object*)&l_instReprOrdering_repr___closed__4_value;
static const lean_ctor_object l_instReprOrdering_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprOrdering_repr___closed__4_value)}};
static const lean_object* l_instReprOrdering_repr___closed__5 = (const lean_object*)&l_instReprOrdering_repr___closed__5_value;
static lean_once_cell_t l_instReprOrdering_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprOrdering_repr___closed__6;
static lean_once_cell_t l_instReprOrdering_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprOrdering_repr___closed__7;
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprOrdering___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprOrdering_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprOrdering___closed__0 = (const lean_object*)&l_instReprOrdering___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprOrdering = (const lean_object*)&l_instReprOrdering___closed__0_value;
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_compareOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdNat___closed__0 = (const lean_object*)&l_instOrdNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdNat = (const lean_object*)&l_instOrdNat___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdInt___closed__0 = (const lean_object*)&l_instOrdInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdInt = (const lean_object*)&l_instOrdInt___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdBool___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdBool___closed__0 = (const lean_object*)&l_instOrdBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdBool = (const lean_object*)&l_instOrdBool___closed__0_value;
LEAN_EXPORT lean_object* l_instOrdFin(lean_object*);
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdChar___closed__0 = (const lean_object*)&l_instOrdChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdChar = (const lean_object*)&l_instOrdChar___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdBitVec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdBitVec___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdBitVec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdBitVec___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdBitVec___closed__0 = (const lean_object*)&l_instOrdBitVec___closed__0_value;
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object*);
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instOrdOption(lean_object*, lean_object*);
static const lean_closure_object l_instOrdOrdering___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Ordering_ctorIdx___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdOrdering___closed__0 = (const lean_object*)&l_instOrdOrdering___closed__0_value;
static const lean_closure_object l_instOrdOrdering___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instOrdNat___closed__0_value),((lean_object*)&l_instOrdOrdering___closed__0_value)} };
static const lean_object* l_instOrdOrdering___closed__1 = (const lean_object*)&l_instOrdOrdering___closed__1_value;
LEAN_EXPORT const lean_object* l_instOrdOrdering = (const lean_object*)&l_instOrdOrdering___closed__1_value;
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_compareLex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_lexOrd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_lexOrd___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_lexOrd___redArg___closed__0 = (const lean_object*)&l_lexOrd___redArg___closed__0_value;
static const lean_closure_object l_lexOrd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_lexOrd___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_lexOrd___redArg___closed__1 = (const lean_object*)&l_lexOrd___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_lexOrd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_on(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Ordering_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Ordering_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Ordering_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object* v_lt_23_){
_start:
{
lean_inc(v_lt_23_);
return v_lt_23_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object* v_lt_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Ordering_lt_elim___redArg(v_lt_24_);
lean_dec(v_lt_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_lt_29_){
_start:
{
lean_inc(v_lt_29_);
return v_lt_29_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_lt_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Ordering_lt_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_lt_33_);
lean_dec(v_lt_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object* v_eq_36_){
_start:
{
lean_inc(v_eq_36_);
return v_eq_36_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object* v_eq_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Ordering_eq_elim___redArg(v_eq_37_);
lean_dec(v_eq_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_eq_42_){
_start:
{
lean_inc(v_eq_42_);
return v_eq_42_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_eq_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Ordering_eq_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_eq_46_);
lean_dec(v_eq_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object* v_gt_49_){
_start:
{
lean_inc(v_gt_49_);
return v_gt_49_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object* v_gt_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Ordering_gt_elim___redArg(v_gt_50_);
lean_dec(v_gt_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_gt_55_){
_start:
{
lean_inc(v_gt_55_);
return v_gt_55_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_gt_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Ordering_gt_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_gt_59_);
lean_dec(v_gt_59_);
return v_res_61_;
}
}
static uint8_t _init_l_instInhabitedOrdering_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_instInhabitedOrdering(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_dec_le(v_n_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_dec_le(v_n_64_, v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object* v_n_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Ordering_ofNat(v_n_72_);
lean_dec(v_n_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Ordering_ctorIdx(v_x_75_);
v___x_78_ = l_Ordering_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_x_20__boxed_82_; uint8_t v_y_21__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_20__boxed_82_ = lean_unbox(v_x_80_);
v_y_21__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_instDecidableEqOrdering(v_x_20__boxed_82_, v_y_21__boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__6(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__7(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_to_int(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t v_x_99_, lean_object* v_prec_100_){
_start:
{
lean_object* v___y_102_; lean_object* v___y_109_; lean_object* v___y_116_; 
switch(v_x_99_)
{
case 0:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1024u);
v___x_123_ = lean_nat_dec_le(v___x_122_, v_prec_100_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_102_ = v___x_124_;
goto v___jp_101_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_102_ = v___x_125_;
goto v___jp_101_;
}
}
case 1:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1024u);
v___x_127_ = lean_nat_dec_le(v___x_126_, v_prec_100_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_109_ = v___x_128_;
goto v___jp_108_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_109_ = v___x_129_;
goto v___jp_108_;
}
}
default: 
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = lean_nat_dec_le(v___x_130_, v_prec_100_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_116_ = v___x_132_;
goto v___jp_115_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_116_ = v___x_133_;
goto v___jp_115_;
}
}
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = ((lean_object*)(l_instReprOrdering_repr___closed__1));
lean_inc(v___y_102_);
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = 0;
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
v___x_107_ = l_Repr_addAppParen(v___x_106_, v_prec_100_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = ((lean_object*)(l_instReprOrdering_repr___closed__3));
lean_inc(v___y_109_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_100_);
return v___x_114_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = ((lean_object*)(l_instReprOrdering_repr___closed__5));
lean_inc(v___y_116_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_100_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object* v_x_134_, lean_object* v_prec_135_){
_start:
{
uint8_t v_x_171__boxed_136_; lean_object* v_res_137_; 
v_x_171__boxed_136_ = lean_unbox(v_x_134_);
v_res_137_ = l_instReprOrdering_repr(v_x_171__boxed_136_, v_prec_135_);
lean_dec(v_prec_135_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t v_x_140_){
_start:
{
switch(v_x_140_)
{
case 0:
{
uint8_t v___x_141_; 
v___x_141_ = 2;
return v___x_141_;
}
case 1:
{
return v_x_140_;
}
default: 
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_x_25__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_x_25__boxed_144_ = lean_unbox(v_x_143_);
v_res_145_ = l_Ordering_swap(v_x_25__boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t v_x_147_){
_start:
{
if (v_x_147_ == 1)
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object* v_x_150_){
_start:
{
uint8_t v_x_17__boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_x_17__boxed_151_ = lean_unbox(v_x_150_);
v_res_152_ = l_Ordering_isEq(v_x_17__boxed_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t v_x_154_){
_start:
{
if (v_x_154_ == 1)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 1;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object* v_x_157_){
_start:
{
uint8_t v_x_17__boxed_158_; uint8_t v_res_159_; lean_object* v_r_160_; 
v_x_17__boxed_158_ = lean_unbox(v_x_157_);
v_res_159_ = l_Ordering_isNe(v_x_17__boxed_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t v_x_161_){
_start:
{
if (v_x_161_ == 2)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 1;
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object* v_x_164_){
_start:
{
uint8_t v_x_17__boxed_165_; uint8_t v_res_166_; lean_object* v_r_167_; 
v_x_17__boxed_165_ = lean_unbox(v_x_164_);
v_res_166_ = l_Ordering_isLE(v_x_17__boxed_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t v_x_168_){
_start:
{
if (v_x_168_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object* v_x_171_){
_start:
{
uint8_t v_x_17__boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_x_17__boxed_172_ = lean_unbox(v_x_171_);
v_res_173_ = l_Ordering_isLT(v_x_17__boxed_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t v_x_175_){
_start:
{
if (v_x_175_ == 2)
{
uint8_t v___x_176_; 
v___x_176_ = 1;
return v___x_176_;
}
else
{
uint8_t v___x_177_; 
v___x_177_ = 0;
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object* v_x_178_){
_start:
{
uint8_t v_x_17__boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_x_17__boxed_179_ = lean_unbox(v_x_178_);
v_res_180_ = l_Ordering_isGT(v_x_17__boxed_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t v_x_182_){
_start:
{
if (v_x_182_ == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = 1;
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object* v_x_185_){
_start:
{
uint8_t v_x_17__boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_x_17__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Ordering_isGE(v_x_17__boxed_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_189_){
_start:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_190_ = 0;
v___x_191_ = lean_box(v___x_190_);
lean_inc_ref_n(v_inst_189_, 2);
v___x_192_ = lean_apply_1(v_inst_189_, v___x_191_);
v___x_193_ = 1;
v___x_194_ = lean_box(v___x_193_);
v___x_195_ = lean_apply_1(v_inst_189_, v___x_194_);
v___x_196_ = lean_unbox(v___x_195_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_dec_ref(v_inst_189_);
v___x_197_ = lean_unbox(v___x_192_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = lean_unbox(v___x_192_);
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v___x_195_);
return v___x_199_;
}
}
else
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v___x_192_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
lean_dec_ref(v_inst_189_);
v___x_201_ = lean_unbox(v___x_192_);
return v___x_201_;
}
else
{
uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = 2;
v___x_203_ = lean_box(v___x_202_);
v___x_204_ = lean_apply_1(v_inst_189_, v___x_203_);
v___x_205_ = lean_unbox(v___x_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* v_p_209_, lean_object* v_inst_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_212_, lean_object* v_inst_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_212_, v_inst_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_216_){
_start:
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_217_ = 0;
v___x_218_ = lean_box(v___x_217_);
lean_inc_ref_n(v_inst_216_, 2);
v___x_219_ = lean_apply_1(v_inst_216_, v___x_218_);
v___x_220_ = 1;
v___x_221_ = lean_box(v___x_220_);
v___x_222_ = lean_apply_1(v_inst_216_, v___x_221_);
v___x_223_ = lean_unbox(v___x_222_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v___x_219_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_225_ = 2;
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_apply_1(v_inst_216_, v___x_226_);
v___x_228_ = lean_unbox(v___x_227_);
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
lean_dec_ref(v_inst_216_);
v___x_229_ = lean_unbox(v___x_219_);
return v___x_229_;
}
}
else
{
uint8_t v___x_230_; 
lean_dec_ref(v_inst_216_);
v___x_230_ = lean_unbox(v___x_219_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
v___x_231_ = lean_unbox(v___x_222_);
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = lean_unbox(v___x_219_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_233_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* v_p_236_, lean_object* v_inst_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_239_, lean_object* v_inst_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_239_, v_inst_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (v_a_243_ == 1)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__2_245_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__1_244_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_h__1_244_);
v___x_248_ = lean_box(v_a_243_);
v___x_249_ = lean_apply_2(v_h__2_245_, v___x_248_, lean_box(0));
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
uint8_t v_a_13__boxed_253_; lean_object* v_res_254_; 
v_a_13__boxed_253_ = lean_unbox(v_a_250_);
v_res_254_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_253_, v_h__1_251_, v_h__2_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* v_motive_255_, uint8_t v_a_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (v_a_256_ == 1)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_258_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_1(v_h__1_257_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_257_);
v___x_261_ = lean_box(v_a_256_);
v___x_262_ = lean_apply_2(v_h__2_258_, v___x_261_, lean_box(0));
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_263_, lean_object* v_a_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
uint8_t v_a_24__boxed_267_; lean_object* v_res_268_; 
v_a_24__boxed_267_ = lean_unbox(v_a_264_);
v_res_268_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(v_motive_263_, v_a_24__boxed_267_, v_h__1_265_, v_h__2_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object* v_x_269_, lean_object* v_y_270_, uint8_t v_inst_271_, lean_object* v_inst_272_){
_start:
{
if (v_inst_271_ == 0)
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_apply_2(v_inst_272_, v_x_269_, v_y_270_);
v___x_274_ = lean_unbox(v___x_273_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 2;
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 1;
return v___x_276_;
}
}
else
{
uint8_t v___x_277_; 
lean_dec_ref(v_inst_272_);
lean_dec(v_y_270_);
lean_dec(v_x_269_);
v___x_277_ = 0;
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* v_x_278_, lean_object* v_y_279_, lean_object* v_inst_280_, lean_object* v_inst_281_){
_start:
{
uint8_t v_inst_21__boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_inst_21__boxed_282_ = lean_unbox(v_inst_280_);
v_res_283_ = l_compareOfLessAndEq___redArg(v_x_278_, v_y_279_, v_inst_21__boxed_282_, v_inst_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object* v_00_u03b1_285_, lean_object* v_x_286_, lean_object* v_y_287_, lean_object* v_inst_288_, uint8_t v_inst_289_, lean_object* v_inst_290_){
_start:
{
if (v_inst_289_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_apply_2(v_inst_290_, v_x_286_, v_y_287_);
v___x_292_ = lean_unbox(v___x_291_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; 
v___x_293_ = 2;
return v___x_293_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
}
else
{
uint8_t v___x_295_; 
lean_dec_ref(v_inst_290_);
lean_dec(v_y_287_);
lean_dec(v_x_286_);
v___x_295_ = 0;
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* v_00_u03b1_296_, lean_object* v_x_297_, lean_object* v_y_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_){
_start:
{
uint8_t v_inst_38__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_inst_38__boxed_302_ = lean_unbox(v_inst_300_);
v_res_303_ = l_compareOfLessAndEq(v_00_u03b1_296_, v_x_297_, v_y_298_, v_inst_299_, v_inst_38__boxed_302_, v_inst_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object* v_x_305_, lean_object* v_y_306_, uint8_t v_inst_307_, lean_object* v_inst_308_){
_start:
{
if (v_inst_307_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_apply_2(v_inst_308_, v_x_305_, v_y_306_);
v___x_310_ = lean_unbox(v___x_309_);
if (v___x_310_ == 0)
{
uint8_t v___x_311_; 
v___x_311_ = 2;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
}
else
{
uint8_t v___x_313_; 
lean_dec_ref(v_inst_308_);
lean_dec(v_y_306_);
lean_dec(v_x_305_);
v___x_313_ = 0;
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* v_x_314_, lean_object* v_y_315_, lean_object* v_inst_316_, lean_object* v_inst_317_){
_start:
{
uint8_t v_inst_28__boxed_318_; uint8_t v_res_319_; lean_object* v_r_320_; 
v_inst_28__boxed_318_ = lean_unbox(v_inst_316_);
v_res_319_ = l_compareOfLessAndBEq___redArg(v_x_314_, v_y_315_, v_inst_28__boxed_318_, v_inst_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object* v_00_u03b1_321_, lean_object* v_x_322_, lean_object* v_y_323_, lean_object* v_inst_324_, uint8_t v_inst_325_, lean_object* v_inst_326_){
_start:
{
if (v_inst_325_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_apply_2(v_inst_326_, v_x_322_, v_y_323_);
v___x_328_ = lean_unbox(v___x_327_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = 2;
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 1;
return v___x_330_;
}
}
else
{
uint8_t v___x_331_; 
lean_dec_ref(v_inst_326_);
lean_dec(v_y_323_);
lean_dec(v_x_322_);
v___x_331_ = 0;
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* v_00_u03b1_332_, lean_object* v_x_333_, lean_object* v_y_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_){
_start:
{
uint8_t v_inst_45__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_inst_45__boxed_338_ = lean_unbox(v_inst_336_);
v_res_339_ = l_compareOfLessAndBEq(v_00_u03b1_332_, v_x_333_, v_y_334_, v_inst_335_, v_inst_45__boxed_338_, v_inst_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object* v_cmp_u2081_341_, lean_object* v_cmp_u2082_342_, lean_object* v_a_343_, lean_object* v_b_344_){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
lean_inc(v_b_344_);
lean_inc(v_a_343_);
v___x_345_ = lean_apply_2(v_cmp_u2081_341_, v_a_343_, v_b_344_);
v___x_346_ = lean_unbox(v___x_345_);
if (v___x_346_ == 1)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_apply_2(v_cmp_u2082_342_, v_a_343_, v_b_344_);
v___x_348_ = lean_unbox(v___x_347_);
return v___x_348_;
}
else
{
uint8_t v___x_349_; 
lean_dec(v_b_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_cmp_u2082_342_);
v___x_349_ = lean_unbox(v___x_345_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* v_cmp_u2081_350_, lean_object* v_cmp_u2082_351_, lean_object* v_a_352_, lean_object* v_b_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_compareLex___redArg(v_cmp_u2081_350_, v_cmp_u2082_351_, v_a_352_, v_b_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT uint8_t l_compareLex(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_cmp_u2081_358_, lean_object* v_cmp_u2082_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
lean_inc(v_b_361_);
lean_inc(v_a_360_);
v___x_362_ = lean_apply_2(v_cmp_u2081_358_, v_a_360_, v_b_361_);
v___x_363_ = lean_unbox(v___x_362_);
if (v___x_363_ == 1)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = lean_apply_2(v_cmp_u2082_359_, v_a_360_, v_b_361_);
v___x_365_ = lean_unbox(v___x_364_);
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
lean_dec(v_b_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_cmp_u2082_359_);
v___x_366_ = lean_unbox(v___x_362_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_cmp_u2081_369_, lean_object* v_cmp_u2082_370_, lean_object* v_a_371_, lean_object* v_b_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_compareLex(v_00_u03b1_367_, v_00_u03b2_368_, v_cmp_u2081_369_, v_cmp_u2082_370_, v_a_371_, v_b_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object* v_ord_375_, lean_object* v_f_376_, lean_object* v_x_377_, lean_object* v_y_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
lean_inc(v_f_376_);
v___x_379_ = lean_apply_1(v_f_376_, v_x_377_);
v___x_380_ = lean_apply_1(v_f_376_, v_y_378_);
v___x_381_ = lean_apply_2(v_ord_375_, v___x_379_, v___x_380_);
v___x_382_ = lean_unbox(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* v_ord_383_, lean_object* v_f_384_, lean_object* v_x_385_, lean_object* v_y_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_compareOn___redArg(v_ord_383_, v_f_384_, v_x_385_, v_y_386_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_compareOn(lean_object* v_00_u03b2_389_, lean_object* v_00_u03b1_390_, lean_object* v_ord_391_, lean_object* v_f_392_, lean_object* v_x_393_, lean_object* v_y_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
lean_inc(v_f_392_);
v___x_395_ = lean_apply_1(v_f_392_, v_x_393_);
v___x_396_ = lean_apply_1(v_f_392_, v_y_394_);
v___x_397_ = lean_apply_2(v_ord_391_, v___x_395_, v___x_396_);
v___x_398_ = lean_unbox(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* v_00_u03b2_399_, lean_object* v_00_u03b1_400_, lean_object* v_ord_401_, lean_object* v_f_402_, lean_object* v_x_403_, lean_object* v_y_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_compareOn(v_00_u03b2_399_, v_00_u03b1_400_, v_ord_401_, v_f_402_, v_x_403_, v_y_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object* v_x_407_, lean_object* v_y_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_lt(v_x_407_, v_y_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_eq(v_x_407_, v_y_408_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 2;
return v___x_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 1;
return v___x_412_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* v_x_414_, lean_object* v_y_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_instOrdNat___lam__0(v_x_414_, v_y_415_);
lean_dec(v_y_415_);
lean_dec(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object* v_x_420_, lean_object* v_y_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_int_dec_lt(v_x_420_, v_y_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_int_dec_eq(v_x_420_, v_y_421_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 2;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 1;
return v___x_425_;
}
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* v_x_427_, lean_object* v_y_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_instOrdInt___lam__0(v_x_427_, v_y_428_);
lean_dec(v_y_428_);
lean_dec(v_x_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t v_x_433_, uint8_t v_x_434_){
_start:
{
if (v_x_433_ == 0)
{
if (v_x_434_ == 1)
{
uint8_t v___x_435_; 
v___x_435_ = 0;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 1;
return v___x_436_;
}
}
else
{
if (v_x_434_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = 2;
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 1;
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_x_39__boxed_441_; uint8_t v_x_40__boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_x_39__boxed_441_ = lean_unbox(v_x_439_);
v_x_40__boxed_442_ = lean_unbox(v_x_440_);
v_res_443_ = l_instOrdBool___lam__0(v_x_39__boxed_441_, v_x_40__boxed_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* v_n_447_){
_start:
{
lean_object* v___f_448_; 
v___f_448_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_448_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* v_n_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_instOrdFin(v_n_449_);
lean_dec(v_n_449_);
return v_res_450_;
}
}
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t v_x_451_, uint32_t v_y_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_uint32_dec_lt(v_x_451_, v_y_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = lean_uint32_dec_eq(v_x_451_, v_y_452_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 2;
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 1;
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* v_x_458_, lean_object* v_y_459_){
_start:
{
uint32_t v_x_boxed_460_; uint32_t v_y_boxed_461_; uint8_t v_res_462_; lean_object* v_r_463_; 
v_x_boxed_460_ = lean_unbox_uint32(v_x_458_);
lean_dec(v_x_458_);
v_y_boxed_461_ = lean_unbox_uint32(v_y_459_);
lean_dec(v_y_459_);
v_res_462_ = l_instOrdChar___lam__0(v_x_boxed_460_, v_y_boxed_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint8_t l_instOrdBitVec___lam__0(lean_object* v_x_466_, lean_object* v_y_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_x_466_, v___x_468_);
v___x_470_ = lean_nat_dec_le(v___x_469_, v_y_467_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = lean_nat_dec_eq(v_x_466_, v_y_467_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = 2;
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = 1;
return v___x_473_;
}
}
else
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___lam__0___boxed(lean_object* v_x_475_, lean_object* v_y_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_instOrdBitVec___lam__0(v_x_475_, v_y_476_);
lean_dec(v_y_476_);
lean_dec(v_x_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_480_){
_start:
{
lean_object* v___f_481_; 
v___f_481_ = ((lean_object*)(l_instOrdBitVec___closed__0));
return v___f_481_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_instOrdBitVec(v_n_482_);
lean_dec(v_n_482_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_dec_ref(v_inst_484_);
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 1;
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
lean_dec_ref_known(v_x_486_, 1);
v___x_488_ = 0;
return v___x_488_;
}
}
else
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_489_; 
lean_dec_ref_known(v_x_485_, 1);
lean_dec_ref(v_inst_484_);
v___x_489_ = 2;
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v_val_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_val_490_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v_x_485_, 1);
v_val_491_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v_x_486_, 1);
v___x_492_ = lean_apply_2(v_inst_484_, v_val_490_, v_val_491_);
v___x_493_ = lean_unbox(v___x_492_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_instOrdOption___redArg___lam__0(v_inst_494_, v_x_495_, v_x_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_499_){
_start:
{
lean_object* v___f_500_; 
v___f_500_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v_inst_499_);
return v___f_500_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_503_, 0, v_inst_502_);
return v___f_503_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* v_cmp_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_dec_ref(v_cmp_509_);
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 1;
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
lean_dec(v_x_511_);
v___x_513_ = 0;
return v___x_513_;
}
}
else
{
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_514_; 
lean_dec_ref_known(v_x_510_, 2);
lean_dec_ref(v_cmp_509_);
v___x_514_ = 2;
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v_head_517_; lean_object* v_tail_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_head_515_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_head_515_);
v_tail_516_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_x_510_, 2);
v_head_517_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_head_517_);
v_tail_518_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_tail_518_);
lean_dec_ref_known(v_x_511_, 2);
lean_inc_ref(v_cmp_509_);
v___x_519_ = lean_apply_2(v_cmp_509_, v_head_515_, v_head_517_);
v___x_520_ = lean_unbox(v___x_519_);
if (v___x_520_ == 1)
{
v_x_510_ = v_tail_516_;
v_x_511_ = v_tail_518_;
goto _start;
}
else
{
uint8_t v___x_522_; 
lean_dec(v_tail_518_);
lean_dec(v_tail_516_);
lean_dec_ref(v_cmp_509_);
v___x_522_ = lean_unbox(v___x_519_);
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
uint8_t v_res_526_; lean_object* v_r_527_; 
v_res_526_ = l_List_compareLex___redArg(v_cmp_523_, v_x_524_, v_x_525_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* v_00_u03b1_528_, lean_object* v_cmp_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = l_List_compareLex___redArg(v_cmp_529_, v_x_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_List_compareLex(v_00_u03b1_533_, v_cmp_534_, v_x_535_, v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_540_, 0, lean_box(0));
lean_closure_set(v___x_540_, 1, v_inst_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_541_, lean_object* v_inst_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_543_, 0, lean_box(0));
lean_closure_set(v___x_543_, 1, v_inst_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_, lean_object* v_h__3_548_, lean_object* v_h__4_549_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_dec(v_h__4_549_);
lean_dec(v_h__3_548_);
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_547_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_apply_1(v_h__1_546_, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_h__1_546_);
v___x_552_ = lean_apply_2(v_h__2_547_, v_x_545_, lean_box(0));
return v___x_552_;
}
}
else
{
lean_dec(v_h__2_547_);
lean_dec(v_h__1_546_);
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_553_; 
lean_dec(v_h__4_549_);
v___x_553_ = lean_apply_2(v_h__3_548_, v_x_544_, lean_box(0));
return v___x_553_;
}
else
{
lean_object* v_head_554_; lean_object* v_tail_555_; lean_object* v_head_556_; lean_object* v_tail_557_; lean_object* v___x_558_; 
lean_dec(v_h__3_548_);
v_head_554_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_head_554_);
v_tail_555_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_tail_555_);
lean_dec_ref_known(v_x_544_, 2);
v_head_556_ = lean_ctor_get(v_x_545_, 0);
lean_inc(v_head_556_);
v_tail_557_ = lean_ctor_get(v_x_545_, 1);
lean_inc(v_tail_557_);
lean_dec_ref_known(v_x_545_, 2);
v___x_558_ = lean_apply_4(v_h__4_549_, v_head_554_, v_tail_555_, v_head_556_, v_tail_557_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_559_, lean_object* v_motive_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_, lean_object* v_h__3_565_, lean_object* v_h__4_566_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_dec(v_h__4_566_);
lean_dec(v_h__3_565_);
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_h__2_564_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_apply_1(v_h__1_563_, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
lean_dec(v_h__1_563_);
v___x_569_ = lean_apply_2(v_h__2_564_, v_x_562_, lean_box(0));
return v___x_569_;
}
}
else
{
lean_dec(v_h__2_564_);
lean_dec(v_h__1_563_);
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v___x_570_; 
lean_dec(v_h__4_566_);
v___x_570_ = lean_apply_2(v_h__3_565_, v_x_561_, lean_box(0));
return v___x_570_;
}
else
{
lean_object* v_head_571_; lean_object* v_tail_572_; lean_object* v_head_573_; lean_object* v_tail_574_; lean_object* v___x_575_; 
lean_dec(v_h__3_565_);
v_head_571_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_head_571_);
v_tail_572_ = lean_ctor_get(v_x_561_, 1);
lean_inc(v_tail_572_);
lean_dec_ref_known(v_x_561_, 2);
v_head_573_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_head_573_);
v_tail_574_ = lean_ctor_get(v_x_562_, 1);
lean_inc(v_tail_574_);
lean_dec_ref_known(v_x_562_, 2);
v___x_575_ = lean_apply_4(v_h__4_566_, v_head_571_, v_tail_572_, v_head_573_, v_tail_574_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_, lean_object* v_h__3_579_){
_start:
{
switch(v_x_576_)
{
case 0:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_h__3_579_);
lean_dec(v_h__2_578_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_h__1_577_, v___x_580_);
return v___x_581_;
}
case 1:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_h__3_579_);
lean_dec(v_h__1_577_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_apply_1(v_h__2_578_, v___x_582_);
return v___x_583_;
}
default: 
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_h__2_578_);
lean_dec(v_h__1_577_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_apply_1(v_h__3_579_, v___x_584_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_, lean_object* v_h__3_589_){
_start:
{
uint8_t v_x_33__boxed_590_; lean_object* v_res_591_; 
v_x_33__boxed_590_ = lean_unbox(v_x_586_);
v_res_591_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_590_, v_h__1_587_, v_h__2_588_, v_h__3_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_592_, uint8_t v_x_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_, lean_object* v_h__3_596_){
_start:
{
switch(v_x_593_)
{
case 0:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_h__3_596_);
lean_dec(v_h__2_595_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_apply_1(v_h__1_594_, v___x_597_);
return v___x_598_;
}
case 1:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_h__3_596_);
lean_dec(v_h__1_594_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_apply_1(v_h__2_595_, v___x_599_);
return v___x_600_;
}
default: 
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_h__2_595_);
lean_dec(v_h__1_594_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_apply_1(v_h__3_596_, v___x_601_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_, lean_object* v_h__3_607_){
_start:
{
uint8_t v_x_48__boxed_608_; lean_object* v_res_609_; 
v_x_48__boxed_608_ = lean_unbox(v_x_604_);
v_res_609_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_603_, v_x_48__boxed_608_, v_h__1_605_, v_h__2_606_, v_h__3_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_610_){
_start:
{
lean_object* v_fst_611_; 
v_fst_611_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_fst_611_);
return v_fst_611_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_lexOrd___redArg___lam__0(v_x_612_);
lean_dec_ref(v_x_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_614_){
_start:
{
lean_object* v_snd_615_; 
v_snd_615_ = lean_ctor_get(v_x_614_, 1);
lean_inc(v_snd_615_);
return v_snd_615_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_lexOrd___redArg___lam__1(v_x_616_);
lean_dec_ref(v_x_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_620_, lean_object* v_inst_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___f_622_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_623_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_624_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_624_, 0, lean_box(0));
lean_closure_set(v___x_624_, 1, lean_box(0));
lean_closure_set(v___x_624_, 2, v_inst_620_);
lean_closure_set(v___x_624_, 3, v___f_622_);
v___x_625_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_625_, 0, lean_box(0));
lean_closure_set(v___x_625_, 1, lean_box(0));
lean_closure_set(v___x_625_, 2, v_inst_621_);
lean_closure_set(v___x_625_, 3, v___f_623_);
v___x_626_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_626_, 0, lean_box(0));
lean_closure_set(v___x_626_, 1, lean_box(0));
lean_closure_set(v___x_626_, 2, v___x_624_);
lean_closure_set(v___x_626_, 3, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_inst_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_lexOrd___redArg(v_inst_629_, v_inst_630_);
return v___x_631_;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_632_, lean_object* v_a_633_, lean_object* v_b_634_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_apply_2(v_inst_632_, v_a_633_, v_b_634_);
v___x_636_ = lean_unbox(v___x_635_);
if (v___x_636_ == 1)
{
uint8_t v___x_637_; 
v___x_637_ = 1;
return v___x_637_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = 0;
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_639_, lean_object* v_a_640_, lean_object* v_b_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_beqOfOrd___redArg___lam__0(v_inst_639_, v_a_640_, v_b_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_644_){
_start:
{
lean_object* v___f_645_; 
v___f_645_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_645_, 0, v_inst_644_);
return v___f_645_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v___f_648_; 
v___f_648_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_648_, 0, v_inst_647_);
return v___f_648_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(0);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_652_, lean_object* v_inst_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_ltOfOrd(v_00_u03b1_652_, v_inst_653_);
lean_dec_ref(v_inst_653_);
return v_res_654_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_apply_2(v_inst_655_, v_a_656_, v_b_657_);
v___x_659_ = lean_unbox(v___x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 1;
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_662_, lean_object* v_a_663_, lean_object* v_b_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_instDecidableRelLt___redArg(v_inst_662_, v_a_663_, v_b_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_667_, lean_object* v_inst_668_, lean_object* v_a_669_, lean_object* v_b_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_apply_2(v_inst_668_, v_a_669_, v_b_670_);
v___x_672_ = lean_unbox(v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = 1;
return v___x_673_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_675_, lean_object* v_inst_676_, lean_object* v_a_677_, lean_object* v_b_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_instDecidableRelLt(v_00_u03b1_675_, v_inst_676_, v_a_677_, v_b_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_684_, lean_object* v_inst_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_leOfOrd(v_00_u03b1_684_, v_inst_685_);
lean_dec_ref(v_inst_685_);
return v_res_686_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_apply_2(v_inst_687_, v_x_688_, v_x_689_);
v___x_691_ = lean_unbox(v___x_690_);
if (v___x_691_ == 2)
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 1;
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_instDecidableRelLe___redArg(v_inst_694_, v_x_695_, v_x_696_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_699_, lean_object* v_inst_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_apply_2(v_inst_700_, v_x_701_, v_x_702_);
v___x_704_ = lean_unbox(v___x_703_);
if (v___x_704_ == 2)
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = 1;
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_707_, lean_object* v_inst_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_instDecidableRelLe(v_00_u03b1_707_, v_inst_708_, v_x_709_, v_x_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_713_){
_start:
{
lean_object* v___f_714_; 
v___f_714_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_714_, 0, v_ord_713_);
return v___f_714_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_715_, lean_object* v_ord_716_){
_start:
{
lean_object* v___f_717_; 
v___f_717_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_717_, 0, v_ord_716_);
return v___f_717_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_718_, lean_object* v_ord_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(0);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_721_, lean_object* v_ord_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Ord_toLT(v_00_u03b1_721_, v_ord_722_);
lean_dec_ref(v_ord_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_724_, lean_object* v_ord_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_727_, lean_object* v_ord_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Ord_toLE(v_00_u03b1_727_, v_ord_728_);
lean_dec_ref(v_ord_728_);
return v_res_729_;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_730_, lean_object* v_x_731_, lean_object* v_y_732_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_apply_2(v_ord_730_, v_y_732_, v_x_731_);
v___x_734_ = lean_unbox(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_735_, lean_object* v_x_736_, lean_object* v_y_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_Ord_opposite___redArg___lam__0(v_ord_735_, v_x_736_, v_y_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_740_){
_start:
{
lean_object* v___f_741_; 
v___f_741_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_741_, 0, v_ord_740_);
return v___f_741_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_742_, lean_object* v_ord_743_){
_start:
{
lean_object* v___f_744_; 
v___f_744_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_744_, 0, v_ord_743_);
return v___f_744_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_745_, lean_object* v_f_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_747_, 0, lean_box(0));
lean_closure_set(v___x_747_, 1, lean_box(0));
lean_closure_set(v___x_747_, 2, v_x_745_);
lean_closure_set(v___x_747_, 3, v_f_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_748_, lean_object* v_00_u03b1_749_, lean_object* v_x_750_, lean_object* v_f_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_752_, 0, lean_box(0));
lean_closure_set(v___x_752_, 1, lean_box(0));
lean_closure_set(v___x_752_, 2, v_x_750_);
lean_closure_set(v___x_752_, 3, v_f_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_lexOrd___redArg(v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_lexOrd___redArg(v_x_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_761_, lean_object* v_ord_u2082_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_763_, 0, lean_box(0));
lean_closure_set(v___x_763_, 1, lean_box(0));
lean_closure_set(v___x_763_, 2, v_ord_u2081_761_);
lean_closure_set(v___x_763_, 3, v_ord_u2082_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_764_, lean_object* v_ord_u2081_765_, lean_object* v_ord_u2082_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_767_, 0, lean_box(0));
lean_closure_set(v___x_767_, 1, lean_box(0));
lean_closure_set(v___x_767_, 2, v_ord_u2081_765_);
lean_closure_set(v___x_767_, 3, v_ord_u2082_766_);
return v___x_767_;
}
}
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedOrdering_default = _init_l_instInhabitedOrdering_default();
l_instInhabitedOrdering = _init_l_instInhabitedOrdering();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
