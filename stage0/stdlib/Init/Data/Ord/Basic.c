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
uint8_t l_instDecidableLtBitVec___aux__1___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Ordering_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Ordering_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Ordering_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Ordering_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Ordering_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object* v_lt_28_){
_start:
{
lean_inc(v_lt_28_);
return v_lt_28_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object* v_lt_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Ordering_lt_elim___redArg(v_lt_29_);
lean_dec(v_lt_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_lt_34_){
_start:
{
lean_inc(v_lt_34_);
return v_lt_34_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_lt_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Ordering_lt_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_lt_38_);
lean_dec(v_lt_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object* v_eq_41_){
_start:
{
lean_inc(v_eq_41_);
return v_eq_41_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object* v_eq_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Ordering_eq_elim___redArg(v_eq_42_);
lean_dec(v_eq_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_eq_47_){
_start:
{
lean_inc(v_eq_47_);
return v_eq_47_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_eq_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Ordering_eq_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_eq_51_);
lean_dec(v_eq_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object* v_gt_54_){
_start:
{
lean_inc(v_gt_54_);
return v_gt_54_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object* v_gt_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Ordering_gt_elim___redArg(v_gt_55_);
lean_dec(v_gt_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_gt_60_){
_start:
{
lean_inc(v_gt_60_);
return v_gt_60_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_gt_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Ordering_gt_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_gt_64_);
lean_dec(v_gt_64_);
return v_res_66_;
}
}
static uint8_t _init_l_instInhabitedOrdering_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_instInhabitedOrdering(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Ordering_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Ordering_ctorIdx(v_x_80_);
v___x_83_ = l_Ordering_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_instDecidableEqOrdering(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__6(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v___y_107_; lean_object* v___y_114_; lean_object* v___y_121_; 
switch(v_x_104_)
{
case 0:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_105_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_107_ = v___x_129_;
goto v___jp_106_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_107_ = v___x_130_;
goto v___jp_106_;
}
}
case 1:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_105_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_114_ = v___x_133_;
goto v___jp_113_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_114_ = v___x_134_;
goto v___jp_113_;
}
}
default: 
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_105_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_121_ = v___x_137_;
goto v___jp_120_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_121_ = v___x_138_;
goto v___jp_120_;
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_instReprOrdering_repr___closed__1));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_105_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_instReprOrdering_repr___closed__3));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_105_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_instReprOrdering_repr___closed__5));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_105_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object* v_x_139_, lean_object* v_prec_140_){
_start:
{
uint8_t v_x_177__boxed_141_; lean_object* v_res_142_; 
v_x_177__boxed_141_ = lean_unbox(v_x_139_);
v_res_142_ = l_instReprOrdering_repr(v_x_177__boxed_141_, v_prec_140_);
lean_dec(v_prec_140_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
uint8_t v___x_146_; 
v___x_146_ = 2;
return v___x_146_;
}
case 1:
{
return v_x_145_;
}
default: 
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object* v_x_148_){
_start:
{
uint8_t v_x_25__boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_x_25__boxed_149_ = lean_unbox(v_x_148_);
v_res_150_ = l_Ordering_swap(v_x_25__boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t v_x_152_){
_start:
{
if (v_x_152_ == 1)
{
uint8_t v___x_153_; 
v___x_153_ = 1;
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object* v_x_155_){
_start:
{
uint8_t v_x_21__boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_x_21__boxed_156_ = lean_unbox(v_x_155_);
v_res_157_ = l_Ordering_isEq(v_x_21__boxed_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t v_x_159_){
_start:
{
if (v_x_159_ == 1)
{
uint8_t v___x_160_; 
v___x_160_ = 0;
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object* v_x_162_){
_start:
{
uint8_t v_x_21__boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_x_21__boxed_163_ = lean_unbox(v_x_162_);
v_res_164_ = l_Ordering_isNe(v_x_21__boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t v_x_166_){
_start:
{
if (v_x_166_ == 2)
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 1;
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object* v_x_169_){
_start:
{
uint8_t v_x_21__boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_x_21__boxed_170_ = lean_unbox(v_x_169_);
v_res_171_ = l_Ordering_isLE(v_x_21__boxed_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t v_x_173_){
_start:
{
if (v_x_173_ == 0)
{
uint8_t v___x_174_; 
v___x_174_ = 1;
return v___x_174_;
}
else
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object* v_x_176_){
_start:
{
uint8_t v_x_21__boxed_177_; uint8_t v_res_178_; lean_object* v_r_179_; 
v_x_21__boxed_177_ = lean_unbox(v_x_176_);
v_res_178_ = l_Ordering_isLT(v_x_21__boxed_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t v_x_180_){
_start:
{
if (v_x_180_ == 2)
{
uint8_t v___x_181_; 
v___x_181_ = 1;
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object* v_x_183_){
_start:
{
uint8_t v_x_21__boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_x_21__boxed_184_ = lean_unbox(v_x_183_);
v_res_185_ = l_Ordering_isGT(v_x_21__boxed_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t v_x_187_){
_start:
{
if (v_x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 1;
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object* v_x_190_){
_start:
{
uint8_t v_x_21__boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_x_21__boxed_191_ = lean_unbox(v_x_190_);
v_res_192_ = l_Ordering_isGE(v_x_21__boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_194_){
_start:
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = 0;
v___x_196_ = lean_box(v___x_195_);
lean_inc_ref(v_inst_194_);
v___x_197_ = lean_apply_1(v_inst_194_, v___x_196_);
v___x_198_ = lean_unbox(v___x_197_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; 
lean_dec_ref(v_inst_194_);
v___x_199_ = lean_unbox(v___x_197_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_200_ = 1;
v___x_201_ = lean_box(v___x_200_);
lean_inc_ref(v_inst_194_);
v___x_202_ = lean_apply_1(v_inst_194_, v___x_201_);
v___x_203_ = lean_unbox(v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
lean_dec_ref(v_inst_194_);
v___x_204_ = lean_unbox(v___x_202_);
return v___x_204_;
}
else
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_205_ = 2;
v___x_206_ = lean_box(v___x_205_);
v___x_207_ = lean_apply_1(v_inst_194_, v___x_206_);
v___x_208_ = lean_unbox(v___x_207_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* v_p_212_, lean_object* v_inst_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_215_, lean_object* v_inst_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_215_, v_inst_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_219_){
_start:
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = 0;
v___x_221_ = lean_box(v___x_220_);
lean_inc_ref(v_inst_219_);
v___x_222_ = lean_apply_1(v_inst_219_, v___x_221_);
v___x_223_ = lean_unbox(v___x_222_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = 1;
v___x_225_ = lean_box(v___x_224_);
lean_inc_ref(v_inst_219_);
v___x_226_ = lean_apply_1(v_inst_219_, v___x_225_);
v___x_227_ = lean_unbox(v___x_226_);
if (v___x_227_ == 0)
{
uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_228_ = 2;
v___x_229_ = lean_box(v___x_228_);
v___x_230_ = lean_apply_1(v_inst_219_, v___x_229_);
v___x_231_ = lean_unbox(v___x_230_);
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
lean_dec_ref(v_inst_219_);
v___x_232_ = lean_unbox(v___x_226_);
return v___x_232_;
}
}
else
{
uint8_t v___x_233_; 
lean_dec_ref(v_inst_219_);
v___x_233_ = lean_unbox(v___x_222_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_234_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* v_p_237_, lean_object* v_inst_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_240_, lean_object* v_inst_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_240_, v_inst_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_){
_start:
{
if (v_a_244_ == 1)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_h__2_246_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_h__1_245_, v___x_247_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_h__1_245_);
v___x_249_ = lean_box(v_a_244_);
v___x_250_ = lean_apply_2(v_h__2_246_, v___x_249_, lean_box(0));
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_251_, lean_object* v_h__1_252_, lean_object* v_h__2_253_){
_start:
{
uint8_t v_a_17__boxed_254_; lean_object* v_res_255_; 
v_a_17__boxed_254_ = lean_unbox(v_a_251_);
v_res_255_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_17__boxed_254_, v_h__1_252_, v_h__2_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* v_motive_256_, uint8_t v_a_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_){
_start:
{
if (v_a_257_ == 1)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_h__2_259_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_1(v_h__1_258_, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_258_);
v___x_262_ = lean_box(v_a_257_);
v___x_263_ = lean_apply_2(v_h__2_259_, v___x_262_, lean_box(0));
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_264_, lean_object* v_a_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
uint8_t v_a_28__boxed_268_; lean_object* v_res_269_; 
v_a_28__boxed_268_ = lean_unbox(v_a_265_);
v_res_269_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(v_motive_264_, v_a_28__boxed_268_, v_h__1_266_, v_h__2_267_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object* v_x_270_, lean_object* v_y_271_, uint8_t v_inst_272_, lean_object* v_inst_273_){
_start:
{
if (v_inst_272_ == 0)
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_apply_2(v_inst_273_, v_x_270_, v_y_271_);
v___x_275_ = lean_unbox(v___x_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 2;
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 1;
return v___x_277_;
}
}
else
{
uint8_t v___x_278_; 
lean_dec_ref(v_inst_273_);
lean_dec(v_y_271_);
lean_dec(v_x_270_);
v___x_278_ = 0;
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* v_x_279_, lean_object* v_y_280_, lean_object* v_inst_281_, lean_object* v_inst_282_){
_start:
{
uint8_t v_inst_23__boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_inst_23__boxed_283_ = lean_unbox(v_inst_281_);
v_res_284_ = l_compareOfLessAndEq___redArg(v_x_279_, v_y_280_, v_inst_23__boxed_283_, v_inst_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object* v_00_u03b1_286_, lean_object* v_x_287_, lean_object* v_y_288_, lean_object* v_inst_289_, uint8_t v_inst_290_, lean_object* v_inst_291_){
_start:
{
if (v_inst_290_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_apply_2(v_inst_291_, v_x_287_, v_y_288_);
v___x_293_ = lean_unbox(v___x_292_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 2;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 1;
return v___x_295_;
}
}
else
{
uint8_t v___x_296_; 
lean_dec_ref(v_inst_291_);
lean_dec(v_y_288_);
lean_dec(v_x_287_);
v___x_296_ = 0;
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* v_00_u03b1_297_, lean_object* v_x_298_, lean_object* v_y_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_){
_start:
{
uint8_t v_inst_40__boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_inst_40__boxed_303_ = lean_unbox(v_inst_301_);
v_res_304_ = l_compareOfLessAndEq(v_00_u03b1_297_, v_x_298_, v_y_299_, v_inst_300_, v_inst_40__boxed_303_, v_inst_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object* v_x_306_, lean_object* v_y_307_, uint8_t v_inst_308_, lean_object* v_inst_309_){
_start:
{
if (v_inst_308_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_apply_2(v_inst_309_, v_x_306_, v_y_307_);
v___x_311_ = lean_unbox(v___x_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 2;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 1;
return v___x_313_;
}
}
else
{
uint8_t v___x_314_; 
lean_dec_ref(v_inst_309_);
lean_dec(v_y_307_);
lean_dec(v_x_306_);
v___x_314_ = 0;
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* v_x_315_, lean_object* v_y_316_, lean_object* v_inst_317_, lean_object* v_inst_318_){
_start:
{
uint8_t v_inst_42__boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_inst_42__boxed_319_ = lean_unbox(v_inst_317_);
v_res_320_ = l_compareOfLessAndBEq___redArg(v_x_315_, v_y_316_, v_inst_42__boxed_319_, v_inst_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object* v_00_u03b1_322_, lean_object* v_x_323_, lean_object* v_y_324_, lean_object* v_inst_325_, uint8_t v_inst_326_, lean_object* v_inst_327_){
_start:
{
if (v_inst_326_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_apply_2(v_inst_327_, v_x_323_, v_y_324_);
v___x_329_ = lean_unbox(v___x_328_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; 
v___x_330_ = 2;
return v___x_330_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
}
else
{
uint8_t v___x_332_; 
lean_dec_ref(v_inst_327_);
lean_dec(v_y_324_);
lean_dec(v_x_323_);
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* v_00_u03b1_333_, lean_object* v_x_334_, lean_object* v_y_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_){
_start:
{
uint8_t v_inst_59__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_inst_59__boxed_339_ = lean_unbox(v_inst_337_);
v_res_340_ = l_compareOfLessAndBEq(v_00_u03b1_333_, v_x_334_, v_y_335_, v_inst_336_, v_inst_59__boxed_339_, v_inst_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object* v_cmp_u2081_342_, lean_object* v_cmp_u2082_343_, lean_object* v_a_344_, lean_object* v_b_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
lean_inc(v_b_345_);
lean_inc(v_a_344_);
v___x_346_ = lean_apply_2(v_cmp_u2081_342_, v_a_344_, v_b_345_);
v___x_347_ = lean_unbox(v___x_346_);
if (v___x_347_ == 1)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_apply_2(v_cmp_u2082_343_, v_a_344_, v_b_345_);
v___x_349_ = lean_unbox(v___x_348_);
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
lean_dec(v_b_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_cmp_u2082_343_);
v___x_350_ = lean_unbox(v___x_346_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* v_cmp_u2081_351_, lean_object* v_cmp_u2082_352_, lean_object* v_a_353_, lean_object* v_b_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_compareLex___redArg(v_cmp_u2081_351_, v_cmp_u2082_352_, v_a_353_, v_b_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_compareLex(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_cmp_u2081_359_, lean_object* v_cmp_u2082_360_, lean_object* v_a_361_, lean_object* v_b_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
lean_inc(v_b_362_);
lean_inc(v_a_361_);
v___x_363_ = lean_apply_2(v_cmp_u2081_359_, v_a_361_, v_b_362_);
v___x_364_ = lean_unbox(v___x_363_);
if (v___x_364_ == 1)
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_apply_2(v_cmp_u2082_360_, v_a_361_, v_b_362_);
v___x_366_ = lean_unbox(v___x_365_);
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
lean_dec(v_b_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_cmp_u2082_360_);
v___x_367_ = lean_unbox(v___x_363_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_cmp_u2081_370_, lean_object* v_cmp_u2082_371_, lean_object* v_a_372_, lean_object* v_b_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_compareLex(v_00_u03b1_368_, v_00_u03b2_369_, v_cmp_u2081_370_, v_cmp_u2082_371_, v_a_372_, v_b_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object* v_ord_376_, lean_object* v_f_377_, lean_object* v_x_378_, lean_object* v_y_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
lean_inc(v_f_377_);
v___x_380_ = lean_apply_1(v_f_377_, v_x_378_);
v___x_381_ = lean_apply_1(v_f_377_, v_y_379_);
v___x_382_ = lean_apply_2(v_ord_376_, v___x_380_, v___x_381_);
v___x_383_ = lean_unbox(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* v_ord_384_, lean_object* v_f_385_, lean_object* v_x_386_, lean_object* v_y_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_compareOn___redArg(v_ord_384_, v_f_385_, v_x_386_, v_y_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_compareOn(lean_object* v_00_u03b2_390_, lean_object* v_00_u03b1_391_, lean_object* v_ord_392_, lean_object* v_f_393_, lean_object* v_x_394_, lean_object* v_y_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
lean_inc(v_f_393_);
v___x_396_ = lean_apply_1(v_f_393_, v_x_394_);
v___x_397_ = lean_apply_1(v_f_393_, v_y_395_);
v___x_398_ = lean_apply_2(v_ord_392_, v___x_396_, v___x_397_);
v___x_399_ = lean_unbox(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* v_00_u03b2_400_, lean_object* v_00_u03b1_401_, lean_object* v_ord_402_, lean_object* v_f_403_, lean_object* v_x_404_, lean_object* v_y_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_compareOn(v_00_u03b2_400_, v_00_u03b1_401_, v_ord_402_, v_f_403_, v_x_404_, v_y_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object* v_x_408_, lean_object* v_y_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_x_408_, v_y_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_eq(v_x_408_, v_y_409_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = 2;
return v___x_412_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 1;
return v___x_413_;
}
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* v_x_415_, lean_object* v_y_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_instOrdNat___lam__0(v_x_415_, v_y_416_);
lean_dec(v_y_416_);
lean_dec(v_x_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object* v_x_421_, lean_object* v_y_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_int_dec_lt(v_x_421_, v_y_422_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = lean_int_dec_eq(v_x_421_, v_y_422_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 2;
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 1;
return v___x_426_;
}
}
else
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* v_x_428_, lean_object* v_y_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_instOrdInt___lam__0(v_x_428_, v_y_429_);
lean_dec(v_y_429_);
lean_dec(v_x_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t v_x_434_, uint8_t v_x_435_){
_start:
{
if (v_x_434_ == 0)
{
if (v_x_435_ == 1)
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 1;
return v___x_437_;
}
}
else
{
if (v_x_435_ == 0)
{
uint8_t v___x_438_; 
v___x_438_ = 2;
return v___x_438_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = 1;
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_x_49__boxed_442_; uint8_t v_x_50__boxed_443_; uint8_t v_res_444_; lean_object* v_r_445_; 
v_x_49__boxed_442_ = lean_unbox(v_x_440_);
v_x_50__boxed_443_ = lean_unbox(v_x_441_);
v_res_444_ = l_instOrdBool___lam__0(v_x_49__boxed_442_, v_x_50__boxed_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* v_n_448_){
_start:
{
lean_object* v___f_449_; 
v___f_449_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_449_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* v_n_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_instOrdFin(v_n_450_);
lean_dec(v_n_450_);
return v_res_451_;
}
}
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t v_x_452_, uint32_t v_y_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_uint32_dec_lt(v_x_452_, v_y_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = lean_uint32_dec_eq(v_x_452_, v_y_453_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 2;
return v___x_456_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 1;
return v___x_457_;
}
}
else
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* v_x_459_, lean_object* v_y_460_){
_start:
{
uint32_t v_x_boxed_461_; uint32_t v_y_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_x_boxed_461_ = lean_unbox_uint32(v_x_459_);
lean_dec(v_x_459_);
v_y_boxed_462_ = lean_unbox_uint32(v_y_460_);
lean_dec(v_y_460_);
v_res_463_ = l_instOrdChar___lam__0(v_x_boxed_461_, v_y_boxed_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l_instOrdBitVec___lam__0(lean_object* v_x_467_, lean_object* v_y_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = l_instDecidableLtBitVec___aux__1___redArg(v_x_467_, v_y_468_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_eq(v_x_467_, v_y_468_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = 2;
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = 1;
return v___x_472_;
}
}
else
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___lam__0___boxed(lean_object* v_x_474_, lean_object* v_y_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_instOrdBitVec___lam__0(v_x_474_, v_y_475_);
lean_dec(v_y_475_);
lean_dec(v_x_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_479_){
_start:
{
lean_object* v___f_480_; 
v___f_480_ = ((lean_object*)(l_instOrdBitVec___closed__0));
return v___f_480_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_instOrdBitVec(v_n_481_);
lean_dec(v_n_481_);
return v_res_482_;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_dec_ref(v_inst_483_);
if (lean_obj_tag(v_x_485_) == 0)
{
uint8_t v___x_486_; 
v___x_486_ = 1;
return v___x_486_;
}
else
{
uint8_t v___x_487_; 
lean_dec_ref(v_x_485_);
v___x_487_ = 0;
return v___x_487_;
}
}
else
{
if (lean_obj_tag(v_x_485_) == 0)
{
uint8_t v___x_488_; 
lean_dec_ref(v_x_484_);
lean_dec_ref(v_inst_483_);
v___x_488_ = 2;
return v___x_488_;
}
else
{
lean_object* v_val_489_; lean_object* v_val_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_val_489_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_val_489_);
lean_dec_ref(v_x_484_);
v_val_490_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_val_490_);
lean_dec_ref(v_x_485_);
v___x_491_ = lean_apply_2(v_inst_483_, v_val_489_, v_val_490_);
v___x_492_ = lean_unbox(v___x_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_instOrdOption___redArg___lam__0(v_inst_493_, v_x_494_, v_x_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_498_){
_start:
{
lean_object* v___f_499_; 
v___f_499_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_499_, 0, v_inst_498_);
return v___f_499_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_500_, lean_object* v_inst_501_){
_start:
{
lean_object* v___f_502_; 
v___f_502_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_502_, 0, v_inst_501_);
return v___f_502_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* v_cmp_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_dec_ref(v_cmp_508_);
if (lean_obj_tag(v_x_510_) == 0)
{
uint8_t v___x_511_; 
v___x_511_ = 1;
return v___x_511_;
}
else
{
uint8_t v___x_512_; 
lean_dec(v_x_510_);
v___x_512_ = 0;
return v___x_512_;
}
}
else
{
if (lean_obj_tag(v_x_510_) == 0)
{
uint8_t v___x_513_; 
lean_dec_ref(v_x_509_);
lean_dec_ref(v_cmp_508_);
v___x_513_ = 2;
return v___x_513_;
}
else
{
lean_object* v_head_514_; lean_object* v_tail_515_; lean_object* v_head_516_; lean_object* v_tail_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_head_514_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_head_514_);
v_tail_515_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_tail_515_);
lean_dec_ref(v_x_509_);
v_head_516_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_head_516_);
v_tail_517_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_tail_517_);
lean_dec_ref(v_x_510_);
lean_inc_ref(v_cmp_508_);
v___x_518_ = lean_apply_2(v_cmp_508_, v_head_514_, v_head_516_);
v___x_519_ = lean_unbox(v___x_518_);
if (v___x_519_ == 1)
{
v_x_509_ = v_tail_515_;
v_x_510_ = v_tail_517_;
goto _start;
}
else
{
uint8_t v___x_521_; 
lean_dec(v_tail_517_);
lean_dec(v_tail_515_);
lean_dec_ref(v_cmp_508_);
v___x_521_ = lean_unbox(v___x_518_);
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_List_compareLex___redArg(v_cmp_522_, v_x_523_, v_x_524_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* v_00_u03b1_527_, lean_object* v_cmp_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_List_compareLex___redArg(v_cmp_528_, v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_532_, lean_object* v_cmp_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_List_compareLex(v_00_u03b1_532_, v_cmp_533_, v_x_534_, v_x_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_539_, 0, lean_box(0));
lean_closure_set(v___x_539_, 1, v_inst_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_540_, lean_object* v_inst_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_542_, 0, lean_box(0));
lean_closure_set(v___x_542_, 1, v_inst_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_, lean_object* v_h__3_547_, lean_object* v_h__4_548_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_dec(v_h__4_548_);
lean_dec(v_h__3_547_);
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_h__2_546_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_apply_1(v_h__1_545_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
lean_dec(v_h__1_545_);
v___x_551_ = lean_apply_2(v_h__2_546_, v_x_544_, lean_box(0));
return v___x_551_;
}
}
else
{
lean_dec(v_h__2_546_);
lean_dec(v_h__1_545_);
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v___x_552_; 
lean_dec(v_h__4_548_);
v___x_552_ = lean_apply_2(v_h__3_547_, v_x_543_, lean_box(0));
return v___x_552_;
}
else
{
lean_object* v_head_553_; lean_object* v_tail_554_; lean_object* v_head_555_; lean_object* v_tail_556_; lean_object* v___x_557_; 
lean_dec(v_h__3_547_);
v_head_553_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_head_553_);
v_tail_554_ = lean_ctor_get(v_x_543_, 1);
lean_inc(v_tail_554_);
lean_dec_ref(v_x_543_);
v_head_555_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_head_555_);
v_tail_556_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_tail_556_);
lean_dec_ref(v_x_544_);
v___x_557_ = lean_apply_4(v_h__4_548_, v_head_553_, v_tail_554_, v_head_555_, v_tail_556_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_558_, lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_h__1_562_, lean_object* v_h__2_563_, lean_object* v_h__3_564_, lean_object* v_h__4_565_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_dec(v_h__4_565_);
lean_dec(v_h__3_564_);
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_h__2_563_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_apply_1(v_h__1_562_, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; 
lean_dec(v_h__1_562_);
v___x_568_ = lean_apply_2(v_h__2_563_, v_x_561_, lean_box(0));
return v___x_568_;
}
}
else
{
lean_dec(v_h__2_563_);
lean_dec(v_h__1_562_);
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v___x_569_; 
lean_dec(v_h__4_565_);
v___x_569_ = lean_apply_2(v_h__3_564_, v_x_560_, lean_box(0));
return v___x_569_;
}
else
{
lean_object* v_head_570_; lean_object* v_tail_571_; lean_object* v_head_572_; lean_object* v_tail_573_; lean_object* v___x_574_; 
lean_dec(v_h__3_564_);
v_head_570_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_570_);
v_tail_571_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_tail_571_);
lean_dec_ref(v_x_560_);
v_head_572_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_head_572_);
v_tail_573_ = lean_ctor_get(v_x_561_, 1);
lean_inc(v_tail_573_);
lean_dec_ref(v_x_561_);
v___x_574_ = lean_apply_4(v_h__4_565_, v_head_570_, v_tail_571_, v_head_572_, v_tail_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_, lean_object* v_h__3_578_){
_start:
{
switch(v_x_575_)
{
case 0:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_h__3_578_);
lean_dec(v_h__2_577_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_h__1_576_, v___x_579_);
return v___x_580_;
}
case 1:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v_h__3_578_);
lean_dec(v_h__1_576_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_apply_1(v_h__2_577_, v___x_581_);
return v___x_582_;
}
default: 
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_h__2_577_);
lean_dec(v_h__1_576_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_apply_1(v_h__3_578_, v___x_583_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_585_, lean_object* v_h__1_586_, lean_object* v_h__2_587_, lean_object* v_h__3_588_){
_start:
{
uint8_t v_x_36__boxed_589_; lean_object* v_res_590_; 
v_x_36__boxed_589_ = lean_unbox(v_x_585_);
v_res_590_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_36__boxed_589_, v_h__1_586_, v_h__2_587_, v_h__3_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_591_, uint8_t v_x_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_, lean_object* v_h__3_595_){
_start:
{
switch(v_x_592_)
{
case 0:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_h__3_595_);
lean_dec(v_h__2_594_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_apply_1(v_h__1_593_, v___x_596_);
return v___x_597_;
}
case 1:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_h__3_595_);
lean_dec(v_h__1_593_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_apply_1(v_h__2_594_, v___x_598_);
return v___x_599_;
}
default: 
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_h__2_594_);
lean_dec(v_h__1_593_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_apply_1(v_h__3_595_, v___x_600_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_602_, lean_object* v_x_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_, lean_object* v_h__3_606_){
_start:
{
uint8_t v_x_51__boxed_607_; lean_object* v_res_608_; 
v_x_51__boxed_607_ = lean_unbox(v_x_603_);
v_res_608_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_602_, v_x_51__boxed_607_, v_h__1_604_, v_h__2_605_, v_h__3_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_609_){
_start:
{
lean_object* v_fst_610_; 
v_fst_610_ = lean_ctor_get(v_x_609_, 0);
lean_inc(v_fst_610_);
return v_fst_610_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_lexOrd___redArg___lam__0(v_x_611_);
lean_dec_ref(v_x_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_613_){
_start:
{
lean_object* v_snd_614_; 
v_snd_614_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_snd_614_);
return v_snd_614_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_lexOrd___redArg___lam__1(v_x_615_);
lean_dec_ref(v_x_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_621_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_622_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_623_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, lean_box(0));
lean_closure_set(v___x_623_, 2, v_inst_619_);
lean_closure_set(v___x_623_, 3, v___f_621_);
v___x_624_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_624_, 0, lean_box(0));
lean_closure_set(v___x_624_, 1, lean_box(0));
lean_closure_set(v___x_624_, 2, v_inst_620_);
lean_closure_set(v___x_624_, 3, v___f_622_);
v___x_625_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_625_, 0, lean_box(0));
lean_closure_set(v___x_625_, 1, lean_box(0));
lean_closure_set(v___x_625_, 2, v___x_623_);
lean_closure_set(v___x_625_, 3, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_lexOrd___redArg(v_inst_628_, v_inst_629_);
return v___x_630_;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_631_, lean_object* v_a_632_, lean_object* v_b_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_apply_2(v_inst_631_, v_a_632_, v_b_633_);
v___x_635_ = lean_unbox(v___x_634_);
if (v___x_635_ == 1)
{
uint8_t v___x_636_; 
v___x_636_ = 1;
return v___x_636_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = 0;
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_638_, lean_object* v_a_639_, lean_object* v_b_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_beqOfOrd___redArg___lam__0(v_inst_638_, v_a_639_, v_b_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_643_){
_start:
{
lean_object* v___f_644_; 
v___f_644_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_644_, 0, v_inst_643_);
return v___f_644_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v___f_647_; 
v___f_647_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_647_, 0, v_inst_646_);
return v___f_647_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_648_, lean_object* v_inst_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_ltOfOrd(v_00_u03b1_651_, v_inst_652_);
lean_dec_ref(v_inst_652_);
return v_res_653_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_apply_2(v_inst_654_, v_a_655_, v_b_656_);
v___x_658_ = lean_unbox(v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = 1;
return v___x_659_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = 0;
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_661_, lean_object* v_a_662_, lean_object* v_b_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_instDecidableRelLt___redArg(v_inst_661_, v_a_662_, v_b_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_, lean_object* v_a_668_, lean_object* v_b_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_apply_2(v_inst_667_, v_a_668_, v_b_669_);
v___x_671_ = lean_unbox(v___x_670_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_, lean_object* v_a_676_, lean_object* v_b_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_instDecidableRelLt(v_00_u03b1_674_, v_inst_675_, v_a_676_, v_b_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_683_, lean_object* v_inst_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_leOfOrd(v_00_u03b1_683_, v_inst_684_);
lean_dec_ref(v_inst_684_);
return v_res_685_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_apply_2(v_inst_686_, v_x_687_, v_x_688_);
v___x_690_ = lean_unbox(v___x_689_);
if (v___x_690_ == 2)
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 1;
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_instDecidableRelLe___redArg(v_inst_693_, v_x_694_, v_x_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_698_, lean_object* v_inst_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_apply_2(v_inst_699_, v_x_700_, v_x_701_);
v___x_703_ = lean_unbox(v___x_702_);
if (v___x_703_ == 2)
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 1;
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_instDecidableRelLe(v_00_u03b1_706_, v_inst_707_, v_x_708_, v_x_709_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_712_){
_start:
{
lean_object* v___f_713_; 
v___f_713_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_713_, 0, v_ord_712_);
return v___f_713_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_714_, lean_object* v_ord_715_){
_start:
{
lean_object* v___f_716_; 
v___f_716_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_716_, 0, v_ord_715_);
return v___f_716_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_717_, lean_object* v_ord_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_720_, lean_object* v_ord_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Ord_toLT(v_00_u03b1_720_, v_ord_721_);
lean_dec_ref(v_ord_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_723_, lean_object* v_ord_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_726_, lean_object* v_ord_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Ord_toLE(v_00_u03b1_726_, v_ord_727_);
lean_dec_ref(v_ord_727_);
return v_res_728_;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_729_, lean_object* v_x_730_, lean_object* v_y_731_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_apply_2(v_ord_729_, v_y_731_, v_x_730_);
v___x_733_ = lean_unbox(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_734_, lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_Ord_opposite___redArg___lam__0(v_ord_734_, v_x_735_, v_y_736_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_739_){
_start:
{
lean_object* v___f_740_; 
v___f_740_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_740_, 0, v_ord_739_);
return v___f_740_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_741_, lean_object* v_ord_742_){
_start:
{
lean_object* v___f_743_; 
v___f_743_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_743_, 0, v_ord_742_);
return v___f_743_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_744_, lean_object* v_f_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_746_, 0, lean_box(0));
lean_closure_set(v___x_746_, 1, lean_box(0));
lean_closure_set(v___x_746_, 2, v_x_744_);
lean_closure_set(v___x_746_, 3, v_f_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_747_, lean_object* v_00_u03b1_748_, lean_object* v_x_749_, lean_object* v_f_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_751_, 0, lean_box(0));
lean_closure_set(v___x_751_, 1, lean_box(0));
lean_closure_set(v___x_751_, 2, v_x_749_);
lean_closure_set(v___x_751_, 3, v_f_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_lexOrd___redArg(v_x_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_lexOrd___redArg(v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_760_, lean_object* v_ord_u2082_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_762_, 0, lean_box(0));
lean_closure_set(v___x_762_, 1, lean_box(0));
lean_closure_set(v___x_762_, 2, v_ord_u2081_760_);
lean_closure_set(v___x_762_, 3, v_ord_u2082_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_763_, lean_object* v_ord_u2081_764_, lean_object* v_ord_u2082_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_766_, 0, lean_box(0));
lean_closure_set(v___x_766_, 1, lean_box(0));
lean_closure_set(v___x_766_, 2, v_ord_u2081_764_);
lean_closure_set(v___x_766_, 3, v_ord_u2082_765_);
return v___x_766_;
}
}
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
