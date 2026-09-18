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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
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
LEAN_EXPORT lean_object* l_instOrdFin___redArg();
LEAN_EXPORT lean_object* l_instOrdFin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instOrdFin(lean_object*);
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdChar___closed__0 = (const lean_object*)&l_instOrdChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrdChar = (const lean_object*)&l_instOrdChar___closed__0_value;
LEAN_EXPORT uint8_t l_instOrdBitVec___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instOrdBitVec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdBitVec___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrdBitVec___redArg___closed__0 = (const lean_object*)&l_instOrdBitVec___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg();
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_ltOfOrd___redArg();
LEAN_EXPORT lean_object* l_ltOfOrd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd___redArg();
LEAN_EXPORT lean_object* l_leOfOrd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT___redArg();
LEAN_EXPORT lean_object* l_Ord_toLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ord_toLE___redArg();
LEAN_EXPORT lean_object* l_Ord_toLE___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instOrdFin___redArg(){
_start:
{
lean_object* v___f_448_; 
v___f_448_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_448_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___redArg___boxed(lean_object* v___dummy_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_instOrdFin___redArg();
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* v_n_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* v_n_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_instOrdFin(v_n_453_);
lean_dec(v_n_453_);
return v_res_454_;
}
}
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t v_x_455_, uint32_t v_y_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = lean_uint32_dec_lt(v_x_455_, v_y_456_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = lean_uint32_dec_eq(v_x_455_, v_y_456_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 2;
return v___x_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 1;
return v___x_460_;
}
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* v_x_462_, lean_object* v_y_463_){
_start:
{
uint32_t v_x_boxed_464_; uint32_t v_y_boxed_465_; uint8_t v_res_466_; lean_object* v_r_467_; 
v_x_boxed_464_ = lean_unbox_uint32(v_x_462_);
lean_dec(v_x_462_);
v_y_boxed_465_ = lean_unbox_uint32(v_y_463_);
lean_dec(v_y_463_);
v_res_466_ = l_instOrdChar___lam__0(v_x_boxed_464_, v_y_boxed_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT uint8_t l_instOrdBitVec___redArg___lam__0(lean_object* v_x_470_, lean_object* v_y_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_x_470_, v___x_472_);
v___x_474_ = lean_nat_dec_le(v___x_473_, v_y_471_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_eq(v_x_470_, v_y_471_);
if (v___x_475_ == 0)
{
uint8_t v___x_476_; 
v___x_476_ = 2;
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = 1;
return v___x_477_;
}
}
else
{
uint8_t v___x_478_; 
v___x_478_ = 0;
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___lam__0___boxed(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_instOrdBitVec___redArg___lam__0(v_x_479_, v_y_480_);
lean_dec(v_y_480_);
lean_dec(v_x_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg(){
_start:
{
lean_object* v___f_485_; 
v___f_485_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_485_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___boxed(lean_object* v___dummy_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_instOrdBitVec___redArg();
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_488_){
_start:
{
lean_object* v___f_489_; 
v___f_489_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_489_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_instOrdBitVec(v_n_490_);
lean_dec(v_n_490_);
return v_res_491_;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_dec_ref(v_inst_492_);
if (lean_obj_tag(v_x_494_) == 0)
{
uint8_t v___x_495_; 
v___x_495_ = 1;
return v___x_495_;
}
else
{
uint8_t v___x_496_; 
lean_dec_ref_known(v_x_494_, 1);
v___x_496_ = 0;
return v___x_496_;
}
}
else
{
if (lean_obj_tag(v_x_494_) == 0)
{
uint8_t v___x_497_; 
lean_dec_ref_known(v_x_493_, 1);
lean_dec_ref(v_inst_492_);
v___x_497_ = 2;
return v___x_497_;
}
else
{
lean_object* v_val_498_; lean_object* v_val_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_val_498_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_x_493_, 1);
v_val_499_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_x_494_, 1);
v___x_500_ = lean_apply_2(v_inst_492_, v_val_498_, v_val_499_);
v___x_501_ = lean_unbox(v___x_500_);
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_instOrdOption___redArg___lam__0(v_inst_502_, v_x_503_, v_x_504_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_507_){
_start:
{
lean_object* v___f_508_; 
v___f_508_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_508_, 0, v_inst_507_);
return v___f_508_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_509_, lean_object* v_inst_510_){
_start:
{
lean_object* v___f_511_; 
v___f_511_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_511_, 0, v_inst_510_);
return v___f_511_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* v_cmp_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_dec_ref(v_cmp_517_);
if (lean_obj_tag(v_x_519_) == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 1;
return v___x_520_;
}
else
{
uint8_t v___x_521_; 
lean_dec(v_x_519_);
v___x_521_ = 0;
return v___x_521_;
}
}
else
{
if (lean_obj_tag(v_x_519_) == 0)
{
uint8_t v___x_522_; 
lean_dec_ref_known(v_x_518_, 2);
lean_dec_ref(v_cmp_517_);
v___x_522_ = 2;
return v___x_522_;
}
else
{
lean_object* v_head_523_; lean_object* v_tail_524_; lean_object* v_head_525_; lean_object* v_tail_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_head_523_ = lean_ctor_get(v_x_518_, 0);
lean_inc(v_head_523_);
v_tail_524_ = lean_ctor_get(v_x_518_, 1);
lean_inc(v_tail_524_);
lean_dec_ref_known(v_x_518_, 2);
v_head_525_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_head_525_);
v_tail_526_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_tail_526_);
lean_dec_ref_known(v_x_519_, 2);
lean_inc_ref(v_cmp_517_);
v___x_527_ = lean_apply_2(v_cmp_517_, v_head_523_, v_head_525_);
v___x_528_ = lean_unbox(v___x_527_);
if (v___x_528_ == 1)
{
v_x_518_ = v_tail_524_;
v_x_519_ = v_tail_526_;
goto _start;
}
else
{
uint8_t v___x_530_; 
lean_dec(v_tail_526_);
lean_dec(v_tail_524_);
lean_dec_ref(v_cmp_517_);
v___x_530_ = lean_unbox(v___x_527_);
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_List_compareLex___redArg(v_cmp_531_, v_x_532_, v_x_533_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* v_00_u03b1_536_, lean_object* v_cmp_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = l_List_compareLex___redArg(v_cmp_537_, v_x_538_, v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_541_, lean_object* v_cmp_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_List_compareLex(v_00_u03b1_541_, v_cmp_542_, v_x_543_, v_x_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_548_, 0, lean_box(0));
lean_closure_set(v___x_548_, 1, v_inst_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_551_, 0, lean_box(0));
lean_closure_set(v___x_551_, 1, v_inst_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_, lean_object* v_h__3_556_, lean_object* v_h__4_557_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_dec(v_h__4_557_);
lean_dec(v_h__3_556_);
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_h__2_555_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_1(v_h__1_554_, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_h__1_554_);
v___x_560_ = lean_apply_2(v_h__2_555_, v_x_553_, lean_box(0));
return v___x_560_;
}
}
else
{
lean_dec(v_h__2_555_);
lean_dec(v_h__1_554_);
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v___x_561_; 
lean_dec(v_h__4_557_);
v___x_561_ = lean_apply_2(v_h__3_556_, v_x_552_, lean_box(0));
return v___x_561_;
}
else
{
lean_object* v_head_562_; lean_object* v_tail_563_; lean_object* v_head_564_; lean_object* v_tail_565_; lean_object* v___x_566_; 
lean_dec(v_h__3_556_);
v_head_562_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_head_562_);
v_tail_563_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_tail_563_);
lean_dec_ref_known(v_x_552_, 2);
v_head_564_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_head_564_);
v_tail_565_ = lean_ctor_get(v_x_553_, 1);
lean_inc(v_tail_565_);
lean_dec_ref_known(v_x_553_, 2);
v___x_566_ = lean_apply_4(v_h__4_557_, v_head_562_, v_tail_563_, v_head_564_, v_tail_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_567_, lean_object* v_motive_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_h__1_571_, lean_object* v_h__2_572_, lean_object* v_h__3_573_, lean_object* v_h__4_574_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_dec(v_h__4_574_);
lean_dec(v_h__3_573_);
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v_h__2_572_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_apply_1(v_h__1_571_, v___x_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; 
lean_dec(v_h__1_571_);
v___x_577_ = lean_apply_2(v_h__2_572_, v_x_570_, lean_box(0));
return v___x_577_;
}
}
else
{
lean_dec(v_h__2_572_);
lean_dec(v_h__1_571_);
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_578_; 
lean_dec(v_h__4_574_);
v___x_578_ = lean_apply_2(v_h__3_573_, v_x_569_, lean_box(0));
return v___x_578_;
}
else
{
lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v_head_581_; lean_object* v_tail_582_; lean_object* v___x_583_; 
lean_dec(v_h__3_573_);
v_head_579_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_head_579_);
v_tail_580_ = lean_ctor_get(v_x_569_, 1);
lean_inc(v_tail_580_);
lean_dec_ref_known(v_x_569_, 2);
v_head_581_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_head_581_);
v_tail_582_ = lean_ctor_get(v_x_570_, 1);
lean_inc(v_tail_582_);
lean_dec_ref_known(v_x_570_, 2);
v___x_583_ = lean_apply_4(v_h__4_574_, v_head_579_, v_tail_580_, v_head_581_, v_tail_582_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_, lean_object* v_h__3_587_){
_start:
{
switch(v_x_584_)
{
case 0:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_h__3_587_);
lean_dec(v_h__2_586_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_apply_1(v_h__1_585_, v___x_588_);
return v___x_589_;
}
case 1:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_h__3_587_);
lean_dec(v_h__1_585_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_apply_1(v_h__2_586_, v___x_590_);
return v___x_591_;
}
default: 
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_h__2_586_);
lean_dec(v_h__1_585_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_apply_1(v_h__3_587_, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_594_, lean_object* v_h__1_595_, lean_object* v_h__2_596_, lean_object* v_h__3_597_){
_start:
{
uint8_t v_x_33__boxed_598_; lean_object* v_res_599_; 
v_x_33__boxed_598_ = lean_unbox(v_x_594_);
v_res_599_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_598_, v_h__1_595_, v_h__2_596_, v_h__3_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_600_, uint8_t v_x_601_, lean_object* v_h__1_602_, lean_object* v_h__2_603_, lean_object* v_h__3_604_){
_start:
{
switch(v_x_601_)
{
case 0:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_h__3_604_);
lean_dec(v_h__2_603_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_apply_1(v_h__1_602_, v___x_605_);
return v___x_606_;
}
case 1:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_h__3_604_);
lean_dec(v_h__1_602_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_apply_1(v_h__2_603_, v___x_607_);
return v___x_608_;
}
default: 
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_h__2_603_);
lean_dec(v_h__1_602_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_apply_1(v_h__3_604_, v___x_609_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_611_, lean_object* v_x_612_, lean_object* v_h__1_613_, lean_object* v_h__2_614_, lean_object* v_h__3_615_){
_start:
{
uint8_t v_x_48__boxed_616_; lean_object* v_res_617_; 
v_x_48__boxed_616_ = lean_unbox(v_x_612_);
v_res_617_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_611_, v_x_48__boxed_616_, v_h__1_613_, v_h__2_614_, v_h__3_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_618_){
_start:
{
lean_object* v_fst_619_; 
v_fst_619_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_fst_619_);
return v_fst_619_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_lexOrd___redArg___lam__0(v_x_620_);
lean_dec_ref(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_622_){
_start:
{
lean_object* v_snd_623_; 
v_snd_623_ = lean_ctor_get(v_x_622_, 1);
lean_inc(v_snd_623_);
return v_snd_623_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_lexOrd___redArg___lam__1(v_x_624_);
lean_dec_ref(v_x_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___f_630_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_631_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_632_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_632_, 0, lean_box(0));
lean_closure_set(v___x_632_, 1, lean_box(0));
lean_closure_set(v___x_632_, 2, v_inst_628_);
lean_closure_set(v___x_632_, 3, v___f_630_);
v___x_633_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_633_, 0, lean_box(0));
lean_closure_set(v___x_633_, 1, lean_box(0));
lean_closure_set(v___x_633_, 2, v_inst_629_);
lean_closure_set(v___x_633_, 3, v___f_631_);
v___x_634_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_634_, 0, lean_box(0));
lean_closure_set(v___x_634_, 1, lean_box(0));
lean_closure_set(v___x_634_, 2, v___x_632_);
lean_closure_set(v___x_634_, 3, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_inst_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_lexOrd___redArg(v_inst_637_, v_inst_638_);
return v___x_639_;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_apply_2(v_inst_640_, v_a_641_, v_b_642_);
v___x_644_ = lean_unbox(v___x_643_);
if (v___x_644_ == 1)
{
uint8_t v___x_645_; 
v___x_645_ = 1;
return v___x_645_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_647_, lean_object* v_a_648_, lean_object* v_b_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_beqOfOrd___redArg___lam__0(v_inst_647_, v_a_648_, v_b_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_652_){
_start:
{
lean_object* v___f_653_; 
v___f_653_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_653_, 0, v_inst_652_);
return v___f_653_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_654_, lean_object* v_inst_655_){
_start:
{
lean_object* v___f_656_; 
v___f_656_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_656_, 0, v_inst_655_);
return v___f_656_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___redArg(){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___redArg___boxed(lean_object* v___dummy_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_ltOfOrd___redArg();
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_661_, lean_object* v_inst_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_box(0);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_664_, lean_object* v_inst_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_ltOfOrd(v_00_u03b1_664_, v_inst_665_);
lean_dec_ref(v_inst_665_);
return v_res_666_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_667_, lean_object* v_a_668_, lean_object* v_b_669_){
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
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_674_, lean_object* v_a_675_, lean_object* v_b_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_instDecidableRelLt___redArg(v_inst_674_, v_a_675_, v_b_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_679_, lean_object* v_inst_680_, lean_object* v_a_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_apply_2(v_inst_680_, v_a_681_, v_b_682_);
v___x_684_ = lean_unbox(v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = 1;
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = 0;
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_687_, lean_object* v_inst_688_, lean_object* v_a_689_, lean_object* v_b_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_instDecidableRelLt(v_00_u03b1_687_, v_inst_688_, v_a_689_, v_b_690_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___redArg(){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_box(0);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___redArg___boxed(lean_object* v___dummy_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_leOfOrd___redArg();
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_box(0);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_leOfOrd(v_00_u03b1_700_, v_inst_701_);
lean_dec_ref(v_inst_701_);
return v_res_702_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_apply_2(v_inst_703_, v_x_704_, v_x_705_);
v___x_707_ = lean_unbox(v___x_706_);
if (v___x_707_ == 2)
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = 1;
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_instDecidableRelLe___redArg(v_inst_710_, v_x_711_, v_x_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_715_, lean_object* v_inst_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_apply_2(v_inst_716_, v_x_717_, v_x_718_);
v___x_720_ = lean_unbox(v___x_719_);
if (v___x_720_ == 2)
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = 1;
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_723_, lean_object* v_inst_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_instDecidableRelLe(v_00_u03b1_723_, v_inst_724_, v_x_725_, v_x_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_729_){
_start:
{
lean_object* v___f_730_; 
v___f_730_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_730_, 0, v_ord_729_);
return v___f_730_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_731_, lean_object* v_ord_732_){
_start:
{
lean_object* v___f_733_; 
v___f_733_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v_ord_732_);
return v___f_733_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___redArg(){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___redArg___boxed(lean_object* v___dummy_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Ord_toLT___redArg();
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_738_, lean_object* v_ord_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_741_, lean_object* v_ord_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Ord_toLT(v_00_u03b1_741_, v_ord_742_);
lean_dec_ref(v_ord_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___redArg(){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_box(0);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___redArg___boxed(lean_object* v___dummy_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Ord_toLE___redArg();
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_748_, lean_object* v_ord_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_751_, lean_object* v_ord_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Ord_toLE(v_00_u03b1_751_, v_ord_752_);
lean_dec_ref(v_ord_752_);
return v_res_753_;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_754_, lean_object* v_x_755_, lean_object* v_y_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_apply_2(v_ord_754_, v_y_756_, v_x_755_);
v___x_758_ = lean_unbox(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_759_, lean_object* v_x_760_, lean_object* v_y_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Ord_opposite___redArg___lam__0(v_ord_759_, v_x_760_, v_y_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_764_){
_start:
{
lean_object* v___f_765_; 
v___f_765_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_765_, 0, v_ord_764_);
return v___f_765_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_766_, lean_object* v_ord_767_){
_start:
{
lean_object* v___f_768_; 
v___f_768_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_768_, 0, v_ord_767_);
return v___f_768_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_769_, lean_object* v_f_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_771_, 0, lean_box(0));
lean_closure_set(v___x_771_, 1, lean_box(0));
lean_closure_set(v___x_771_, 2, v_x_769_);
lean_closure_set(v___x_771_, 3, v_f_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_772_, lean_object* v_00_u03b1_773_, lean_object* v_x_774_, lean_object* v_f_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_776_, 0, lean_box(0));
lean_closure_set(v___x_776_, 1, lean_box(0));
lean_closure_set(v___x_776_, 2, v_x_774_);
lean_closure_set(v___x_776_, 3, v_f_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_lexOrd___redArg(v_x_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_lexOrd___redArg(v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_785_, lean_object* v_ord_u2082_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_787_, 0, lean_box(0));
lean_closure_set(v___x_787_, 1, lean_box(0));
lean_closure_set(v___x_787_, 2, v_ord_u2081_785_);
lean_closure_set(v___x_787_, 3, v_ord_u2082_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_788_, lean_object* v_ord_u2081_789_, lean_object* v_ord_u2082_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_791_, 0, lean_box(0));
lean_closure_set(v___x_791_, 1, lean_box(0));
lean_closure_set(v___x_791_, 2, v_ord_u2081_789_);
lean_closure_set(v___x_791_, 3, v_ord_u2082_790_);
return v___x_791_;
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
