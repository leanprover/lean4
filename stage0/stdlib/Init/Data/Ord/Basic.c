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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instOrdOrdering___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instOrdOrdering___lam__0___boxed(lean_object*);
static const lean_closure_object l_instOrdOrdering___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdOrdering___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Ordering_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Ordering_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Ordering_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object* v_lt_22_){
_start:
{
lean_inc(v_lt_22_);
return v_lt_22_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object* v_lt_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Ordering_lt_elim___redArg(v_lt_23_);
lean_dec(v_lt_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_lt_28_){
_start:
{
lean_inc(v_lt_28_);
return v_lt_28_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_lt_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Ordering_lt_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_lt_32_);
lean_dec(v_lt_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object* v_eq_35_){
_start:
{
lean_inc(v_eq_35_);
return v_eq_35_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object* v_eq_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Ordering_eq_elim___redArg(v_eq_36_);
lean_dec(v_eq_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_eq_41_){
_start:
{
lean_inc(v_eq_41_);
return v_eq_41_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_eq_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Ordering_eq_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_eq_45_);
lean_dec(v_eq_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object* v_gt_48_){
_start:
{
lean_inc(v_gt_48_);
return v_gt_48_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object* v_gt_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Ordering_gt_elim___redArg(v_gt_49_);
lean_dec(v_gt_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_gt_54_){
_start:
{
lean_inc(v_gt_54_);
return v_gt_54_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_gt_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Ordering_gt_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_gt_58_);
lean_dec(v_gt_58_);
return v_res_60_;
}
}
static uint8_t _init_l_instInhabitedOrdering_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_instInhabitedOrdering(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Ordering_ofNat(lean_object* v_n_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_nat_dec_le(v_n_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_dec_le(v_n_63_, v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 2;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_ofNat___boxed(lean_object* v_n_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Ordering_ofNat(v_n_71_);
lean_dec(v_n_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOrdering(uint8_t v_x_74_, uint8_t v_y_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = lean_box(v_x_74_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_box(v_y_75_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_23__boxed_83_; uint8_t v_y_24__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_23__boxed_83_ = lean_unbox(v_x_81_);
v_y_24__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_instDecidableEqOrdering(v_x_23__boxed_83_, v_y_24__boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__7(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr(uint8_t v_x_100_, lean_object* v_prec_101_){
_start:
{
lean_object* v___y_103_; lean_object* v___y_110_; lean_object* v___y_117_; 
switch(v_x_100_)
{
case 0:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1024u);
v___x_124_ = lean_nat_dec_le(v___x_123_, v_prec_101_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_103_ = v___x_125_;
goto v___jp_102_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_103_ = v___x_126_;
goto v___jp_102_;
}
}
case 1:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_101_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_110_ = v___x_129_;
goto v___jp_109_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_110_ = v___x_130_;
goto v___jp_109_;
}
}
default: 
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_101_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_117_ = v___x_133_;
goto v___jp_116_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_117_ = v___x_134_;
goto v___jp_116_;
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = ((lean_object*)(l_instReprOrdering_repr___closed__1));
lean_inc(v___y_103_);
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___y_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_106_);
v___x_108_ = l_Repr_addAppParen(v___x_107_, v_prec_101_);
return v___x_108_;
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l_instReprOrdering_repr___closed__3));
lean_inc(v___y_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_101_);
return v___x_115_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_instReprOrdering_repr___closed__5));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_101_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object* v_x_135_, lean_object* v_prec_136_){
_start:
{
uint8_t v_x_171__boxed_137_; lean_object* v_res_138_; 
v_x_171__boxed_137_ = lean_unbox(v_x_135_);
v_res_138_ = l_instReprOrdering_repr(v_x_171__boxed_137_, v_prec_136_);
lean_dec(v_prec_136_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l_Ordering_swap(uint8_t v_x_141_){
_start:
{
switch(v_x_141_)
{
case 0:
{
uint8_t v___x_142_; 
v___x_142_ = 2;
return v___x_142_;
}
case 1:
{
return v_x_141_;
}
default: 
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_25__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_x_25__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Ordering_swap(v_x_25__boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isEq(uint8_t v_x_148_){
_start:
{
if (v_x_148_ == 1)
{
uint8_t v___x_149_; 
v___x_149_ = 1;
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object* v_x_151_){
_start:
{
uint8_t v_x_17__boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_x_17__boxed_152_ = lean_unbox(v_x_151_);
v_res_153_ = l_Ordering_isEq(v_x_17__boxed_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isNe(uint8_t v_x_155_){
_start:
{
if (v_x_155_ == 1)
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 1;
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object* v_x_158_){
_start:
{
uint8_t v_x_17__boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_x_17__boxed_159_ = lean_unbox(v_x_158_);
v_res_160_ = l_Ordering_isNe(v_x_17__boxed_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLE(uint8_t v_x_162_){
_start:
{
if (v_x_162_ == 2)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object* v_x_165_){
_start:
{
uint8_t v_x_17__boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_x_17__boxed_166_ = lean_unbox(v_x_165_);
v_res_167_ = l_Ordering_isLE(v_x_17__boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isLT(uint8_t v_x_169_){
_start:
{
if (v_x_169_ == 0)
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object* v_x_172_){
_start:
{
uint8_t v_x_17__boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_x_17__boxed_173_ = lean_unbox(v_x_172_);
v_res_174_ = l_Ordering_isLT(v_x_17__boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGT(uint8_t v_x_176_){
_start:
{
if (v_x_176_ == 2)
{
uint8_t v___x_177_; 
v___x_177_ = 1;
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_x_17__boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_x_17__boxed_180_ = lean_unbox(v_x_179_);
v_res_181_ = l_Ordering_isGT(v_x_17__boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Ordering_isGE(uint8_t v_x_183_){
_start:
{
if (v_x_183_ == 0)
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 1;
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object* v_x_186_){
_start:
{
uint8_t v_x_17__boxed_187_; uint8_t v_res_188_; lean_object* v_r_189_; 
v_x_17__boxed_187_ = lean_unbox(v_x_186_);
v_res_188_ = l_Ordering_isGE(v_x_17__boxed_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_190_){
_start:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = 0;
v___x_192_ = lean_box(v___x_191_);
lean_inc_ref(v_inst_190_);
v___x_193_ = lean_apply_1(v_inst_190_, v___x_192_);
v___x_194_ = lean_unbox(v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
lean_dec_ref(v_inst_190_);
v___x_195_ = lean_unbox(v___x_193_);
return v___x_195_;
}
else
{
uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_196_ = 1;
v___x_197_ = lean_box(v___x_196_);
lean_inc_ref(v_inst_190_);
v___x_198_ = lean_apply_1(v_inst_190_, v___x_197_);
v___x_199_ = lean_unbox(v___x_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
lean_dec_ref(v_inst_190_);
v___x_200_ = lean_unbox(v___x_198_);
return v___x_200_;
}
else
{
uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_201_ = 2;
v___x_202_ = lean_box(v___x_201_);
v___x_203_ = lean_apply_1(v_inst_190_, v___x_202_);
v___x_204_ = lean_unbox(v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* v_p_208_, lean_object* v_inst_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_211_, lean_object* v_inst_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_211_, v_inst_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_215_){
_start:
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_216_ = 0;
v___x_217_ = lean_box(v___x_216_);
lean_inc_ref(v_inst_215_);
v___x_218_ = lean_apply_1(v_inst_215_, v___x_217_);
v___x_219_ = lean_unbox(v___x_218_);
if (v___x_219_ == 0)
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = 1;
v___x_221_ = lean_box(v___x_220_);
lean_inc_ref(v_inst_215_);
v___x_222_ = lean_apply_1(v_inst_215_, v___x_221_);
v___x_223_ = lean_unbox(v___x_222_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = 2;
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_apply_1(v_inst_215_, v___x_225_);
v___x_227_ = lean_unbox(v___x_226_);
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
lean_dec_ref(v_inst_215_);
v___x_228_ = lean_unbox(v___x_222_);
return v___x_228_;
}
}
else
{
uint8_t v___x_229_; 
lean_dec_ref(v_inst_215_);
v___x_229_ = lean_unbox(v___x_218_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* v_p_233_, lean_object* v_inst_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_236_, lean_object* v_inst_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_236_, v_inst_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
if (v_a_240_ == 1)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_h__2_242_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_apply_1(v_h__1_241_, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_h__1_241_);
v___x_245_ = lean_box(v_a_240_);
v___x_246_ = lean_apply_2(v_h__2_242_, v___x_245_, lean_box(0));
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_){
_start:
{
uint8_t v_a_13__boxed_250_; lean_object* v_res_251_; 
v_a_13__boxed_250_ = lean_unbox(v_a_247_);
v_res_251_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_250_, v_h__1_248_, v_h__2_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* v_motive_252_, uint8_t v_a_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
if (v_a_253_ == 1)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__2_255_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_1(v_h__1_254_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__1_254_);
v___x_258_ = lean_box(v_a_253_);
v___x_259_ = lean_apply_2(v_h__2_255_, v___x_258_, lean_box(0));
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_260_, lean_object* v_a_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
uint8_t v_a_24__boxed_264_; lean_object* v_res_265_; 
v_a_24__boxed_264_ = lean_unbox(v_a_261_);
v_res_265_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(v_motive_260_, v_a_24__boxed_264_, v_h__1_262_, v_h__2_263_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object* v_x_266_, lean_object* v_y_267_, uint8_t v_inst_268_, lean_object* v_inst_269_){
_start:
{
if (v_inst_268_ == 0)
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_apply_2(v_inst_269_, v_x_266_, v_y_267_);
v___x_271_ = lean_unbox(v___x_270_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 2;
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = 1;
return v___x_273_;
}
}
else
{
uint8_t v___x_274_; 
lean_dec_ref(v_inst_269_);
lean_dec(v_y_267_);
lean_dec(v_x_266_);
v___x_274_ = 0;
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* v_x_275_, lean_object* v_y_276_, lean_object* v_inst_277_, lean_object* v_inst_278_){
_start:
{
uint8_t v_inst_21__boxed_279_; uint8_t v_res_280_; lean_object* v_r_281_; 
v_inst_21__boxed_279_ = lean_unbox(v_inst_277_);
v_res_280_ = l_compareOfLessAndEq___redArg(v_x_275_, v_y_276_, v_inst_21__boxed_279_, v_inst_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object* v_00_u03b1_282_, lean_object* v_x_283_, lean_object* v_y_284_, lean_object* v_inst_285_, uint8_t v_inst_286_, lean_object* v_inst_287_){
_start:
{
if (v_inst_286_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_apply_2(v_inst_287_, v_x_283_, v_y_284_);
v___x_289_ = lean_unbox(v___x_288_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 2;
return v___x_290_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = 1;
return v___x_291_;
}
}
else
{
uint8_t v___x_292_; 
lean_dec_ref(v_inst_287_);
lean_dec(v_y_284_);
lean_dec(v_x_283_);
v___x_292_ = 0;
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* v_00_u03b1_293_, lean_object* v_x_294_, lean_object* v_y_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_){
_start:
{
uint8_t v_inst_38__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_inst_38__boxed_299_ = lean_unbox(v_inst_297_);
v_res_300_ = l_compareOfLessAndEq(v_00_u03b1_293_, v_x_294_, v_y_295_, v_inst_296_, v_inst_38__boxed_299_, v_inst_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object* v_x_302_, lean_object* v_y_303_, uint8_t v_inst_304_, lean_object* v_inst_305_){
_start:
{
if (v_inst_304_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_apply_2(v_inst_305_, v_x_302_, v_y_303_);
v___x_307_ = lean_unbox(v___x_306_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 2;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
}
else
{
uint8_t v___x_310_; 
lean_dec_ref(v_inst_305_);
lean_dec(v_y_303_);
lean_dec(v_x_302_);
v___x_310_ = 0;
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* v_x_311_, lean_object* v_y_312_, lean_object* v_inst_313_, lean_object* v_inst_314_){
_start:
{
uint8_t v_inst_28__boxed_315_; uint8_t v_res_316_; lean_object* v_r_317_; 
v_inst_28__boxed_315_ = lean_unbox(v_inst_313_);
v_res_316_ = l_compareOfLessAndBEq___redArg(v_x_311_, v_y_312_, v_inst_28__boxed_315_, v_inst_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object* v_00_u03b1_318_, lean_object* v_x_319_, lean_object* v_y_320_, lean_object* v_inst_321_, uint8_t v_inst_322_, lean_object* v_inst_323_){
_start:
{
if (v_inst_322_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_apply_2(v_inst_323_, v_x_319_, v_y_320_);
v___x_325_ = lean_unbox(v___x_324_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = 2;
return v___x_326_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = 1;
return v___x_327_;
}
}
else
{
uint8_t v___x_328_; 
lean_dec_ref(v_inst_323_);
lean_dec(v_y_320_);
lean_dec(v_x_319_);
v___x_328_ = 0;
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* v_00_u03b1_329_, lean_object* v_x_330_, lean_object* v_y_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_){
_start:
{
uint8_t v_inst_45__boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_inst_45__boxed_335_ = lean_unbox(v_inst_333_);
v_res_336_ = l_compareOfLessAndBEq(v_00_u03b1_329_, v_x_330_, v_y_331_, v_inst_332_, v_inst_45__boxed_335_, v_inst_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object* v_cmp_u2081_338_, lean_object* v_cmp_u2082_339_, lean_object* v_a_340_, lean_object* v_b_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
lean_inc(v_b_341_);
lean_inc(v_a_340_);
v___x_342_ = lean_apply_2(v_cmp_u2081_338_, v_a_340_, v_b_341_);
v___x_343_ = lean_unbox(v___x_342_);
if (v___x_343_ == 1)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_apply_2(v_cmp_u2082_339_, v_a_340_, v_b_341_);
v___x_345_ = lean_unbox(v___x_344_);
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_b_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_cmp_u2082_339_);
v___x_346_ = lean_unbox(v___x_342_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* v_cmp_u2081_347_, lean_object* v_cmp_u2082_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_compareLex___redArg(v_cmp_u2081_347_, v_cmp_u2082_348_, v_a_349_, v_b_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_compareLex(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_cmp_u2081_355_, lean_object* v_cmp_u2082_356_, lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
lean_inc(v_b_358_);
lean_inc(v_a_357_);
v___x_359_ = lean_apply_2(v_cmp_u2081_355_, v_a_357_, v_b_358_);
v___x_360_ = lean_unbox(v___x_359_);
if (v___x_360_ == 1)
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_apply_2(v_cmp_u2082_356_, v_a_357_, v_b_358_);
v___x_362_ = lean_unbox(v___x_361_);
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
lean_dec(v_b_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_cmp_u2082_356_);
v___x_363_ = lean_unbox(v___x_359_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_cmp_u2081_366_, lean_object* v_cmp_u2082_367_, lean_object* v_a_368_, lean_object* v_b_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_compareLex(v_00_u03b1_364_, v_00_u03b2_365_, v_cmp_u2081_366_, v_cmp_u2082_367_, v_a_368_, v_b_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object* v_ord_372_, lean_object* v_f_373_, lean_object* v_x_374_, lean_object* v_y_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
lean_inc(v_f_373_);
v___x_376_ = lean_apply_1(v_f_373_, v_x_374_);
v___x_377_ = lean_apply_1(v_f_373_, v_y_375_);
v___x_378_ = lean_apply_2(v_ord_372_, v___x_376_, v___x_377_);
v___x_379_ = lean_unbox(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* v_ord_380_, lean_object* v_f_381_, lean_object* v_x_382_, lean_object* v_y_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_compareOn___redArg(v_ord_380_, v_f_381_, v_x_382_, v_y_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_compareOn(lean_object* v_00_u03b2_386_, lean_object* v_00_u03b1_387_, lean_object* v_ord_388_, lean_object* v_f_389_, lean_object* v_x_390_, lean_object* v_y_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
lean_inc(v_f_389_);
v___x_392_ = lean_apply_1(v_f_389_, v_x_390_);
v___x_393_ = lean_apply_1(v_f_389_, v_y_391_);
v___x_394_ = lean_apply_2(v_ord_388_, v___x_392_, v___x_393_);
v___x_395_ = lean_unbox(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* v_00_u03b2_396_, lean_object* v_00_u03b1_397_, lean_object* v_ord_398_, lean_object* v_f_399_, lean_object* v_x_400_, lean_object* v_y_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_compareOn(v_00_u03b2_396_, v_00_u03b1_397_, v_ord_398_, v_f_399_, v_x_400_, v_y_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object* v_x_404_, lean_object* v_y_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_lt(v_x_404_, v_y_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = lean_nat_dec_eq(v_x_404_, v_y_405_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; 
v___x_408_ = 2;
return v___x_408_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 1;
return v___x_409_;
}
}
else
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* v_x_411_, lean_object* v_y_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_instOrdNat___lam__0(v_x_411_, v_y_412_);
lean_dec(v_y_412_);
lean_dec(v_x_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object* v_x_417_, lean_object* v_y_418_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = lean_int_dec_lt(v_x_417_, v_y_418_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = lean_int_dec_eq(v_x_417_, v_y_418_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 2;
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 1;
return v___x_422_;
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* v_x_424_, lean_object* v_y_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_instOrdInt___lam__0(v_x_424_, v_y_425_);
lean_dec(v_y_425_);
lean_dec(v_x_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t v_x_430_, uint8_t v_x_431_){
_start:
{
if (v_x_430_ == 0)
{
if (v_x_431_ == 1)
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = 1;
return v___x_433_;
}
}
else
{
if (v_x_431_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = 2;
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = 1;
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_x_39__boxed_438_; uint8_t v_x_40__boxed_439_; uint8_t v_res_440_; lean_object* v_r_441_; 
v_x_39__boxed_438_ = lean_unbox(v_x_436_);
v_x_40__boxed_439_ = lean_unbox(v_x_437_);
v_res_440_ = l_instOrdBool___lam__0(v_x_39__boxed_438_, v_x_40__boxed_439_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___redArg(){
_start:
{
lean_object* v___f_445_; 
v___f_445_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___redArg___boxed(lean_object* v___dummy_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_instOrdFin___redArg();
return v_res_447_;
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
LEAN_EXPORT uint8_t l_instOrdBitVec___redArg___lam__0(lean_object* v_x_467_, lean_object* v_y_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_x_467_, v___x_469_);
v___x_471_ = lean_nat_dec_le(v___x_470_, v_y_468_);
lean_dec(v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_eq(v_x_467_, v_y_468_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = 2;
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = 1;
return v___x_474_;
}
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___lam__0___boxed(lean_object* v_x_476_, lean_object* v_y_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_instOrdBitVec___redArg___lam__0(v_x_476_, v_y_477_);
lean_dec(v_y_477_);
lean_dec(v_x_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg(){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___boxed(lean_object* v___dummy_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_instOrdBitVec___redArg();
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_485_){
_start:
{
lean_object* v___f_486_; 
v___f_486_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_486_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_instOrdBitVec(v_n_487_);
lean_dec(v_n_487_);
return v_res_488_;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_dec_ref(v_inst_489_);
if (lean_obj_tag(v_x_491_) == 0)
{
uint8_t v___x_492_; 
v___x_492_ = 1;
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
lean_dec_ref_known(v_x_491_, 1);
v___x_493_ = 0;
return v___x_493_;
}
}
else
{
if (lean_obj_tag(v_x_491_) == 0)
{
uint8_t v___x_494_; 
lean_dec_ref_known(v_x_490_, 1);
lean_dec_ref(v_inst_489_);
v___x_494_ = 2;
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v_val_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_val_495_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_x_490_, 1);
v_val_496_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v_x_491_, 1);
v___x_497_ = lean_apply_2(v_inst_489_, v_val_495_, v_val_496_);
v___x_498_ = lean_unbox(v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_instOrdOption___redArg___lam__0(v_inst_499_, v_x_500_, v_x_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_504_){
_start:
{
lean_object* v___f_505_; 
v___f_505_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_505_, 0, v_inst_504_);
return v___f_505_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_506_, lean_object* v_inst_507_){
_start:
{
lean_object* v___f_508_; 
v___f_508_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_508_, 0, v_inst_507_);
return v___f_508_;
}
}
LEAN_EXPORT lean_object* l_instOrdOrdering___lam__0(uint8_t v_x_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_box(v_x_509_);
v___x_511_ = lean_obj_tag_nat(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_instOrdOrdering___lam__0___boxed(lean_object* v_x_512_){
_start:
{
uint8_t v_x_11__boxed_513_; lean_object* v_res_514_; 
v_x_11__boxed_513_ = lean_unbox(v_x_512_);
v_res_514_ = l_instOrdOrdering___lam__0(v_x_11__boxed_513_);
return v_res_514_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* v_cmp_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_dec_ref(v_cmp_520_);
if (lean_obj_tag(v_x_522_) == 0)
{
uint8_t v___x_523_; 
v___x_523_ = 1;
return v___x_523_;
}
else
{
uint8_t v___x_524_; 
lean_dec(v_x_522_);
v___x_524_ = 0;
return v___x_524_;
}
}
else
{
if (lean_obj_tag(v_x_522_) == 0)
{
uint8_t v___x_525_; 
lean_dec_ref_known(v_x_521_, 2);
lean_dec_ref(v_cmp_520_);
v___x_525_ = 2;
return v___x_525_;
}
else
{
lean_object* v_head_526_; lean_object* v_tail_527_; lean_object* v_head_528_; lean_object* v_tail_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_head_526_ = lean_ctor_get(v_x_521_, 0);
lean_inc(v_head_526_);
v_tail_527_ = lean_ctor_get(v_x_521_, 1);
lean_inc(v_tail_527_);
lean_dec_ref_known(v_x_521_, 2);
v_head_528_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_head_528_);
v_tail_529_ = lean_ctor_get(v_x_522_, 1);
lean_inc(v_tail_529_);
lean_dec_ref_known(v_x_522_, 2);
lean_inc_ref(v_cmp_520_);
v___x_530_ = lean_apply_2(v_cmp_520_, v_head_526_, v_head_528_);
v___x_531_ = lean_unbox(v___x_530_);
if (v___x_531_ == 1)
{
v_x_521_ = v_tail_527_;
v_x_522_ = v_tail_529_;
goto _start;
}
else
{
uint8_t v___x_533_; 
lean_dec(v_tail_529_);
lean_dec(v_tail_527_);
lean_dec_ref(v_cmp_520_);
v___x_533_ = lean_unbox(v___x_530_);
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_List_compareLex___redArg(v_cmp_534_, v_x_535_, v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* v_00_u03b1_539_, lean_object* v_cmp_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = l_List_compareLex___redArg(v_cmp_540_, v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_544_, lean_object* v_cmp_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_List_compareLex(v_00_u03b1_544_, v_cmp_545_, v_x_546_, v_x_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_551_, 0, lean_box(0));
lean_closure_set(v___x_551_, 1, v_inst_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_552_, lean_object* v_inst_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_554_, 0, lean_box(0));
lean_closure_set(v___x_554_, 1, v_inst_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_h__1_557_, lean_object* v_h__2_558_, lean_object* v_h__3_559_, lean_object* v_h__4_560_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_dec(v_h__4_560_);
lean_dec(v_h__3_559_);
if (lean_obj_tag(v_x_556_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_h__2_558_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_1(v_h__1_557_, v___x_561_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
lean_dec(v_h__1_557_);
v___x_563_ = lean_apply_2(v_h__2_558_, v_x_556_, lean_box(0));
return v___x_563_;
}
}
else
{
lean_dec(v_h__2_558_);
lean_dec(v_h__1_557_);
if (lean_obj_tag(v_x_556_) == 0)
{
lean_object* v___x_564_; 
lean_dec(v_h__4_560_);
v___x_564_ = lean_apply_2(v_h__3_559_, v_x_555_, lean_box(0));
return v___x_564_;
}
else
{
lean_object* v_head_565_; lean_object* v_tail_566_; lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_569_; 
lean_dec(v_h__3_559_);
v_head_565_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_head_565_);
v_tail_566_ = lean_ctor_get(v_x_555_, 1);
lean_inc(v_tail_566_);
lean_dec_ref_known(v_x_555_, 2);
v_head_567_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_head_567_);
v_tail_568_ = lean_ctor_get(v_x_556_, 1);
lean_inc(v_tail_568_);
lean_dec_ref_known(v_x_556_, 2);
v___x_569_ = lean_apply_4(v_h__4_560_, v_head_565_, v_tail_566_, v_head_567_, v_tail_568_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_570_, lean_object* v_motive_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_h__1_574_, lean_object* v_h__2_575_, lean_object* v_h__3_576_, lean_object* v_h__4_577_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_dec(v_h__4_577_);
lean_dec(v_h__3_576_);
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__2_575_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_h__1_574_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
lean_dec(v_h__1_574_);
v___x_580_ = lean_apply_2(v_h__2_575_, v_x_573_, lean_box(0));
return v___x_580_;
}
}
else
{
lean_dec(v_h__2_575_);
lean_dec(v_h__1_574_);
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v___x_581_; 
lean_dec(v_h__4_577_);
v___x_581_ = lean_apply_2(v_h__3_576_, v_x_572_, lean_box(0));
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v___x_586_; 
lean_dec(v_h__3_576_);
v_head_582_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_head_582_);
v_tail_583_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_tail_583_);
lean_dec_ref_known(v_x_572_, 2);
v_head_584_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_head_584_);
v_tail_585_ = lean_ctor_get(v_x_573_, 1);
lean_inc(v_tail_585_);
lean_dec_ref_known(v_x_573_, 2);
v___x_586_ = lean_apply_4(v_h__4_577_, v_head_582_, v_tail_583_, v_head_584_, v_tail_585_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_587_, lean_object* v_h__1_588_, lean_object* v_h__2_589_, lean_object* v_h__3_590_){
_start:
{
switch(v_x_587_)
{
case 0:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_h__3_590_);
lean_dec(v_h__2_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_1(v_h__1_588_, v___x_591_);
return v___x_592_;
}
case 1:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_h__3_590_);
lean_dec(v_h__1_588_);
v___x_593_ = lean_box(0);
v___x_594_ = lean_apply_1(v_h__2_589_, v___x_593_);
return v___x_594_;
}
default: 
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_h__2_589_);
lean_dec(v_h__1_588_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_apply_1(v_h__3_590_, v___x_595_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_, lean_object* v_h__3_600_){
_start:
{
uint8_t v_x_33__boxed_601_; lean_object* v_res_602_; 
v_x_33__boxed_601_ = lean_unbox(v_x_597_);
v_res_602_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_601_, v_h__1_598_, v_h__2_599_, v_h__3_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_603_, uint8_t v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_, lean_object* v_h__3_607_){
_start:
{
switch(v_x_604_)
{
case 0:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_h__3_607_);
lean_dec(v_h__2_606_);
v___x_608_ = lean_box(0);
v___x_609_ = lean_apply_1(v_h__1_605_, v___x_608_);
return v___x_609_;
}
case 1:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_h__3_607_);
lean_dec(v_h__1_605_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_apply_1(v_h__2_606_, v___x_610_);
return v___x_611_;
}
default: 
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_h__2_606_);
lean_dec(v_h__1_605_);
v___x_612_ = lean_box(0);
v___x_613_ = lean_apply_1(v_h__3_607_, v___x_612_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_614_, lean_object* v_x_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_, lean_object* v_h__3_618_){
_start:
{
uint8_t v_x_48__boxed_619_; lean_object* v_res_620_; 
v_x_48__boxed_619_ = lean_unbox(v_x_615_);
v_res_620_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_614_, v_x_48__boxed_619_, v_h__1_616_, v_h__2_617_, v_h__3_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_621_){
_start:
{
lean_object* v_fst_622_; 
v_fst_622_ = lean_ctor_get(v_x_621_, 0);
lean_inc(v_fst_622_);
return v_fst_622_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_lexOrd___redArg___lam__0(v_x_623_);
lean_dec_ref(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_625_){
_start:
{
lean_object* v_snd_626_; 
v_snd_626_ = lean_ctor_get(v_x_625_, 1);
lean_inc(v_snd_626_);
return v_snd_626_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_lexOrd___redArg___lam__1(v_x_627_);
lean_dec_ref(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_631_, lean_object* v_inst_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___f_633_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_634_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_635_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_635_, 0, lean_box(0));
lean_closure_set(v___x_635_, 1, lean_box(0));
lean_closure_set(v___x_635_, 2, v_inst_631_);
lean_closure_set(v___x_635_, 3, v___f_633_);
v___x_636_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_636_, 0, lean_box(0));
lean_closure_set(v___x_636_, 1, lean_box(0));
lean_closure_set(v___x_636_, 2, v_inst_632_);
lean_closure_set(v___x_636_, 3, v___f_634_);
v___x_637_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_637_, 0, lean_box(0));
lean_closure_set(v___x_637_, 1, lean_box(0));
lean_closure_set(v___x_637_, 2, v___x_635_);
lean_closure_set(v___x_637_, 3, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_inst_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_lexOrd___redArg(v_inst_640_, v_inst_641_);
return v___x_642_;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_apply_2(v_inst_643_, v_a_644_, v_b_645_);
v___x_647_ = lean_unbox(v___x_646_);
if (v___x_647_ == 1)
{
uint8_t v___x_648_; 
v___x_648_ = 1;
return v___x_648_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_650_, lean_object* v_a_651_, lean_object* v_b_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l_beqOfOrd___redArg___lam__0(v_inst_650_, v_a_651_, v_b_652_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_655_){
_start:
{
lean_object* v___f_656_; 
v___f_656_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_656_, 0, v_inst_655_);
return v___f_656_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___f_659_; 
v___f_659_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_659_, 0, v_inst_658_);
return v___f_659_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___redArg(){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___redArg___boxed(lean_object* v___dummy_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_ltOfOrd___redArg();
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_664_, lean_object* v_inst_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_box(0);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_ltOfOrd(v_00_u03b1_667_, v_inst_668_);
lean_dec_ref(v_inst_668_);
return v_res_669_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_670_, lean_object* v_a_671_, lean_object* v_b_672_){
_start:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_apply_2(v_inst_670_, v_a_671_, v_b_672_);
v___x_674_ = lean_unbox(v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 1;
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_instDecidableRelLt___redArg(v_inst_677_, v_a_678_, v_b_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_682_, lean_object* v_inst_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_apply_2(v_inst_683_, v_a_684_, v_b_685_);
v___x_687_ = lean_unbox(v___x_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = 1;
return v___x_688_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_690_, lean_object* v_inst_691_, lean_object* v_a_692_, lean_object* v_b_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_instDecidableRelLt(v_00_u03b1_690_, v_inst_691_, v_a_692_, v_b_693_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___redArg(){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___redArg___boxed(lean_object* v___dummy_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_leOfOrd___redArg();
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_box(0);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_leOfOrd(v_00_u03b1_703_, v_inst_704_);
lean_dec_ref(v_inst_704_);
return v_res_705_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_apply_2(v_inst_706_, v_x_707_, v_x_708_);
v___x_710_ = lean_unbox(v___x_709_);
if (v___x_710_ == 2)
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 1;
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_713_, lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_instDecidableRelLe___redArg(v_inst_713_, v_x_714_, v_x_715_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_718_, lean_object* v_inst_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_apply_2(v_inst_719_, v_x_720_, v_x_721_);
v___x_723_ = lean_unbox(v___x_722_);
if (v___x_723_ == 2)
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = 1;
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_726_, lean_object* v_inst_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_instDecidableRelLe(v_00_u03b1_726_, v_inst_727_, v_x_728_, v_x_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_732_){
_start:
{
lean_object* v___f_733_; 
v___f_733_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v_ord_732_);
return v___f_733_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_734_, lean_object* v_ord_735_){
_start:
{
lean_object* v___f_736_; 
v___f_736_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_736_, 0, v_ord_735_);
return v___f_736_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___redArg(){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_box(0);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___redArg___boxed(lean_object* v___dummy_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Ord_toLT___redArg();
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_741_, lean_object* v_ord_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(0);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_744_, lean_object* v_ord_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Ord_toLT(v_00_u03b1_744_, v_ord_745_);
lean_dec_ref(v_ord_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___redArg(){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___redArg___boxed(lean_object* v___dummy_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Ord_toLE___redArg();
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_751_, lean_object* v_ord_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_box(0);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_754_, lean_object* v_ord_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Ord_toLE(v_00_u03b1_754_, v_ord_755_);
lean_dec_ref(v_ord_755_);
return v_res_756_;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_757_, lean_object* v_x_758_, lean_object* v_y_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_apply_2(v_ord_757_, v_y_759_, v_x_758_);
v___x_761_ = lean_unbox(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_762_, lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Ord_opposite___redArg___lam__0(v_ord_762_, v_x_763_, v_y_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_767_){
_start:
{
lean_object* v___f_768_; 
v___f_768_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_768_, 0, v_ord_767_);
return v___f_768_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_769_, lean_object* v_ord_770_){
_start:
{
lean_object* v___f_771_; 
v___f_771_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_771_, 0, v_ord_770_);
return v___f_771_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_772_, lean_object* v_f_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_774_, 0, lean_box(0));
lean_closure_set(v___x_774_, 1, lean_box(0));
lean_closure_set(v___x_774_, 2, v_x_772_);
lean_closure_set(v___x_774_, 3, v_f_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_775_, lean_object* v_00_u03b1_776_, lean_object* v_x_777_, lean_object* v_f_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_779_, 0, lean_box(0));
lean_closure_set(v___x_779_, 1, lean_box(0));
lean_closure_set(v___x_779_, 2, v_x_777_);
lean_closure_set(v___x_779_, 3, v_f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_lexOrd___redArg(v_x_780_, v_x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_lexOrd___redArg(v_x_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_788_, lean_object* v_ord_u2082_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_790_, 0, lean_box(0));
lean_closure_set(v___x_790_, 1, lean_box(0));
lean_closure_set(v___x_790_, 2, v_ord_u2081_788_);
lean_closure_set(v___x_790_, 3, v_ord_u2082_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_791_, lean_object* v_ord_u2081_792_, lean_object* v_ord_u2082_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_794_, 0, lean_box(0));
lean_closure_set(v___x_794_, 1, lean_box(0));
lean_closure_set(v___x_794_, 2, v_ord_u2081_792_);
lean_closure_set(v___x_794_, 3, v_ord_u2082_793_);
return v___x_794_;
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
