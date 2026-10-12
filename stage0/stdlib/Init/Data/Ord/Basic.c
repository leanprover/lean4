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
lean_object* l_Ordering_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Ordering_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Ordering_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Ordering_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Ordering_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Ordering_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Ordering_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Ordering_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Ordering_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Ordering_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg(lean_object* v_lt_24_){
_start:
{
lean_inc(v_lt_24_);
return v_lt_24_;
}
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___redArg___boxed(lean_object* v_lt_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Ordering_lt_elim___redArg(v_lt_25_);
lean_dec(v_lt_25_);
return v_res_26_;
}
}
lean_object* l_Ordering_lt_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_lt_30_){
_start:
{
lean_inc(v_lt_30_);
return v_lt_30_;
}
}
LEAN_EXPORT void l_Ordering_lt_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_lt_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Ordering_lt_elim(lean_box(0), v_t_28_, lean_box(0), v_lt_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Ordering_lt_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_lt_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Ordering_lt_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_lt_35_);
lean_dec(v_lt_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg(lean_object* v_eq_38_){
_start:
{
lean_inc(v_eq_38_);
return v_eq_38_;
}
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___redArg___boxed(lean_object* v_eq_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Ordering_eq_elim___redArg(v_eq_39_);
lean_dec(v_eq_39_);
return v_res_40_;
}
}
lean_object* l_Ordering_eq_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_eq_44_){
_start:
{
lean_inc(v_eq_44_);
return v_eq_44_;
}
}
LEAN_EXPORT void l_Ordering_eq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_eq_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Ordering_eq_elim(lean_box(0), v_t_42_, lean_box(0), v_eq_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Ordering_eq_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_eq_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Ordering_eq_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_eq_49_);
lean_dec(v_eq_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg(lean_object* v_gt_52_){
_start:
{
lean_inc(v_gt_52_);
return v_gt_52_;
}
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___redArg___boxed(lean_object* v_gt_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Ordering_gt_elim___redArg(v_gt_53_);
lean_dec(v_gt_53_);
return v_res_54_;
}
}
lean_object* l_Ordering_gt_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_gt_58_){
_start:
{
lean_inc(v_gt_58_);
return v_gt_58_;
}
}
LEAN_EXPORT void l_Ordering_gt_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_gt_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Ordering_gt_elim(lean_box(0), v_t_56_, lean_box(0), v_gt_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Ordering_gt_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_gt_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Ordering_gt_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_gt_63_);
lean_dec(v_gt_63_);
return v_res_65_;
}
}
static uint8_t _init_l_instInhabitedOrdering_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_instInhabitedOrdering(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
uint8_t l_Ordering_ofNat(lean_object* v_n_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_le(v_n_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_dec_le(v_n_68_, v___x_71_);
if (v___x_72_ == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 2;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
}
LEAN_EXPORT void l_Ordering_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_68_ = stack[0].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Ordering_ofNat(v_n_68_);
stack->m_num = v_res_76_;
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
uint8_t l_instDecidableEqOrdering(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_82_ = lean_box(v_x_80_);
v___x_83_ = lean_obj_tag_nat(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_box(v_y_81_);
v___x_85_ = lean_obj_tag_nat(v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_nat_dec_eq(v___x_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_instDecidableEqOrdering_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_80_ = stack[0].m_num;
uint8_t v_y_81_ = stack[1].m_num;
uint8_t v_res_87_;
v_res_87_ = l_instDecidableEqOrdering(v_x_80_, v_y_81_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_instDecidableEqOrdering___boxed(lean_object* v_x_88_, lean_object* v_y_89_){
_start:
{
uint8_t v_x_23__boxed_90_; uint8_t v_y_24__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_23__boxed_90_ = lean_unbox(v_x_88_);
v_y_24__boxed_91_ = lean_unbox(v_y_89_);
v_res_92_ = l_instDecidableEqOrdering(v_x_23__boxed_90_, v_y_24__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__6(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_instReprOrdering_repr___closed__7(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_to_int(v___x_105_);
return v___x_106_;
}
}
lean_object* l_instReprOrdering_repr(uint8_t v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v___y_110_; lean_object* v___y_117_; lean_object* v___y_124_; 
switch(v_x_107_)
{
case 0:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = lean_nat_dec_le(v___x_130_, v_prec_108_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_110_ = v___x_132_;
goto v___jp_109_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_110_ = v___x_133_;
goto v___jp_109_;
}
}
case 1:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = lean_nat_dec_le(v___x_134_, v_prec_108_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_117_ = v___x_136_;
goto v___jp_116_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_117_ = v___x_137_;
goto v___jp_116_;
}
}
default: 
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_108_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_instReprOrdering_repr___closed__6, &l_instReprOrdering_repr___closed__6_once, _init_l_instReprOrdering_repr___closed__6);
v___y_124_ = v___x_140_;
goto v___jp_123_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_instReprOrdering_repr___closed__7, &l_instReprOrdering_repr___closed__7_once, _init_l_instReprOrdering_repr___closed__7);
v___y_124_ = v___x_141_;
goto v___jp_123_;
}
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l_instReprOrdering_repr___closed__1));
lean_inc(v___y_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_108_);
return v___x_115_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_instReprOrdering_repr___closed__3));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_108_);
return v___x_122_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = ((lean_object*)(l_instReprOrdering_repr___closed__5));
lean_inc(v___y_124_);
v___x_126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_126_, 0, v___y_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = l_Repr_addAppParen(v___x_128_, v_prec_108_);
return v___x_129_;
}
}
}
LEAN_EXPORT void l_instReprOrdering_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_107_ = stack[0].m_num;
lean_object* v_prec_108_ = stack[1].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_instReprOrdering_repr(v_x_107_, v_prec_108_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_instReprOrdering_repr___boxed(lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
uint8_t v_x_171__boxed_145_; lean_object* v_res_146_; 
v_x_171__boxed_145_ = lean_unbox(v_x_143_);
v_res_146_ = l_instReprOrdering_repr(v_x_171__boxed_145_, v_prec_144_);
lean_dec(v_prec_144_);
return v_res_146_;
}
}
uint8_t l_Ordering_swap(uint8_t v_x_149_){
_start:
{
switch(v_x_149_)
{
case 0:
{
uint8_t v___x_150_; 
v___x_150_ = 2;
return v___x_150_;
}
case 1:
{
return v_x_149_;
}
default: 
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
}
}
LEAN_EXPORT void l_Ordering_swap_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_149_ = stack[0].m_num;
uint8_t v_res_152_;
v_res_152_ = l_Ordering_swap(v_x_149_);
stack->m_num = v_res_152_;
}
LEAN_EXPORT lean_object* l_Ordering_swap___boxed(lean_object* v_x_153_){
_start:
{
uint8_t v_x_25__boxed_154_; uint8_t v_res_155_; lean_object* v_r_156_; 
v_x_25__boxed_154_ = lean_unbox(v_x_153_);
v_res_155_ = l_Ordering_swap(v_x_25__boxed_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
uint8_t l_Ordering_isEq(uint8_t v_x_157_){
_start:
{
if (v_x_157_ == 1)
{
uint8_t v___x_158_; 
v___x_158_ = 1;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
}
LEAN_EXPORT void l_Ordering_isEq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_157_ = stack[0].m_num;
uint8_t v_res_160_;
v_res_160_ = l_Ordering_isEq(v_x_157_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l_Ordering_isEq___boxed(lean_object* v_x_161_){
_start:
{
uint8_t v_x_17__boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_x_17__boxed_162_ = lean_unbox(v_x_161_);
v_res_163_ = l_Ordering_isEq(v_x_17__boxed_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
uint8_t l_Ordering_isNe(uint8_t v_x_165_){
_start:
{
if (v_x_165_ == 1)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
}
}
LEAN_EXPORT void l_Ordering_isNe_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_165_ = stack[0].m_num;
uint8_t v_res_168_;
v_res_168_ = l_Ordering_isNe(v_x_165_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Ordering_isNe___boxed(lean_object* v_x_169_){
_start:
{
uint8_t v_x_17__boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_x_17__boxed_170_ = lean_unbox(v_x_169_);
v_res_171_ = l_Ordering_isNe(v_x_17__boxed_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
uint8_t l_Ordering_isLE(uint8_t v_x_173_){
_start:
{
if (v_x_173_ == 2)
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
else
{
uint8_t v___x_175_; 
v___x_175_ = 1;
return v___x_175_;
}
}
}
LEAN_EXPORT void l_Ordering_isLE_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_173_ = stack[0].m_num;
uint8_t v_res_176_;
v_res_176_ = l_Ordering_isLE(v_x_173_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Ordering_isLE___boxed(lean_object* v_x_177_){
_start:
{
uint8_t v_x_17__boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_17__boxed_178_ = lean_unbox(v_x_177_);
v_res_179_ = l_Ordering_isLE(v_x_17__boxed_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
uint8_t l_Ordering_isLT(uint8_t v_x_181_){
_start:
{
if (v_x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = 1;
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
}
}
LEAN_EXPORT void l_Ordering_isLT_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_181_ = stack[0].m_num;
uint8_t v_res_184_;
v_res_184_ = l_Ordering_isLT(v_x_181_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_Ordering_isLT___boxed(lean_object* v_x_185_){
_start:
{
uint8_t v_x_17__boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_x_17__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Ordering_isLT(v_x_17__boxed_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
uint8_t l_Ordering_isGT(uint8_t v_x_189_){
_start:
{
if (v_x_189_ == 2)
{
uint8_t v___x_190_; 
v___x_190_ = 1;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
}
LEAN_EXPORT void l_Ordering_isGT_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_189_ = stack[0].m_num;
uint8_t v_res_192_;
v_res_192_ = l_Ordering_isGT(v_x_189_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_Ordering_isGT___boxed(lean_object* v_x_193_){
_start:
{
uint8_t v_x_17__boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_x_17__boxed_194_ = lean_unbox(v_x_193_);
v_res_195_ = l_Ordering_isGT(v_x_17__boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
uint8_t l_Ordering_isGE(uint8_t v_x_197_){
_start:
{
if (v_x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 1;
return v___x_199_;
}
}
}
LEAN_EXPORT void l_Ordering_isGE_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_197_ = stack[0].m_num;
uint8_t v_res_200_;
v_res_200_ = l_Ordering_isGE(v_x_197_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Ordering_isGE___boxed(lean_object* v_x_201_){
_start:
{
uint8_t v_x_17__boxed_202_; uint8_t v_res_203_; lean_object* v_r_204_; 
v_x_17__boxed_202_ = lean_unbox(v_x_201_);
v_res_203_ = l_Ordering_isGE(v_x_17__boxed_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_205_){
_start:
{
uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = 0;
v___x_207_ = lean_box(v___x_206_);
lean_inc_ref(v_inst_205_);
v___x_208_ = lean_apply_1(v_inst_205_, v___x_207_);
v___x_209_ = lean_unbox(v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
lean_dec_ref(v_inst_205_);
v___x_210_ = lean_unbox(v___x_208_);
return v___x_210_;
}
else
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_211_ = 1;
v___x_212_ = lean_box(v___x_211_);
lean_inc_ref(v_inst_205_);
v___x_213_ = lean_apply_1(v_inst_205_, v___x_212_);
v___x_214_ = lean_unbox(v___x_213_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; 
lean_dec_ref(v_inst_205_);
v___x_215_ = lean_unbox(v___x_213_);
return v___x_215_;
}
else
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_216_ = 2;
v___x_217_ = lean_box(v___x_216_);
v___x_218_ = lean_apply_1(v_inst_205_, v___x_217_);
v___x_219_ = lean_unbox(v___x_218_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT void l_Ordering_instDecidableForallOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_205_ = stack[0].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_205_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* v_p_224_, lean_object* v_inst_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Ordering_instDecidableForallOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_225_ = stack[1].m_obj;
uint8_t v_res_227_;
v_res_227_ = l_Ordering_instDecidableForallOfDecidablePred(lean_box(0), v_inst_225_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_228_, lean_object* v_inst_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_228_, v_inst_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_232_){
_start:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_233_ = 0;
v___x_234_ = lean_box(v___x_233_);
lean_inc_ref(v_inst_232_);
v___x_235_ = lean_apply_1(v_inst_232_, v___x_234_);
v___x_236_ = lean_unbox(v___x_235_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_237_ = 1;
v___x_238_ = lean_box(v___x_237_);
lean_inc_ref(v_inst_232_);
v___x_239_ = lean_apply_1(v_inst_232_, v___x_238_);
v___x_240_ = lean_unbox(v___x_239_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_241_ = 2;
v___x_242_ = lean_box(v___x_241_);
v___x_243_ = lean_apply_1(v_inst_232_, v___x_242_);
v___x_244_ = lean_unbox(v___x_243_);
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
lean_dec_ref(v_inst_232_);
v___x_245_ = lean_unbox(v___x_239_);
return v___x_245_;
}
}
else
{
uint8_t v___x_246_; 
lean_dec_ref(v_inst_232_);
v___x_246_ = lean_unbox(v___x_235_);
return v___x_246_;
}
}
}
LEAN_EXPORT void l_Ordering_instDecidableExistsOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_232_ = stack[0].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_232_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* v_p_251_, lean_object* v_inst_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_252_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Ordering_instDecidableExistsOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_252_ = stack[1].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Ordering_instDecidableExistsOfDecidablePred(lean_box(0), v_inst_252_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_255_, lean_object* v_inst_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_255_, v_inst_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_){
_start:
{
if (v_a_259_ == 1)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__2_261_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v_h__1_260_, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__1_260_);
v___x_264_ = lean_box(v_a_259_);
v___x_265_ = lean_apply_2(v_h__2_261_, v___x_264_, lean_box(0));
return v___x_265_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_259_ = stack[0].m_num;
lean_object* v_h__1_260_ = stack[1].m_obj;
lean_object* v_h__2_261_ = stack[2].m_obj;
lean_object* v_res_266_;
v_res_266_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_259_, v_h__1_260_, v_h__2_261_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
uint8_t v_a_13__boxed_270_; lean_object* v_res_271_; 
v_a_13__boxed_270_ = lean_unbox(v_a_267_);
v_res_271_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_270_, v_h__1_268_, v_h__2_269_);
return v_res_271_;
}
}
lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* v_motive_272_, uint8_t v_a_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
if (v_a_273_ == 1)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_h__2_275_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v_h__1_274_, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_274_);
v___x_278_ = lean_box(v_a_273_);
v___x_279_ = lean_apply_2(v_h__2_275_, v___x_278_, lean_box(0));
return v___x_279_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_273_ = stack[1].m_num;
lean_object* v_h__1_274_ = stack[2].m_obj;
lean_object* v_h__2_275_ = stack[3].m_obj;
lean_object* v_res_280_;
v_res_280_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_box(0), v_a_273_, v_h__1_274_, v_h__2_275_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_281_, lean_object* v_a_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
uint8_t v_a_30__boxed_285_; lean_object* v_res_286_; 
v_a_30__boxed_285_ = lean_unbox(v_a_282_);
v_res_286_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(v_motive_281_, v_a_30__boxed_285_, v_h__1_283_, v_h__2_284_);
return v_res_286_;
}
}
uint8_t l_compareOfLessAndEq___redArg(lean_object* v_x_287_, lean_object* v_y_288_, uint8_t v_inst_289_, lean_object* v_inst_290_){
_start:
{
if (v_inst_289_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_apply_2(v_inst_290_, v_x_287_, v_y_288_);
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
lean_dec(v_y_288_);
lean_dec(v_x_287_);
v___x_295_ = 0;
return v___x_295_;
}
}
}
LEAN_EXPORT void l_compareOfLessAndEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_287_ = stack[0].m_obj;
lean_object* v_y_288_ = stack[1].m_obj;
uint8_t v_inst_289_ = stack[2].m_num;
lean_object* v_inst_290_ = stack[3].m_obj;
uint8_t v_res_296_;
v_res_296_ = l_compareOfLessAndEq___redArg(v_x_287_, v_y_288_, v_inst_289_, v_inst_290_);
stack->m_num = v_res_296_;
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* v_x_297_, lean_object* v_y_298_, lean_object* v_inst_299_, lean_object* v_inst_300_){
_start:
{
uint8_t v_inst_21__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_inst_21__boxed_301_ = lean_unbox(v_inst_299_);
v_res_302_ = l_compareOfLessAndEq___redArg(v_x_297_, v_y_298_, v_inst_21__boxed_301_, v_inst_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
uint8_t l_compareOfLessAndEq(lean_object* v_00_u03b1_304_, lean_object* v_x_305_, lean_object* v_y_306_, lean_object* v_inst_307_, uint8_t v_inst_308_, lean_object* v_inst_309_){
_start:
{
if (v_inst_308_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_apply_2(v_inst_309_, v_x_305_, v_y_306_);
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
lean_dec(v_y_306_);
lean_dec(v_x_305_);
v___x_314_ = 0;
return v___x_314_;
}
}
}
LEAN_EXPORT void l_compareOfLessAndEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_305_ = stack[1].m_obj;
lean_object* v_y_306_ = stack[2].m_obj;
lean_object* v_inst_307_ = stack[3].m_obj;
uint8_t v_inst_308_ = stack[4].m_num;
lean_object* v_inst_309_ = stack[5].m_obj;
uint8_t v_res_315_;
v_res_315_ = l_compareOfLessAndEq(lean_box(0), v_x_305_, v_y_306_, v_inst_307_, v_inst_308_, v_inst_309_);
stack->m_num = v_res_315_;
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* v_00_u03b1_316_, lean_object* v_x_317_, lean_object* v_y_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_){
_start:
{
uint8_t v_inst_47__boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_inst_47__boxed_322_ = lean_unbox(v_inst_320_);
v_res_323_ = l_compareOfLessAndEq(v_00_u03b1_316_, v_x_317_, v_y_318_, v_inst_319_, v_inst_47__boxed_322_, v_inst_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
uint8_t l_compareOfLessAndBEq___redArg(lean_object* v_x_325_, lean_object* v_y_326_, uint8_t v_inst_327_, lean_object* v_inst_328_){
_start:
{
if (v_inst_327_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_apply_2(v_inst_328_, v_x_325_, v_y_326_);
v___x_330_ = lean_unbox(v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = 2;
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 1;
return v___x_332_;
}
}
else
{
uint8_t v___x_333_; 
lean_dec_ref(v_inst_328_);
lean_dec(v_y_326_);
lean_dec(v_x_325_);
v___x_333_ = 0;
return v___x_333_;
}
}
}
LEAN_EXPORT void l_compareOfLessAndBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_325_ = stack[0].m_obj;
lean_object* v_y_326_ = stack[1].m_obj;
uint8_t v_inst_327_ = stack[2].m_num;
lean_object* v_inst_328_ = stack[3].m_obj;
uint8_t v_res_334_;
v_res_334_ = l_compareOfLessAndBEq___redArg(v_x_325_, v_y_326_, v_inst_327_, v_inst_328_);
stack->m_num = v_res_334_;
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* v_x_335_, lean_object* v_y_336_, lean_object* v_inst_337_, lean_object* v_inst_338_){
_start:
{
uint8_t v_inst_28__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_inst_28__boxed_339_ = lean_unbox(v_inst_337_);
v_res_340_ = l_compareOfLessAndBEq___redArg(v_x_335_, v_y_336_, v_inst_28__boxed_339_, v_inst_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
uint8_t l_compareOfLessAndBEq(lean_object* v_00_u03b1_342_, lean_object* v_x_343_, lean_object* v_y_344_, lean_object* v_inst_345_, uint8_t v_inst_346_, lean_object* v_inst_347_){
_start:
{
if (v_inst_346_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_apply_2(v_inst_347_, v_x_343_, v_y_344_);
v___x_349_ = lean_unbox(v___x_348_);
if (v___x_349_ == 0)
{
uint8_t v___x_350_; 
v___x_350_ = 2;
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 1;
return v___x_351_;
}
}
else
{
uint8_t v___x_352_; 
lean_dec_ref(v_inst_347_);
lean_dec(v_y_344_);
lean_dec(v_x_343_);
v___x_352_ = 0;
return v___x_352_;
}
}
}
LEAN_EXPORT void l_compareOfLessAndBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_343_ = stack[1].m_obj;
lean_object* v_y_344_ = stack[2].m_obj;
lean_object* v_inst_345_ = stack[3].m_obj;
uint8_t v_inst_346_ = stack[4].m_num;
lean_object* v_inst_347_ = stack[5].m_obj;
uint8_t v_res_353_;
v_res_353_ = l_compareOfLessAndBEq(lean_box(0), v_x_343_, v_y_344_, v_inst_345_, v_inst_346_, v_inst_347_);
stack->m_num = v_res_353_;
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* v_00_u03b1_354_, lean_object* v_x_355_, lean_object* v_y_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_){
_start:
{
uint8_t v_inst_54__boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v_inst_54__boxed_360_ = lean_unbox(v_inst_358_);
v_res_361_ = l_compareOfLessAndBEq(v_00_u03b1_354_, v_x_355_, v_y_356_, v_inst_357_, v_inst_54__boxed_360_, v_inst_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
uint8_t l_compareLex___redArg(lean_object* v_cmp_u2081_363_, lean_object* v_cmp_u2082_364_, lean_object* v_a_365_, lean_object* v_b_366_){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
lean_inc(v_b_366_);
lean_inc(v_a_365_);
v___x_367_ = lean_apply_2(v_cmp_u2081_363_, v_a_365_, v_b_366_);
v___x_368_ = lean_unbox(v___x_367_);
if (v___x_368_ == 1)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_apply_2(v_cmp_u2082_364_, v_a_365_, v_b_366_);
v___x_370_ = lean_unbox(v___x_369_);
return v___x_370_;
}
else
{
uint8_t v___x_371_; 
lean_dec(v_b_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_cmp_u2082_364_);
v___x_371_ = lean_unbox(v___x_367_);
return v___x_371_;
}
}
}
LEAN_EXPORT void l_compareLex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_u2081_363_ = stack[0].m_obj;
lean_object* v_cmp_u2082_364_ = stack[1].m_obj;
lean_object* v_a_365_ = stack[2].m_obj;
lean_object* v_b_366_ = stack[3].m_obj;
uint8_t v_res_372_;
v_res_372_ = l_compareLex___redArg(v_cmp_u2081_363_, v_cmp_u2082_364_, v_a_365_, v_b_366_);
stack->m_num = v_res_372_;
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* v_cmp_u2081_373_, lean_object* v_cmp_u2082_374_, lean_object* v_a_375_, lean_object* v_b_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_compareLex___redArg(v_cmp_u2081_373_, v_cmp_u2082_374_, v_a_375_, v_b_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
uint8_t l_compareLex(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_cmp_u2081_381_, lean_object* v_cmp_u2082_382_, lean_object* v_a_383_, lean_object* v_b_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
lean_inc(v_b_384_);
lean_inc(v_a_383_);
v___x_385_ = lean_apply_2(v_cmp_u2081_381_, v_a_383_, v_b_384_);
v___x_386_ = lean_unbox(v___x_385_);
if (v___x_386_ == 1)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = lean_apply_2(v_cmp_u2082_382_, v_a_383_, v_b_384_);
v___x_388_ = lean_unbox(v___x_387_);
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
lean_dec(v_b_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_cmp_u2082_382_);
v___x_389_ = lean_unbox(v___x_385_);
return v___x_389_;
}
}
}
LEAN_EXPORT void l_compareLex_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_u2081_381_ = stack[2].m_obj;
lean_object* v_cmp_u2082_382_ = stack[3].m_obj;
lean_object* v_a_383_ = stack[4].m_obj;
lean_object* v_b_384_ = stack[5].m_obj;
uint8_t v_res_390_;
v_res_390_ = l_compareLex(lean_box(0), lean_box(0), v_cmp_u2081_381_, v_cmp_u2082_382_, v_a_383_, v_b_384_);
stack->m_num = v_res_390_;
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_cmp_u2081_393_, lean_object* v_cmp_u2082_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_compareLex(v_00_u03b1_391_, v_00_u03b2_392_, v_cmp_u2081_393_, v_cmp_u2082_394_, v_a_395_, v_b_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
uint8_t l_compareOn___redArg(lean_object* v_ord_399_, lean_object* v_f_400_, lean_object* v_x_401_, lean_object* v_y_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
lean_inc(v_f_400_);
v___x_403_ = lean_apply_1(v_f_400_, v_x_401_);
v___x_404_ = lean_apply_1(v_f_400_, v_y_402_);
v___x_405_ = lean_apply_2(v_ord_399_, v___x_403_, v___x_404_);
v___x_406_ = lean_unbox(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT void l_compareOn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ord_399_ = stack[0].m_obj;
lean_object* v_f_400_ = stack[1].m_obj;
lean_object* v_x_401_ = stack[2].m_obj;
lean_object* v_y_402_ = stack[3].m_obj;
uint8_t v_res_407_;
v_res_407_ = l_compareOn___redArg(v_ord_399_, v_f_400_, v_x_401_, v_y_402_);
stack->m_num = v_res_407_;
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* v_ord_408_, lean_object* v_f_409_, lean_object* v_x_410_, lean_object* v_y_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_compareOn___redArg(v_ord_408_, v_f_409_, v_x_410_, v_y_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
uint8_t l_compareOn(lean_object* v_00_u03b2_414_, lean_object* v_00_u03b1_415_, lean_object* v_ord_416_, lean_object* v_f_417_, lean_object* v_x_418_, lean_object* v_y_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
lean_inc(v_f_417_);
v___x_420_ = lean_apply_1(v_f_417_, v_x_418_);
v___x_421_ = lean_apply_1(v_f_417_, v_y_419_);
v___x_422_ = lean_apply_2(v_ord_416_, v___x_420_, v___x_421_);
v___x_423_ = lean_unbox(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT void l_compareOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_ord_416_ = stack[2].m_obj;
lean_object* v_f_417_ = stack[3].m_obj;
lean_object* v_x_418_ = stack[4].m_obj;
lean_object* v_y_419_ = stack[5].m_obj;
uint8_t v_res_424_;
v_res_424_ = l_compareOn(lean_box(0), lean_box(0), v_ord_416_, v_f_417_, v_x_418_, v_y_419_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* v_00_u03b2_425_, lean_object* v_00_u03b1_426_, lean_object* v_ord_427_, lean_object* v_f_428_, lean_object* v_x_429_, lean_object* v_y_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_compareOn(v_00_u03b2_425_, v_00_u03b1_426_, v_ord_427_, v_f_428_, v_x_429_, v_y_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
uint8_t l_instOrdNat___lam__0(lean_object* v_x_433_, lean_object* v_y_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_nat_dec_lt(v_x_433_, v_y_434_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_eq(v_x_433_, v_y_434_);
if (v___x_436_ == 0)
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
else
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
}
}
LEAN_EXPORT void l_instOrdNat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_433_ = stack[0].m_obj;
lean_object* v_y_434_ = stack[1].m_obj;
uint8_t v_res_440_;
v_res_440_ = l_instOrdNat___lam__0(v_x_433_, v_y_434_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* v_x_441_, lean_object* v_y_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_instOrdNat___lam__0(v_x_441_, v_y_442_);
lean_dec(v_y_442_);
lean_dec(v_x_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
uint8_t l_instOrdInt___lam__0(lean_object* v_x_447_, lean_object* v_y_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_int_dec_lt(v_x_447_, v_y_448_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = lean_int_dec_eq(v_x_447_, v_y_448_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = 2;
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 1;
return v___x_452_;
}
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 0;
return v___x_453_;
}
}
}
LEAN_EXPORT void l_instOrdInt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_447_ = stack[0].m_obj;
lean_object* v_y_448_ = stack[1].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_instOrdInt___lam__0(v_x_447_, v_y_448_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* v_x_455_, lean_object* v_y_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_instOrdInt___lam__0(v_x_455_, v_y_456_);
lean_dec(v_y_456_);
lean_dec(v_x_455_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
uint8_t l_instOrdBool___lam__0(uint8_t v_x_461_, uint8_t v_x_462_){
_start:
{
if (v_x_461_ == 0)
{
if (v_x_462_ == 1)
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = 1;
return v___x_464_;
}
}
else
{
if (v_x_462_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 2;
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 1;
return v___x_466_;
}
}
}
}
LEAN_EXPORT void l_instOrdBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_461_ = stack[0].m_num;
uint8_t v_x_462_ = stack[1].m_num;
uint8_t v_res_467_;
v_res_467_ = l_instOrdBool___lam__0(v_x_461_, v_x_462_);
stack->m_num = v_res_467_;
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_x_39__boxed_470_; uint8_t v_x_40__boxed_471_; uint8_t v_res_472_; lean_object* v_r_473_; 
v_x_39__boxed_470_ = lean_unbox(v_x_468_);
v_x_40__boxed_471_ = lean_unbox(v_x_469_);
v_res_472_ = l_instOrdBool___lam__0(v_x_39__boxed_470_, v_x_40__boxed_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
lean_object* l_instOrdFin___redArg(){
_start:
{
lean_object* v___f_477_; 
v___f_477_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_477_;
}
}
LEAN_EXPORT void l_instOrdFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_478_;
v_res_478_ = l_instOrdFin___redArg();
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_instOrdFin___redArg___boxed(lean_object* v___dummy_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_instOrdFin___redArg();
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* v_n_481_){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* v_n_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_instOrdFin(v_n_483_);
lean_dec(v_n_483_);
return v_res_484_;
}
}
uint8_t l_instOrdChar___lam__0(uint32_t v_x_485_, uint32_t v_y_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = lean_uint32_dec_lt(v_x_485_, v_y_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = lean_uint32_dec_eq(v_x_485_, v_y_486_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 2;
return v___x_489_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = 1;
return v___x_490_;
}
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
}
}
LEAN_EXPORT void l_instOrdChar___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_485_ = stack[0].m_num;
uint32_t v_y_486_ = stack[1].m_num;
uint8_t v_res_492_;
v_res_492_ = l_instOrdChar___lam__0(v_x_485_, v_y_486_);
stack->m_num = v_res_492_;
}
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* v_x_493_, lean_object* v_y_494_){
_start:
{
uint32_t v_x_boxed_495_; uint32_t v_y_boxed_496_; uint8_t v_res_497_; lean_object* v_r_498_; 
v_x_boxed_495_ = lean_unbox_uint32(v_x_493_);
lean_dec(v_x_493_);
v_y_boxed_496_ = lean_unbox_uint32(v_y_494_);
lean_dec(v_y_494_);
v_res_497_ = l_instOrdChar___lam__0(v_x_boxed_495_, v_y_boxed_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
uint8_t l_instOrdBitVec___redArg___lam__0(lean_object* v_x_501_, lean_object* v_y_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_add(v_x_501_, v___x_503_);
v___x_505_ = lean_nat_dec_le(v___x_504_, v_y_502_);
lean_dec(v___x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
v___x_506_ = lean_nat_dec_eq(v_x_501_, v_y_502_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 2;
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = 1;
return v___x_508_;
}
}
else
{
uint8_t v___x_509_; 
v___x_509_ = 0;
return v___x_509_;
}
}
}
LEAN_EXPORT void l_instOrdBitVec___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_501_ = stack[0].m_obj;
lean_object* v_y_502_ = stack[1].m_obj;
uint8_t v_res_510_;
v_res_510_ = l_instOrdBitVec___redArg___lam__0(v_x_501_, v_y_502_);
stack->m_num = v_res_510_;
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___lam__0___boxed(lean_object* v_x_511_, lean_object* v_y_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_instOrdBitVec___redArg___lam__0(v_x_511_, v_y_512_);
lean_dec(v_y_512_);
lean_dec(v_x_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
lean_object* l_instOrdBitVec___redArg(){
_start:
{
lean_object* v___f_517_; 
v___f_517_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_517_;
}
}
LEAN_EXPORT void l_instOrdBitVec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_518_;
v_res_518_ = l_instOrdBitVec___redArg();
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_instOrdBitVec___redArg___boxed(lean_object* v___dummy_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_instOrdBitVec___redArg();
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_521_){
_start:
{
lean_object* v___f_522_; 
v___f_522_ = ((lean_object*)(l_instOrdBitVec___redArg___closed__0));
return v___f_522_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_instOrdBitVec(v_n_523_);
lean_dec(v_n_523_);
return v_res_524_;
}
}
uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_dec_ref(v_inst_525_);
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 1;
return v___x_528_;
}
else
{
uint8_t v___x_529_; 
lean_dec_ref_known(v_x_527_, 1);
v___x_529_ = 0;
return v___x_529_;
}
}
else
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_530_; 
lean_dec_ref_known(v_x_526_, 1);
lean_dec_ref(v_inst_525_);
v___x_530_ = 2;
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v_val_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_val_531_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v_x_526_, 1);
v_val_532_ = lean_ctor_get(v_x_527_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v_x_527_, 1);
v___x_533_ = lean_apply_2(v_inst_525_, v_val_531_, v_val_532_);
v___x_534_ = lean_unbox(v___x_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT void l_instOrdOption___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_525_ = stack[0].m_obj;
lean_object* v_x_526_ = stack[1].m_obj;
lean_object* v_x_527_ = stack[2].m_obj;
uint8_t v_res_535_;
v_res_535_ = l_instOrdOption___redArg___lam__0(v_inst_525_, v_x_526_, v_x_527_);
stack->m_num = v_res_535_;
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_instOrdOption___redArg___lam__0(v_inst_536_, v_x_537_, v_x_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_541_){
_start:
{
lean_object* v___f_542_; 
v___f_542_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_542_, 0, v_inst_541_);
return v___f_542_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_543_, lean_object* v_inst_544_){
_start:
{
lean_object* v___f_545_; 
v___f_545_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_545_, 0, v_inst_544_);
return v___f_545_;
}
}
lean_object* l_instOrdOrdering___lam__0(uint8_t v_x_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(v_x_546_);
v___x_548_ = lean_obj_tag_nat(v___x_547_);
lean_dec(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT void l_instOrdOrdering___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_546_ = stack[0].m_num;
lean_object* v_res_549_;
v_res_549_ = l_instOrdOrdering___lam__0(v_x_546_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_instOrdOrdering___lam__0___boxed(lean_object* v_x_550_){
_start:
{
uint8_t v_x_11__boxed_551_; lean_object* v_res_552_; 
v_x_11__boxed_551_ = lean_unbox(v_x_550_);
v_res_552_ = l_instOrdOrdering___lam__0(v_x_11__boxed_551_);
return v_res_552_;
}
}
uint8_t l_List_compareLex___redArg(lean_object* v_cmp_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_dec_ref(v_cmp_558_);
if (lean_obj_tag(v_x_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = 1;
return v___x_561_;
}
else
{
uint8_t v___x_562_; 
lean_dec(v_x_560_);
v___x_562_ = 0;
return v___x_562_;
}
}
else
{
if (lean_obj_tag(v_x_560_) == 0)
{
uint8_t v___x_563_; 
lean_dec_ref_known(v_x_559_, 2);
lean_dec_ref(v_cmp_558_);
v___x_563_ = 2;
return v___x_563_;
}
else
{
lean_object* v_head_564_; lean_object* v_tail_565_; lean_object* v_head_566_; lean_object* v_tail_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_head_564_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_head_564_);
v_tail_565_ = lean_ctor_get(v_x_559_, 1);
lean_inc(v_tail_565_);
lean_dec_ref_known(v_x_559_, 2);
v_head_566_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_566_);
v_tail_567_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_tail_567_);
lean_dec_ref_known(v_x_560_, 2);
lean_inc_ref(v_cmp_558_);
v___x_568_ = lean_apply_2(v_cmp_558_, v_head_564_, v_head_566_);
v___x_569_ = lean_unbox(v___x_568_);
if (v___x_569_ == 1)
{
v_x_559_ = v_tail_565_;
v_x_560_ = v_tail_567_;
goto _start;
}
else
{
uint8_t v___x_571_; 
lean_dec(v_tail_567_);
lean_dec(v_tail_565_);
lean_dec_ref(v_cmp_558_);
v___x_571_ = lean_unbox(v___x_568_);
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT void l_List_compareLex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_558_ = stack[0].m_obj;
lean_object* v_x_559_ = stack[1].m_obj;
lean_object* v_x_560_ = stack[2].m_obj;
uint8_t v_res_572_;
v_res_572_ = l_List_compareLex___redArg(v_cmp_558_, v_x_559_, v_x_560_);
stack->m_num = v_res_572_;
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_List_compareLex___redArg(v_cmp_573_, v_x_574_, v_x_575_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
uint8_t l_List_compareLex(lean_object* v_00_u03b1_578_, lean_object* v_cmp_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_List_compareLex___redArg(v_cmp_579_, v_x_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT void l_List_compareLex_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_579_ = stack[1].m_obj;
lean_object* v_x_580_ = stack[2].m_obj;
lean_object* v_x_581_ = stack[3].m_obj;
uint8_t v_res_583_;
v_res_583_ = l_List_compareLex(lean_box(0), v_cmp_579_, v_x_580_, v_x_581_);
stack->m_num = v_res_583_;
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_584_, lean_object* v_cmp_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_List_compareLex(v_00_u03b1_584_, v_cmp_585_, v_x_586_, v_x_587_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_591_, 0, lean_box(0));
lean_closure_set(v___x_591_, 1, v_inst_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_592_, lean_object* v_inst_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_594_, 0, lean_box(0));
lean_closure_set(v___x_594_, 1, v_inst_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_h__1_597_, lean_object* v_h__2_598_, lean_object* v_h__3_599_, lean_object* v_h__4_600_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_dec(v_h__4_600_);
lean_dec(v_h__3_599_);
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_h__2_598_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_apply_1(v_h__1_597_, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; 
lean_dec(v_h__1_597_);
v___x_603_ = lean_apply_2(v_h__2_598_, v_x_596_, lean_box(0));
return v___x_603_;
}
}
else
{
lean_dec(v_h__2_598_);
lean_dec(v_h__1_597_);
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_604_; 
lean_dec(v_h__4_600_);
v___x_604_ = lean_apply_2(v_h__3_599_, v_x_595_, lean_box(0));
return v___x_604_;
}
else
{
lean_object* v_head_605_; lean_object* v_tail_606_; lean_object* v_head_607_; lean_object* v_tail_608_; lean_object* v___x_609_; 
lean_dec(v_h__3_599_);
v_head_605_ = lean_ctor_get(v_x_595_, 0);
lean_inc(v_head_605_);
v_tail_606_ = lean_ctor_get(v_x_595_, 1);
lean_inc(v_tail_606_);
lean_dec_ref_known(v_x_595_, 2);
v_head_607_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_head_607_);
v_tail_608_ = lean_ctor_get(v_x_596_, 1);
lean_inc(v_tail_608_);
lean_dec_ref_known(v_x_596_, 2);
v___x_609_ = lean_apply_4(v_h__4_600_, v_head_605_, v_tail_606_, v_head_607_, v_tail_608_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_610_, lean_object* v_motive_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_h__1_614_, lean_object* v_h__2_615_, lean_object* v_h__3_616_, lean_object* v_h__4_617_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_dec(v_h__4_617_);
lean_dec(v_h__3_616_);
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_h__2_615_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_apply_1(v_h__1_614_, v___x_618_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; 
lean_dec(v_h__1_614_);
v___x_620_ = lean_apply_2(v_h__2_615_, v_x_613_, lean_box(0));
return v___x_620_;
}
}
else
{
lean_dec(v_h__2_615_);
lean_dec(v_h__1_614_);
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_621_; 
lean_dec(v_h__4_617_);
v___x_621_ = lean_apply_2(v_h__3_616_, v_x_612_, lean_box(0));
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_626_; 
lean_dec(v_h__3_616_);
v_head_622_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_head_622_);
v_tail_623_ = lean_ctor_get(v_x_612_, 1);
lean_inc(v_tail_623_);
lean_dec_ref_known(v_x_612_, 2);
v_head_624_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_head_624_);
v_tail_625_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_tail_625_);
lean_dec_ref_known(v_x_613_, 2);
v___x_626_ = lean_apply_4(v_h__4_617_, v_head_622_, v_tail_623_, v_head_624_, v_tail_625_);
return v___x_626_;
}
}
}
}
lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_, lean_object* v_h__3_630_){
_start:
{
switch(v_x_627_)
{
case 0:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_apply_1(v_h__1_628_, v___x_631_);
return v___x_632_;
}
case 1:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_h__3_630_);
lean_dec(v_h__1_628_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_1(v_h__2_629_, v___x_633_);
return v___x_634_;
}
default: 
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_apply_1(v_h__3_630_, v___x_635_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_627_ = stack[0].m_num;
lean_object* v_h__1_628_ = stack[1].m_obj;
lean_object* v_h__2_629_ = stack[2].m_obj;
lean_object* v_h__3_630_ = stack[3].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_627_, v_h__1_628_, v_h__2_629_, v_h__3_630_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_, lean_object* v_h__3_641_){
_start:
{
uint8_t v_x_33__boxed_642_; lean_object* v_res_643_; 
v_x_33__boxed_642_ = lean_unbox(v_x_638_);
v_res_643_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_642_, v_h__1_639_, v_h__2_640_, v_h__3_641_);
return v_res_643_;
}
}
lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_644_, uint8_t v_x_645_, lean_object* v_h__1_646_, lean_object* v_h__2_647_, lean_object* v_h__3_648_){
_start:
{
switch(v_x_645_)
{
case 0:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v_h__3_648_);
lean_dec(v_h__2_647_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_apply_1(v_h__1_646_, v___x_649_);
return v___x_650_;
}
case 1:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_h__3_648_);
lean_dec(v_h__1_646_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_apply_1(v_h__2_647_, v___x_651_);
return v___x_652_;
}
default: 
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_h__2_647_);
lean_dec(v_h__1_646_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_apply_1(v_h__3_648_, v___x_653_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_645_ = stack[1].m_num;
lean_object* v_h__1_646_ = stack[2].m_obj;
lean_object* v_h__2_647_ = stack[3].m_obj;
lean_object* v_h__3_648_ = stack[4].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_box(0), v_x_645_, v_h__1_646_, v_h__2_647_, v_h__3_648_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_656_, lean_object* v_x_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_, lean_object* v_h__3_660_){
_start:
{
uint8_t v_x_56__boxed_661_; lean_object* v_res_662_; 
v_x_56__boxed_661_ = lean_unbox(v_x_657_);
v_res_662_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_656_, v_x_56__boxed_661_, v_h__1_658_, v_h__2_659_, v_h__3_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_663_){
_start:
{
lean_object* v_fst_664_; 
v_fst_664_ = lean_ctor_get(v_x_663_, 0);
lean_inc(v_fst_664_);
return v_fst_664_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_lexOrd___redArg___lam__0(v_x_665_);
lean_dec_ref(v_x_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_667_){
_start:
{
lean_object* v_snd_668_; 
v_snd_668_ = lean_ctor_get(v_x_667_, 1);
lean_inc(v_snd_668_);
return v_snd_668_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_lexOrd___redArg___lam__1(v_x_669_);
lean_dec_ref(v_x_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___f_675_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_676_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_677_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_677_, 0, lean_box(0));
lean_closure_set(v___x_677_, 1, lean_box(0));
lean_closure_set(v___x_677_, 2, v_inst_673_);
lean_closure_set(v___x_677_, 3, v___f_675_);
v___x_678_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_678_, 0, lean_box(0));
lean_closure_set(v___x_678_, 1, lean_box(0));
lean_closure_set(v___x_678_, 2, v_inst_674_);
lean_closure_set(v___x_678_, 3, v___f_676_);
v___x_679_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_679_, 0, lean_box(0));
lean_closure_set(v___x_679_, 1, lean_box(0));
lean_closure_set(v___x_679_, 2, v___x_677_);
lean_closure_set(v___x_679_, 3, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_inst_682_, lean_object* v_inst_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_lexOrd___redArg(v_inst_682_, v_inst_683_);
return v___x_684_;
}
}
uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_685_, lean_object* v_a_686_, lean_object* v_b_687_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_apply_2(v_inst_685_, v_a_686_, v_b_687_);
v___x_689_ = lean_unbox(v___x_688_);
if (v___x_689_ == 1)
{
uint8_t v___x_690_; 
v___x_690_ = 1;
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
}
LEAN_EXPORT void l_beqOfOrd___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_685_ = stack[0].m_obj;
lean_object* v_a_686_ = stack[1].m_obj;
lean_object* v_b_687_ = stack[2].m_obj;
uint8_t v_res_692_;
v_res_692_ = l_beqOfOrd___redArg___lam__0(v_inst_685_, v_a_686_, v_b_687_);
stack->m_num = v_res_692_;
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_693_, lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_beqOfOrd___redArg___lam__0(v_inst_693_, v_a_694_, v_b_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_698_){
_start:
{
lean_object* v___f_699_; 
v___f_699_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_699_, 0, v_inst_698_);
return v___f_699_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v___f_702_; 
v___f_702_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_702_, 0, v_inst_701_);
return v___f_702_;
}
}
lean_object* l_ltOfOrd___redArg(){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
return v___x_704_;
}
}
LEAN_EXPORT void l_ltOfOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_705_;
v_res_705_ = l_ltOfOrd___redArg();
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_ltOfOrd___redArg___boxed(lean_object* v___dummy_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_ltOfOrd___redArg();
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_711_, lean_object* v_inst_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_ltOfOrd(v_00_u03b1_711_, v_inst_712_);
lean_dec_ref(v_inst_712_);
return v_res_713_;
}
}
uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_714_, lean_object* v_a_715_, lean_object* v_b_716_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_apply_2(v_inst_714_, v_a_715_, v_b_716_);
v___x_718_ = lean_unbox(v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = 1;
return v___x_719_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = 0;
return v___x_720_;
}
}
}
LEAN_EXPORT void l_instDecidableRelLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_714_ = stack[0].m_obj;
lean_object* v_a_715_ = stack[1].m_obj;
lean_object* v_b_716_ = stack[2].m_obj;
uint8_t v_res_721_;
v_res_721_ = l_instDecidableRelLt___redArg(v_inst_714_, v_a_715_, v_b_716_);
stack->m_num = v_res_721_;
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_722_, lean_object* v_a_723_, lean_object* v_b_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_instDecidableRelLt___redArg(v_inst_722_, v_a_723_, v_b_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_727_, lean_object* v_inst_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_apply_2(v_inst_728_, v_a_729_, v_b_730_);
v___x_732_ = lean_unbox(v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = 1;
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
}
}
LEAN_EXPORT void l_instDecidableRelLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_728_ = stack[1].m_obj;
lean_object* v_a_729_ = stack[2].m_obj;
lean_object* v_b_730_ = stack[3].m_obj;
uint8_t v_res_735_;
v_res_735_ = l_instDecidableRelLt(lean_box(0), v_inst_728_, v_a_729_, v_b_730_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_736_, lean_object* v_inst_737_, lean_object* v_a_738_, lean_object* v_b_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_instDecidableRelLt(v_00_u03b1_736_, v_inst_737_, v_a_738_, v_b_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
lean_object* l_leOfOrd___redArg(){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(0);
return v___x_743_;
}
}
LEAN_EXPORT void l_leOfOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_744_;
v_res_744_ = l_leOfOrd___redArg();
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l_leOfOrd___redArg___boxed(lean_object* v___dummy_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_leOfOrd___redArg();
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_leOfOrd(v_00_u03b1_750_, v_inst_751_);
lean_dec_ref(v_inst_751_);
return v_res_752_;
}
}
uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_apply_2(v_inst_753_, v_x_754_, v_x_755_);
v___x_757_ = lean_unbox(v___x_756_);
if (v___x_757_ == 2)
{
uint8_t v___x_758_; 
v___x_758_ = 0;
return v___x_758_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = 1;
return v___x_759_;
}
}
}
LEAN_EXPORT void l_instDecidableRelLe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_753_ = stack[0].m_obj;
lean_object* v_x_754_ = stack[1].m_obj;
lean_object* v_x_755_ = stack[2].m_obj;
uint8_t v_res_760_;
v_res_760_ = l_instDecidableRelLe___redArg(v_inst_753_, v_x_754_, v_x_755_);
stack->m_num = v_res_760_;
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_instDecidableRelLe___redArg(v_inst_761_, v_x_762_, v_x_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_766_, lean_object* v_inst_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_apply_2(v_inst_767_, v_x_768_, v_x_769_);
v___x_771_ = lean_unbox(v___x_770_);
if (v___x_771_ == 2)
{
uint8_t v___x_772_; 
v___x_772_ = 0;
return v___x_772_;
}
else
{
uint8_t v___x_773_; 
v___x_773_ = 1;
return v___x_773_;
}
}
}
LEAN_EXPORT void l_instDecidableRelLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_767_ = stack[1].m_obj;
lean_object* v_x_768_ = stack[2].m_obj;
lean_object* v_x_769_ = stack[3].m_obj;
uint8_t v_res_774_;
v_res_774_ = l_instDecidableRelLe(lean_box(0), v_inst_767_, v_x_768_, v_x_769_);
stack->m_num = v_res_774_;
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_775_, lean_object* v_inst_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_instDecidableRelLe(v_00_u03b1_775_, v_inst_776_, v_x_777_, v_x_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_781_){
_start:
{
lean_object* v___f_782_; 
v___f_782_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_782_, 0, v_ord_781_);
return v___f_782_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_783_, lean_object* v_ord_784_){
_start:
{
lean_object* v___f_785_; 
v___f_785_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_785_, 0, v_ord_784_);
return v___f_785_;
}
}
lean_object* l_Ord_toLT___redArg(){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = lean_box(0);
return v___x_787_;
}
}
LEAN_EXPORT void l_Ord_toLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_788_;
v_res_788_ = l_Ord_toLT___redArg();
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Ord_toLT___redArg___boxed(lean_object* v___dummy_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Ord_toLT___redArg();
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_791_, lean_object* v_ord_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_794_, lean_object* v_ord_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Ord_toLT(v_00_u03b1_794_, v_ord_795_);
lean_dec_ref(v_ord_795_);
return v_res_796_;
}
}
lean_object* l_Ord_toLE___redArg(){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
LEAN_EXPORT void l_Ord_toLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_799_;
v_res_799_ = l_Ord_toLE___redArg();
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Ord_toLE___redArg___boxed(lean_object* v___dummy_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Ord_toLE___redArg();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_802_, lean_object* v_ord_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_box(0);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_805_, lean_object* v_ord_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Ord_toLE(v_00_u03b1_805_, v_ord_806_);
lean_dec_ref(v_ord_806_);
return v_res_807_;
}
}
uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_808_, lean_object* v_x_809_, lean_object* v_y_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_apply_2(v_ord_808_, v_y_810_, v_x_809_);
v___x_812_ = lean_unbox(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT void l_Ord_opposite___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ord_808_ = stack[0].m_obj;
lean_object* v_x_809_ = stack[1].m_obj;
lean_object* v_y_810_ = stack[2].m_obj;
uint8_t v_res_813_;
v_res_813_ = l_Ord_opposite___redArg___lam__0(v_ord_808_, v_x_809_, v_y_810_);
stack->m_num = v_res_813_;
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_814_, lean_object* v_x_815_, lean_object* v_y_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Ord_opposite___redArg___lam__0(v_ord_814_, v_x_815_, v_y_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_819_){
_start:
{
lean_object* v___f_820_; 
v___f_820_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_820_, 0, v_ord_819_);
return v___f_820_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_821_, lean_object* v_ord_822_){
_start:
{
lean_object* v___f_823_; 
v___f_823_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_823_, 0, v_ord_822_);
return v___f_823_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_824_, lean_object* v_f_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_826_, 0, lean_box(0));
lean_closure_set(v___x_826_, 1, lean_box(0));
lean_closure_set(v___x_826_, 2, v_x_824_);
lean_closure_set(v___x_826_, 3, v_f_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_827_, lean_object* v_00_u03b1_828_, lean_object* v_x_829_, lean_object* v_f_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_831_, 0, lean_box(0));
lean_closure_set(v___x_831_, 1, lean_box(0));
lean_closure_set(v___x_831_, 2, v_x_829_);
lean_closure_set(v___x_831_, 3, v_f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_lexOrd___redArg(v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_lexOrd___redArg(v_x_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_840_, lean_object* v_ord_u2082_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_842_, 0, lean_box(0));
lean_closure_set(v___x_842_, 1, lean_box(0));
lean_closure_set(v___x_842_, 2, v_ord_u2081_840_);
lean_closure_set(v___x_842_, 3, v_ord_u2082_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_843_, lean_object* v_ord_u2081_844_, lean_object* v_ord_u2082_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_846_, 0, lean_box(0));
lean_closure_set(v___x_846_, 1, lean_box(0));
lean_closure_set(v___x_846_, 2, v_ord_u2081_844_);
lean_closure_set(v___x_846_, 3, v_ord_u2082_845_);
return v___x_846_;
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
