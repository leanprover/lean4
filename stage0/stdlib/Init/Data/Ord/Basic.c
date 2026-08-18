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
uint8_t v_x_13__boxed_82_; uint8_t v_y_14__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_13__boxed_82_ = lean_unbox(v_x_80_);
v_y_14__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_instDecidableEqOrdering(v_x_13__boxed_82_, v_y_14__boxed_83_);
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
uint8_t v_x_177__boxed_136_; lean_object* v_res_137_; 
v_x_177__boxed_136_ = lean_unbox(v_x_134_);
v_res_137_ = l_instReprOrdering_repr(v_x_177__boxed_136_, v_prec_135_);
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
uint8_t v_x_21__boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_x_21__boxed_151_ = lean_unbox(v_x_150_);
v_res_152_ = l_Ordering_isEq(v_x_21__boxed_151_);
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
uint8_t v_x_21__boxed_158_; uint8_t v_res_159_; lean_object* v_r_160_; 
v_x_21__boxed_158_ = lean_unbox(v_x_157_);
v_res_159_ = l_Ordering_isNe(v_x_21__boxed_158_);
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
uint8_t v_x_21__boxed_165_; uint8_t v_res_166_; lean_object* v_r_167_; 
v_x_21__boxed_165_ = lean_unbox(v_x_164_);
v_res_166_ = l_Ordering_isLE(v_x_21__boxed_165_);
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
uint8_t v_x_21__boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_x_21__boxed_172_ = lean_unbox(v_x_171_);
v_res_173_ = l_Ordering_isLT(v_x_21__boxed_172_);
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
uint8_t v_x_21__boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_x_21__boxed_179_ = lean_unbox(v_x_178_);
v_res_180_ = l_Ordering_isGT(v_x_21__boxed_179_);
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
uint8_t v_x_21__boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_x_21__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Ordering_isGE(v_x_21__boxed_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_189_){
_start:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_190_ = 0;
v___x_191_ = lean_box(v___x_190_);
lean_inc_ref(v_inst_189_);
v___x_192_ = lean_apply_1(v_inst_189_, v___x_191_);
v___x_193_ = lean_unbox(v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
lean_dec_ref(v_inst_189_);
v___x_194_ = lean_unbox(v___x_192_);
return v___x_194_;
}
else
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = 1;
v___x_196_ = lean_box(v___x_195_);
lean_inc_ref(v_inst_189_);
v___x_197_ = lean_apply_1(v_inst_189_, v___x_196_);
v___x_198_ = lean_unbox(v___x_197_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; 
lean_dec_ref(v_inst_189_);
v___x_199_ = lean_unbox(v___x_197_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_200_ = 2;
v___x_201_ = lean_box(v___x_200_);
v___x_202_ = lean_apply_1(v_inst_189_, v___x_201_);
v___x_203_ = lean_unbox(v___x_202_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableForallOfDecidablePred(lean_object* v_p_207_, lean_object* v_inst_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_210_, lean_object* v_inst_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_210_, v_inst_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_214_){
_start:
{
uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_215_ = 0;
v___x_216_ = lean_box(v___x_215_);
lean_inc_ref(v_inst_214_);
v___x_217_ = lean_apply_1(v_inst_214_, v___x_216_);
v___x_218_ = lean_unbox(v___x_217_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_219_ = 1;
v___x_220_ = lean_box(v___x_219_);
lean_inc_ref(v_inst_214_);
v___x_221_ = lean_apply_1(v_inst_214_, v___x_220_);
v___x_222_ = lean_unbox(v___x_221_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_223_ = 2;
v___x_224_ = lean_box(v___x_223_);
v___x_225_ = lean_apply_1(v_inst_214_, v___x_224_);
v___x_226_ = lean_unbox(v___x_225_);
return v___x_226_;
}
else
{
uint8_t v___x_227_; 
lean_dec_ref(v_inst_214_);
v___x_227_ = lean_unbox(v___x_221_);
return v___x_227_;
}
}
else
{
uint8_t v___x_228_; 
lean_dec_ref(v_inst_214_);
v___x_228_ = lean_unbox(v___x_217_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Ordering_instDecidableExistsOfDecidablePred(lean_object* v_p_232_, lean_object* v_inst_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Ordering_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_235_, lean_object* v_inst_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_235_, v_inst_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
if (v_a_239_ == 1)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__2_241_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__1_240_, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__1_240_);
v___x_244_ = lean_box(v_a_239_);
v___x_245_ = lean_apply_2(v_h__2_241_, v___x_244_, lean_box(0));
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_){
_start:
{
uint8_t v_a_17__boxed_249_; lean_object* v_res_250_; 
v_a_17__boxed_249_ = lean_unbox(v_a_246_);
v_res_250_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(v_a_17__boxed_249_, v_h__1_247_, v_h__2_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(lean_object* v_motive_251_, uint8_t v_a_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (v_a_252_ == 1)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_h__2_254_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_h__1_253_, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_253_);
v___x_257_ = lean_box(v_a_252_);
v___x_258_ = lean_apply_2(v_h__2_254_, v___x_257_, lean_box(0));
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_259_, lean_object* v_a_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
uint8_t v_a_28__boxed_263_; lean_object* v_res_264_; 
v_a_28__boxed_263_ = lean_unbox(v_a_260_);
v_res_264_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(v_motive_259_, v_a_28__boxed_263_, v_h__1_261_, v_h__2_262_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq___redArg(lean_object* v_x_265_, lean_object* v_y_266_, uint8_t v_inst_267_, lean_object* v_inst_268_){
_start:
{
if (v_inst_267_ == 0)
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_apply_2(v_inst_268_, v_x_265_, v_y_266_);
v___x_270_ = lean_unbox(v___x_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 2;
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 1;
return v___x_272_;
}
}
else
{
uint8_t v___x_273_; 
lean_dec_ref(v_inst_268_);
lean_dec(v_y_266_);
lean_dec(v_x_265_);
v___x_273_ = 0;
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___redArg___boxed(lean_object* v_x_274_, lean_object* v_y_275_, lean_object* v_inst_276_, lean_object* v_inst_277_){
_start:
{
uint8_t v_inst_23__boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_inst_23__boxed_278_ = lean_unbox(v_inst_276_);
v_res_279_ = l_compareOfLessAndEq___redArg(v_x_274_, v_y_275_, v_inst_23__boxed_278_, v_inst_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndEq(lean_object* v_00_u03b1_281_, lean_object* v_x_282_, lean_object* v_y_283_, lean_object* v_inst_284_, uint8_t v_inst_285_, lean_object* v_inst_286_){
_start:
{
if (v_inst_285_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_apply_2(v_inst_286_, v_x_282_, v_y_283_);
v___x_288_ = lean_unbox(v___x_287_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; 
v___x_289_ = 2;
return v___x_289_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = 1;
return v___x_290_;
}
}
else
{
uint8_t v___x_291_; 
lean_dec_ref(v_inst_286_);
lean_dec(v_y_283_);
lean_dec(v_x_282_);
v___x_291_ = 0;
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndEq___boxed(lean_object* v_00_u03b1_292_, lean_object* v_x_293_, lean_object* v_y_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_){
_start:
{
uint8_t v_inst_40__boxed_298_; uint8_t v_res_299_; lean_object* v_r_300_; 
v_inst_40__boxed_298_ = lean_unbox(v_inst_296_);
v_res_299_ = l_compareOfLessAndEq(v_00_u03b1_292_, v_x_293_, v_y_294_, v_inst_295_, v_inst_40__boxed_298_, v_inst_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq___redArg(lean_object* v_x_301_, lean_object* v_y_302_, uint8_t v_inst_303_, lean_object* v_inst_304_){
_start:
{
if (v_inst_303_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_apply_2(v_inst_304_, v_x_301_, v_y_302_);
v___x_306_ = lean_unbox(v___x_305_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; 
v___x_307_ = 2;
return v___x_307_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = 1;
return v___x_308_;
}
}
else
{
uint8_t v___x_309_; 
lean_dec_ref(v_inst_304_);
lean_dec(v_y_302_);
lean_dec(v_x_301_);
v___x_309_ = 0;
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___redArg___boxed(lean_object* v_x_310_, lean_object* v_y_311_, lean_object* v_inst_312_, lean_object* v_inst_313_){
_start:
{
uint8_t v_inst_42__boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_inst_42__boxed_314_ = lean_unbox(v_inst_312_);
v_res_315_ = l_compareOfLessAndBEq___redArg(v_x_310_, v_y_311_, v_inst_42__boxed_314_, v_inst_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_compareOfLessAndBEq(lean_object* v_00_u03b1_317_, lean_object* v_x_318_, lean_object* v_y_319_, lean_object* v_inst_320_, uint8_t v_inst_321_, lean_object* v_inst_322_){
_start:
{
if (v_inst_321_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_apply_2(v_inst_322_, v_x_318_, v_y_319_);
v___x_324_ = lean_unbox(v___x_323_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 2;
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 1;
return v___x_326_;
}
}
else
{
uint8_t v___x_327_; 
lean_dec_ref(v_inst_322_);
lean_dec(v_y_319_);
lean_dec(v_x_318_);
v___x_327_ = 0;
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_compareOfLessAndBEq___boxed(lean_object* v_00_u03b1_328_, lean_object* v_x_329_, lean_object* v_y_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_){
_start:
{
uint8_t v_inst_59__boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_inst_59__boxed_334_ = lean_unbox(v_inst_332_);
v_res_335_ = l_compareOfLessAndBEq(v_00_u03b1_328_, v_x_329_, v_y_330_, v_inst_331_, v_inst_59__boxed_334_, v_inst_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_compareLex___redArg(lean_object* v_cmp_u2081_337_, lean_object* v_cmp_u2082_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
lean_inc(v_b_340_);
lean_inc(v_a_339_);
v___x_341_ = lean_apply_2(v_cmp_u2081_337_, v_a_339_, v_b_340_);
v___x_342_ = lean_unbox(v___x_341_);
if (v___x_342_ == 1)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_apply_2(v_cmp_u2082_338_, v_a_339_, v_b_340_);
v___x_344_ = lean_unbox(v___x_343_);
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
lean_dec(v_b_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_cmp_u2082_338_);
v___x_345_ = lean_unbox(v___x_341_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___redArg___boxed(lean_object* v_cmp_u2081_346_, lean_object* v_cmp_u2082_347_, lean_object* v_a_348_, lean_object* v_b_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_compareLex___redArg(v_cmp_u2081_346_, v_cmp_u2082_347_, v_a_348_, v_b_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_compareLex(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_cmp_u2081_354_, lean_object* v_cmp_u2082_355_, lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
lean_inc(v_b_357_);
lean_inc(v_a_356_);
v___x_358_ = lean_apply_2(v_cmp_u2081_354_, v_a_356_, v_b_357_);
v___x_359_ = lean_unbox(v___x_358_);
if (v___x_359_ == 1)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_apply_2(v_cmp_u2082_355_, v_a_356_, v_b_357_);
v___x_361_ = lean_unbox(v___x_360_);
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
lean_dec(v_b_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_cmp_u2082_355_);
v___x_362_ = lean_unbox(v___x_358_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_compareLex___boxed(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_cmp_u2081_365_, lean_object* v_cmp_u2082_366_, lean_object* v_a_367_, lean_object* v_b_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_compareLex(v_00_u03b1_363_, v_00_u03b2_364_, v_cmp_u2081_365_, v_cmp_u2082_366_, v_a_367_, v_b_368_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint8_t l_compareOn___redArg(lean_object* v_ord_371_, lean_object* v_f_372_, lean_object* v_x_373_, lean_object* v_y_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
lean_inc(v_f_372_);
v___x_375_ = lean_apply_1(v_f_372_, v_x_373_);
v___x_376_ = lean_apply_1(v_f_372_, v_y_374_);
v___x_377_ = lean_apply_2(v_ord_371_, v___x_375_, v___x_376_);
v___x_378_ = lean_unbox(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_compareOn___redArg___boxed(lean_object* v_ord_379_, lean_object* v_f_380_, lean_object* v_x_381_, lean_object* v_y_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_compareOn___redArg(v_ord_379_, v_f_380_, v_x_381_, v_y_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_compareOn(lean_object* v_00_u03b2_385_, lean_object* v_00_u03b1_386_, lean_object* v_ord_387_, lean_object* v_f_388_, lean_object* v_x_389_, lean_object* v_y_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
lean_inc(v_f_388_);
v___x_391_ = lean_apply_1(v_f_388_, v_x_389_);
v___x_392_ = lean_apply_1(v_f_388_, v_y_390_);
v___x_393_ = lean_apply_2(v_ord_387_, v___x_391_, v___x_392_);
v___x_394_ = lean_unbox(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_compareOn___boxed(lean_object* v_00_u03b2_395_, lean_object* v_00_u03b1_396_, lean_object* v_ord_397_, lean_object* v_f_398_, lean_object* v_x_399_, lean_object* v_y_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_compareOn(v_00_u03b2_395_, v_00_u03b1_396_, v_ord_397_, v_f_398_, v_x_399_, v_y_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_instOrdNat___lam__0(lean_object* v_x_403_, lean_object* v_y_404_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = lean_nat_dec_lt(v_x_403_, v_y_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_eq(v_x_403_, v_y_404_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 2;
return v___x_407_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 1;
return v___x_408_;
}
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdNat___lam__0___boxed(lean_object* v_x_410_, lean_object* v_y_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_instOrdNat___lam__0(v_x_410_, v_y_411_);
lean_dec(v_y_411_);
lean_dec(v_x_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_instOrdInt___lam__0(lean_object* v_x_416_, lean_object* v_y_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_int_dec_lt(v_x_416_, v_y_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = lean_int_dec_eq(v_x_416_, v_y_417_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 2;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 1;
return v___x_421_;
}
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_instOrdInt___lam__0___boxed(lean_object* v_x_423_, lean_object* v_y_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_instOrdInt___lam__0(v_x_423_, v_y_424_);
lean_dec(v_y_424_);
lean_dec(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_instOrdBool___lam__0(uint8_t v_x_429_, uint8_t v_x_430_){
_start:
{
if (v_x_429_ == 0)
{
if (v_x_430_ == 1)
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = 1;
return v___x_432_;
}
}
else
{
if (v_x_430_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 2;
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = 1;
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdBool___lam__0___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_x_49__boxed_437_; uint8_t v_x_50__boxed_438_; uint8_t v_res_439_; lean_object* v_r_440_; 
v_x_49__boxed_437_ = lean_unbox(v_x_435_);
v_x_50__boxed_438_ = lean_unbox(v_x_436_);
v_res_439_ = l_instOrdBool___lam__0(v_x_49__boxed_437_, v_x_50__boxed_438_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin(lean_object* v_n_443_){
_start:
{
lean_object* v___f_444_; 
v___f_444_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_444_;
}
}
LEAN_EXPORT lean_object* l_instOrdFin___boxed(lean_object* v_n_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_instOrdFin(v_n_445_);
lean_dec(v_n_445_);
return v_res_446_;
}
}
LEAN_EXPORT uint8_t l_instOrdChar___lam__0(uint32_t v_x_447_, uint32_t v_y_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_uint32_dec_lt(v_x_447_, v_y_448_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = lean_uint32_dec_eq(v_x_447_, v_y_448_);
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
LEAN_EXPORT lean_object* l_instOrdChar___lam__0___boxed(lean_object* v_x_454_, lean_object* v_y_455_){
_start:
{
uint32_t v_x_boxed_456_; uint32_t v_y_boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v_x_boxed_456_ = lean_unbox_uint32(v_x_454_);
lean_dec(v_x_454_);
v_y_boxed_457_ = lean_unbox_uint32(v_y_455_);
lean_dec(v_y_455_);
v_res_458_ = l_instOrdChar___lam__0(v_x_boxed_456_, v_y_boxed_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec(lean_object* v_n_462_){
_start:
{
lean_object* v___f_463_; 
v___f_463_ = ((lean_object*)(l_instOrdNat___closed__0));
return v___f_463_;
}
}
LEAN_EXPORT lean_object* l_instOrdBitVec___boxed(lean_object* v_n_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_instOrdBitVec(v_n_464_);
lean_dec(v_n_464_);
return v_res_465_;
}
}
LEAN_EXPORT uint8_t l_instOrdOption___redArg___lam__0(lean_object* v_inst_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_dec_ref(v_inst_466_);
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
lean_dec_ref_known(v_x_468_, 1);
v___x_470_ = 0;
return v___x_470_;
}
}
else
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_471_; 
lean_dec_ref_known(v_x_467_, 1);
lean_dec_ref(v_inst_466_);
v___x_471_ = 2;
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v_val_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_val_472_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_x_467_, 1);
v_val_473_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v_x_468_, 1);
v___x_474_ = lean_apply_2(v_inst_466_, v_val_472_, v_val_473_);
v___x_475_ = lean_unbox(v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg___lam__0___boxed(lean_object* v_inst_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_instOrdOption___redArg___lam__0(v_inst_476_, v_x_477_, v_x_478_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption___redArg(lean_object* v_inst_481_){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_482_, 0, v_inst_481_);
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l_instOrdOption(lean_object* v_00_u03b1_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v___f_485_; 
v___f_485_ = lean_alloc_closure((void*)(l_instOrdOption___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_485_, 0, v_inst_484_);
return v___f_485_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex___redArg(lean_object* v_cmp_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_dec_ref(v_cmp_491_);
if (lean_obj_tag(v_x_493_) == 0)
{
uint8_t v___x_494_; 
v___x_494_ = 1;
return v___x_494_;
}
else
{
uint8_t v___x_495_; 
lean_dec(v_x_493_);
v___x_495_ = 0;
return v___x_495_;
}
}
else
{
if (lean_obj_tag(v_x_493_) == 0)
{
uint8_t v___x_496_; 
lean_dec_ref_known(v_x_492_, 2);
lean_dec_ref(v_cmp_491_);
v___x_496_ = 2;
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v_tail_498_; lean_object* v_head_499_; lean_object* v_tail_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_head_497_ = lean_ctor_get(v_x_492_, 0);
lean_inc(v_head_497_);
v_tail_498_ = lean_ctor_get(v_x_492_, 1);
lean_inc(v_tail_498_);
lean_dec_ref_known(v_x_492_, 2);
v_head_499_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_head_499_);
v_tail_500_ = lean_ctor_get(v_x_493_, 1);
lean_inc(v_tail_500_);
lean_dec_ref_known(v_x_493_, 2);
lean_inc_ref(v_cmp_491_);
v___x_501_ = lean_apply_2(v_cmp_491_, v_head_497_, v_head_499_);
v___x_502_ = lean_unbox(v___x_501_);
if (v___x_502_ == 1)
{
v_x_492_ = v_tail_498_;
v_x_493_ = v_tail_500_;
goto _start;
}
else
{
uint8_t v___x_504_; 
lean_dec(v_tail_500_);
lean_dec(v_tail_498_);
lean_dec_ref(v_cmp_491_);
v___x_504_ = lean_unbox(v___x_501_);
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___redArg___boxed(lean_object* v_cmp_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_List_compareLex___redArg(v_cmp_505_, v_x_506_, v_x_507_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT uint8_t l_List_compareLex(lean_object* v_00_u03b1_510_, lean_object* v_cmp_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = l_List_compareLex___redArg(v_cmp_511_, v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_List_compareLex___boxed(lean_object* v_00_u03b1_515_, lean_object* v_cmp_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_List_compareLex(v_00_u03b1_515_, v_cmp_516_, v_x_517_, v_x_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd___redArg(lean_object* v_inst_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_522_, 0, lean_box(0));
lean_closure_set(v___x_522_, 1, v_inst_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_List_instOrd(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_closure((void*)(l_List_compareLex___boxed), 4, 2);
lean_closure_set(v___x_525_, 0, lean_box(0));
lean_closure_set(v___x_525_, 1, v_inst_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_, lean_object* v_h__3_530_, lean_object* v_h__4_531_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_dec(v_h__4_531_);
lean_dec(v_h__3_530_);
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_h__2_529_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_apply_1(v_h__1_528_, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
lean_dec(v_h__1_528_);
v___x_534_ = lean_apply_2(v_h__2_529_, v_x_527_, lean_box(0));
return v___x_534_;
}
}
else
{
lean_dec(v_h__2_529_);
lean_dec(v_h__1_528_);
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v___x_535_; 
lean_dec(v_h__4_531_);
v___x_535_ = lean_apply_2(v_h__3_530_, v_x_526_, lean_box(0));
return v___x_535_;
}
else
{
lean_object* v_head_536_; lean_object* v_tail_537_; lean_object* v_head_538_; lean_object* v_tail_539_; lean_object* v___x_540_; 
lean_dec(v_h__3_530_);
v_head_536_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_head_536_);
v_tail_537_ = lean_ctor_get(v_x_526_, 1);
lean_inc(v_tail_537_);
lean_dec_ref_known(v_x_526_, 2);
v_head_538_ = lean_ctor_get(v_x_527_, 0);
lean_inc(v_head_538_);
v_tail_539_ = lean_ctor_get(v_x_527_, 1);
lean_inc(v_tail_539_);
lean_dec_ref_known(v_x_527_, 2);
v___x_540_ = lean_apply_4(v_h__4_531_, v_head_536_, v_tail_537_, v_head_538_, v_tail_539_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(lean_object* v_00_u03b1_541_, lean_object* v_motive_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_, lean_object* v_h__3_547_, lean_object* v_h__4_548_){
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
lean_dec_ref_known(v_x_543_, 2);
v_head_555_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_head_555_);
v_tail_556_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_tail_556_);
lean_dec_ref_known(v_x_544_, 2);
v___x_557_ = lean_apply_4(v_h__4_548_, v_head_553_, v_tail_554_, v_head_555_, v_tail_556_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(uint8_t v_x_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_, lean_object* v_h__3_561_){
_start:
{
switch(v_x_558_)
{
case 0:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_h__3_561_);
lean_dec(v_h__2_560_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_apply_1(v_h__1_559_, v___x_562_);
return v___x_563_;
}
case 1:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_h__3_561_);
lean_dec(v_h__1_559_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_apply_1(v_h__2_560_, v___x_564_);
return v___x_565_;
}
default: 
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_h__2_560_);
lean_dec(v_h__1_559_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_apply_1(v_h__3_561_, v___x_566_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(lean_object* v_x_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_, lean_object* v_h__3_571_){
_start:
{
uint8_t v_x_33__boxed_572_; lean_object* v_res_573_; 
v_x_33__boxed_572_ = lean_unbox(v_x_568_);
v_res_573_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(v_x_33__boxed_572_, v_h__1_569_, v_h__2_570_, v_h__3_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(lean_object* v_motive_574_, uint8_t v_x_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_, lean_object* v_h__3_578_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(lean_object* v_motive_585_, lean_object* v_x_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_, lean_object* v_h__3_589_){
_start:
{
uint8_t v_x_48__boxed_590_; lean_object* v_res_591_; 
v_x_48__boxed_590_ = lean_unbox(v_x_586_);
v_res_591_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(v_motive_585_, v_x_48__boxed_590_, v_h__1_587_, v_h__2_588_, v_h__3_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0(lean_object* v_x_592_){
_start:
{
lean_object* v_fst_593_; 
v_fst_593_ = lean_ctor_get(v_x_592_, 0);
lean_inc(v_fst_593_);
return v_fst_593_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__0___boxed(lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_lexOrd___redArg___lam__0(v_x_594_);
lean_dec_ref(v_x_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1(lean_object* v_x_596_){
_start:
{
lean_object* v_snd_597_; 
v_snd_597_ = lean_ctor_get(v_x_596_, 1);
lean_inc(v_snd_597_);
return v_snd_597_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg___lam__1___boxed(lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_lexOrd___redArg___lam__1(v_x_598_);
lean_dec_ref(v_x_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_lexOrd___redArg(lean_object* v_inst_602_, lean_object* v_inst_603_){
_start:
{
lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___f_604_ = ((lean_object*)(l_lexOrd___redArg___closed__0));
v___f_605_ = ((lean_object*)(l_lexOrd___redArg___closed__1));
v___x_606_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_606_, 0, lean_box(0));
lean_closure_set(v___x_606_, 1, lean_box(0));
lean_closure_set(v___x_606_, 2, v_inst_602_);
lean_closure_set(v___x_606_, 3, v___f_604_);
v___x_607_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_607_, 0, lean_box(0));
lean_closure_set(v___x_607_, 1, lean_box(0));
lean_closure_set(v___x_607_, 2, v_inst_603_);
lean_closure_set(v___x_607_, 3, v___f_605_);
v___x_608_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_608_, 0, lean_box(0));
lean_closure_set(v___x_608_, 1, lean_box(0));
lean_closure_set(v___x_608_, 2, v___x_606_);
lean_closure_set(v___x_608_, 3, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_lexOrd(lean_object* v_00_u03b1_609_, lean_object* v_00_u03b2_610_, lean_object* v_inst_611_, lean_object* v_inst_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_lexOrd___redArg(v_inst_611_, v_inst_612_);
return v___x_613_;
}
}
LEAN_EXPORT uint8_t l_beqOfOrd___redArg___lam__0(lean_object* v_inst_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_apply_2(v_inst_614_, v_a_615_, v_b_616_);
v___x_618_ = lean_unbox(v___x_617_);
if (v___x_618_ == 1)
{
uint8_t v___x_619_; 
v___x_619_ = 1;
return v___x_619_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg___lam__0___boxed(lean_object* v_inst_621_, lean_object* v_a_622_, lean_object* v_b_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_beqOfOrd___redArg___lam__0(v_inst_621_, v_a_622_, v_b_623_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd___redArg(lean_object* v_inst_626_){
_start:
{
lean_object* v___f_627_; 
v___f_627_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_627_, 0, v_inst_626_);
return v___f_627_;
}
}
LEAN_EXPORT lean_object* l_beqOfOrd(lean_object* v_00_u03b1_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___f_630_; 
v___f_630_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_630_, 0, v_inst_629_);
return v___f_630_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd(lean_object* v_00_u03b1_631_, lean_object* v_inst_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_ltOfOrd___boxed(lean_object* v_00_u03b1_634_, lean_object* v_inst_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_ltOfOrd(v_00_u03b1_634_, v_inst_635_);
lean_dec_ref(v_inst_635_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt___redArg(lean_object* v_inst_637_, lean_object* v_a_638_, lean_object* v_b_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_apply_2(v_inst_637_, v_a_638_, v_b_639_);
v___x_641_ = lean_unbox(v___x_640_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; 
v___x_642_ = 1;
return v___x_642_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = 0;
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___redArg___boxed(lean_object* v_inst_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_instDecidableRelLt___redArg(v_inst_644_, v_a_645_, v_b_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLt(lean_object* v_00_u03b1_649_, lean_object* v_inst_650_, lean_object* v_a_651_, lean_object* v_b_652_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_apply_2(v_inst_650_, v_a_651_, v_b_652_);
v___x_654_ = lean_unbox(v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 1;
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLt___boxed(lean_object* v_00_u03b1_657_, lean_object* v_inst_658_, lean_object* v_a_659_, lean_object* v_b_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_instDecidableRelLt(v_00_u03b1_657_, v_inst_658_, v_a_659_, v_b_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd(lean_object* v_00_u03b1_663_, lean_object* v_inst_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_box(0);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_leOfOrd___boxed(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_leOfOrd(v_00_u03b1_666_, v_inst_667_);
lean_dec_ref(v_inst_667_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe___redArg(lean_object* v_inst_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_apply_2(v_inst_669_, v_x_670_, v_x_671_);
v___x_673_ = lean_unbox(v___x_672_);
if (v___x_673_ == 2)
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
else
{
uint8_t v___x_675_; 
v___x_675_ = 1;
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___redArg___boxed(lean_object* v_inst_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_instDecidableRelLe___redArg(v_inst_676_, v_x_677_, v_x_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l_instDecidableRelLe(lean_object* v_00_u03b1_681_, lean_object* v_inst_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_apply_2(v_inst_682_, v_x_683_, v_x_684_);
v___x_686_ = lean_unbox(v___x_685_);
if (v___x_686_ == 2)
{
uint8_t v___x_687_; 
v___x_687_ = 0;
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 1;
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableRelLe___boxed(lean_object* v_00_u03b1_689_, lean_object* v_inst_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_instDecidableRelLe(v_00_u03b1_689_, v_inst_690_, v_x_691_, v_x_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq___redArg(lean_object* v_ord_695_){
_start:
{
lean_object* v___f_696_; 
v___f_696_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_696_, 0, v_ord_695_);
return v___f_696_;
}
}
LEAN_EXPORT lean_object* l_Ord_toBEq(lean_object* v_00_u03b1_697_, lean_object* v_ord_698_){
_start:
{
lean_object* v___f_699_; 
v___f_699_ = lean_alloc_closure((void*)(l_beqOfOrd___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_699_, 0, v_ord_698_);
return v___f_699_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT(lean_object* v_00_u03b1_700_, lean_object* v_ord_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_box(0);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLT___boxed(lean_object* v_00_u03b1_703_, lean_object* v_ord_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Ord_toLT(v_00_u03b1_703_, v_ord_704_);
lean_dec_ref(v_ord_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE(lean_object* v_00_u03b1_706_, lean_object* v_ord_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Ord_toLE___boxed(lean_object* v_00_u03b1_709_, lean_object* v_ord_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Ord_toLE(v_00_u03b1_709_, v_ord_710_);
lean_dec_ref(v_ord_710_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_Ord_opposite___redArg___lam__0(lean_object* v_ord_712_, lean_object* v_x_713_, lean_object* v_y_714_){
_start:
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_apply_2(v_ord_712_, v_y_714_, v_x_713_);
v___x_716_ = lean_unbox(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object* v_ord_717_, lean_object* v_x_718_, lean_object* v_y_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Ord_opposite___redArg___lam__0(v_ord_717_, v_x_718_, v_y_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite___redArg(lean_object* v_ord_722_){
_start:
{
lean_object* v___f_723_; 
v___f_723_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_723_, 0, v_ord_722_);
return v___f_723_;
}
}
LEAN_EXPORT lean_object* l_Ord_opposite(lean_object* v_00_u03b1_724_, lean_object* v_ord_725_){
_start:
{
lean_object* v___f_726_; 
v___f_726_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_726_, 0, v_ord_725_);
return v___f_726_;
}
}
LEAN_EXPORT lean_object* l_Ord_on___redArg(lean_object* v_x_727_, lean_object* v_f_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_729_, 0, lean_box(0));
lean_closure_set(v___x_729_, 1, lean_box(0));
lean_closure_set(v___x_729_, 2, v_x_727_);
lean_closure_set(v___x_729_, 3, v_f_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Ord_on(lean_object* v_00_u03b2_730_, lean_object* v_00_u03b1_731_, lean_object* v_x_732_, lean_object* v_f_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_734_, 0, lean_box(0));
lean_closure_set(v___x_734_, 1, lean_box(0));
lean_closure_set(v___x_734_, 2, v_x_732_);
lean_closure_set(v___x_734_, 3, v_f_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex___redArg(lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_lexOrd___redArg(v_x_735_, v_x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_lexOrd___redArg(v_x_740_, v_x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27___redArg(lean_object* v_ord_u2081_743_, lean_object* v_ord_u2082_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, lean_box(0));
lean_closure_set(v___x_745_, 2, v_ord_u2081_743_);
lean_closure_set(v___x_745_, 3, v_ord_u2082_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Ord_lex_x27(lean_object* v_00_u03b1_746_, lean_object* v_ord_u2081_747_, lean_object* v_ord_u2082_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_749_, 0, lean_box(0));
lean_closure_set(v___x_749_, 1, lean_box(0));
lean_closure_set(v___x_749_, 2, v_ord_u2081_747_);
lean_closure_set(v___x_749_, 3, v_ord_u2082_748_);
return v___x_749_;
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
