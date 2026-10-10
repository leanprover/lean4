// Lean compiler output
// Module: Init.Data.String.Iterator
// Imports: public import Init.Data.String.Modify
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Legacy_instDecidableEqIterator_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Legacy_instDecidableEqIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Legacy_instInhabitedIterator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Legacy_instInhabitedIterator_default___closed__0 = (const lean_object*)&l_String_Legacy_instInhabitedIterator_default___closed__0_value;
static const lean_ctor_object l_String_Legacy_instInhabitedIterator_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Legacy_instInhabitedIterator_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Legacy_instInhabitedIterator_default___closed__1 = (const lean_object*)&l_String_Legacy_instInhabitedIterator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_String_Legacy_instInhabitedIterator_default = (const lean_object*)&l_String_Legacy_instInhabitedIterator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_String_Legacy_instInhabitedIterator = (const lean_object*)&l_String_Legacy_instInhabitedIterator_default___closed__1_value;
LEAN_EXPORT lean_object* l_String_Legacy_mkIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_iter(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Legacy_instSizeOfIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Legacy_instSizeOfIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Legacy_instSizeOfIterator___closed__0 = (const lean_object*)&l_String_Legacy_instSizeOfIterator___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Legacy_instSizeOfIterator = (const lean_object*)&l_String_Legacy_instSizeOfIterator___closed__0_value;
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prev(lean_object*);
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_atEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_atEnd___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasNext___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_hasPrev(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasPrev___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object*, lean_object*);
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "String.Legacy.Iterator.sizeOf_next_lt_of_hasNext"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value;
static lean_once_cell_t l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Legacy"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Iterator"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "sizeOf_next_lt_of_hasNext"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(246, 18, 100, 86, 169, 238, 29, 225)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(60, 192, 246, 57, 139, 252, 80, 191)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(81, 211, 19, 24, 247, 70, 181, 248)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value;
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "String.Legacy.Iterator.sizeOf_next_lt_of_atEnd"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value;
static lean_once_cell_t l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1;
static const lean_string_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "sizeOf_next_lt_of_atEnd"};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(246, 18, 100, 86, 169, 238, 29, 225)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(60, 192, 246, 57, 139, 252, 80, 191)}};
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2),((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(217, 254, 72, 171, 243, 20, 171, 57)}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value;
static const lean_ctor_object l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5 = (const lean_object*)&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value;
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object*);
static const lean_string_object l_instReprIterator___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "String.Iterator.mk "};
static const lean_object* l_instReprIterator___lam__0___closed__0 = (const lean_object*)&l_instReprIterator___lam__0___closed__0_value;
static const lean_ctor_object l_instReprIterator___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprIterator___lam__0___closed__0_value)}};
static const lean_object* l_instReprIterator___lam__0___closed__1 = (const lean_object*)&l_instReprIterator___lam__0___closed__1_value;
static const lean_string_object l_instReprIterator___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_instReprIterator___lam__0___closed__2 = (const lean_object*)&l_instReprIterator___lam__0___closed__2_value;
static const lean_ctor_object l_instReprIterator___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprIterator___lam__0___closed__2_value)}};
static const lean_object* l_instReprIterator___lam__0___closed__3 = (const lean_object*)&l_instReprIterator___lam__0___closed__3_value;
static const lean_string_object l_instReprIterator___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l_instReprIterator___lam__0___closed__4 = (const lean_object*)&l_instReprIterator___lam__0___closed__4_value;
static const lean_ctor_object l_instReprIterator___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprIterator___lam__0___closed__4_value)}};
static const lean_object* l_instReprIterator___lam__0___closed__5 = (const lean_object*)&l_instReprIterator___lam__0___closed__5_value;
static const lean_string_object l_instReprIterator___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_instReprIterator___lam__0___closed__6 = (const lean_object*)&l_instReprIterator___lam__0___closed__6_value;
static const lean_ctor_object l_instReprIterator___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprIterator___lam__0___closed__6_value)}};
static const lean_object* l_instReprIterator___lam__0___closed__7 = (const lean_object*)&l_instReprIterator___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprIterator___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprIterator___closed__0 = (const lean_object*)&l_instReprIterator___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprIterator = (const lean_object*)&l_instReprIterator___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringIterator___closed__0 = (const lean_object*)&l_instToStringIterator___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringIterator = (const lean_object*)&l_instToStringIterator___closed__0_value;
LEAN_EXPORT lean_object* l_String_iter(lean_object*);
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object*);
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object*);
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object*);
uint8_t l_String_Legacy_instDecidableEqIterator_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_s_3_; lean_object* v_i_4_; lean_object* v_s_5_; lean_object* v_i_6_; uint8_t v___x_7_; 
v_s_3_ = lean_ctor_get(v_x_1_, 0);
v_i_4_ = lean_ctor_get(v_x_1_, 1);
v_s_5_ = lean_ctor_get(v_x_2_, 0);
v_i_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_string_dec_eq(v_s_3_, v_s_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v_decide_8_; 
v_decide_8_ = lean_nat_dec_eq(v_i_4_, v_i_6_);
return v_decide_8_;
}
}
}
LEAN_EXPORT void l_String_Legacy_instDecidableEqIterator_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator_decEq___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_String_Legacy_instDecidableEqIterator(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_14_, v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT void l_String_Legacy_instDecidableEqIterator_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_String_Legacy_instDecidableEqIterator(v_x_14_, v_x_15_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_String_Legacy_instDecidableEqIterator(v_x_18_, v_x_19_);
lean_dec_ref(v_x_19_);
lean_dec_ref(v_x_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_mkIterator(lean_object* v_s_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v_s_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_iter(lean_object* v_s_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v_s_31_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0(lean_object* v_i_34_){
_start:
{
lean_object* v_s_35_; lean_object* v_i_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_s_35_ = lean_ctor_get(v_i_34_, 0);
v_i_36_ = lean_ctor_get(v_i_34_, 1);
v___x_37_ = lean_string_utf8_byte_size(v_s_35_);
v___x_38_ = lean_nat_sub(v___x_37_, v_i_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0___boxed(lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_String_Legacy_instSizeOfIterator___lam__0(v_i_39_);
lean_dec_ref(v_i_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString(lean_object* v_self_43_){
_start:
{
lean_object* v_s_44_; 
v_s_44_ = lean_ctor_get(v_self_43_, 0);
lean_inc_ref(v_s_44_);
return v_s_44_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString___boxed(lean_object* v_self_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_String_Legacy_Iterator_toString(v_self_45_);
lean_dec_ref(v_self_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes(lean_object* v_x_47_){
_start:
{
lean_object* v_s_48_; lean_object* v_i_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_s_48_ = lean_ctor_get(v_x_47_, 0);
v_i_49_ = lean_ctor_get(v_x_47_, 1);
v___x_50_ = lean_string_utf8_byte_size(v_s_48_);
v___x_51_ = lean_nat_sub(v___x_50_, v_i_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_String_Legacy_Iterator_remainingBytes(v_x_52_);
lean_dec_ref(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos(lean_object* v_self_54_){
_start:
{
lean_object* v_i_55_; 
v_i_55_ = lean_ctor_get(v_self_54_, 1);
lean_inc(v_i_55_);
return v_i_55_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos___boxed(lean_object* v_self_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_String_Legacy_Iterator_pos(v_self_56_);
lean_dec_ref(v_self_56_);
return v_res_57_;
}
}
uint32_t l_String_Legacy_Iterator_curr(lean_object* v_x_58_){
_start:
{
lean_object* v_s_59_; lean_object* v_i_60_; uint32_t v___x_61_; 
v_s_59_ = lean_ctor_get(v_x_58_, 0);
v_i_60_ = lean_ctor_get(v_x_58_, 1);
v___x_61_ = lean_string_utf8_get(v_s_59_, v_i_60_);
return v___x_61_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_curr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_58_ = stack[0].m_obj;
uint32_t v_res_62_;
v_res_62_ = l_String_Legacy_Iterator_curr(v_x_58_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr___boxed(lean_object* v_x_63_){
_start:
{
uint32_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_String_Legacy_Iterator_curr(v_x_63_);
lean_dec_ref(v_x_63_);
v_r_65_ = lean_box_uint32(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next(lean_object* v_x_66_){
_start:
{
lean_object* v_s_67_; lean_object* v_i_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_s_67_ = lean_ctor_get(v_x_66_, 0);
v_i_68_ = lean_ctor_get(v_x_66_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v_x_66_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_i_68_);
lean_inc(v_s_67_);
lean_dec(v_x_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_string_utf8_next(v_s_67_, v_i_68_);
lean_dec(v_i_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_s_67_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prev(lean_object* v_x_77_){
_start:
{
lean_object* v_s_78_; lean_object* v_i_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_s_78_ = lean_ctor_get(v_x_77_, 0);
v_i_79_ = lean_ctor_get(v_x_77_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_x_77_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_i_79_);
lean_inc(v_s_78_);
lean_dec(v_x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_string_utf8_prev(v_s_78_, v_i_79_);
lean_dec(v_i_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_s_78_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
uint8_t l_String_Legacy_Iterator_atEnd(lean_object* v_x_88_){
_start:
{
lean_object* v_s_89_; lean_object* v_i_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_s_89_ = lean_ctor_get(v_x_88_, 0);
v_i_90_ = lean_ctor_get(v_x_88_, 1);
v___x_91_ = lean_string_utf8_byte_size(v_s_89_);
v___x_92_ = lean_nat_dec_le(v___x_91_, v_i_90_);
return v___x_92_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_String_Legacy_Iterator_atEnd(v_x_88_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_atEnd___boxed(lean_object* v_x_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_String_Legacy_Iterator_atEnd(v_x_94_);
lean_dec_ref(v_x_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
uint8_t l_String_Legacy_Iterator_hasNext(lean_object* v_x_97_){
_start:
{
lean_object* v_s_98_; lean_object* v_i_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_s_98_ = lean_ctor_get(v_x_97_, 0);
v_i_99_ = lean_ctor_get(v_x_97_, 1);
v___x_100_ = lean_string_utf8_byte_size(v_s_98_);
v___x_101_ = lean_nat_dec_lt(v_i_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_hasNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_97_ = stack[0].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_String_Legacy_Iterator_hasNext(v_x_97_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasNext___boxed(lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_String_Legacy_Iterator_hasNext(v_x_103_);
lean_dec_ref(v_x_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_String_Legacy_Iterator_hasPrev(lean_object* v_x_106_){
_start:
{
lean_object* v_i_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_i_107_ = lean_ctor_get(v_x_106_, 1);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v_i_107_);
return v___x_109_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_hasPrev_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_106_ = stack[0].m_obj;
uint8_t v_res_110_;
v_res_110_ = l_String_Legacy_Iterator_hasPrev(v_x_106_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasPrev___boxed(lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_String_Legacy_Iterator_hasPrev(v_x_111_);
lean_dec_ref(v_x_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object* v_it_114_){
_start:
{
lean_object* v_s_115_; lean_object* v_i_116_; uint32_t v___x_117_; 
v_s_115_ = lean_ctor_get(v_it_114_, 0);
v_i_116_ = lean_ctor_get(v_it_114_, 1);
v___x_117_ = lean_string_utf8_get_fast(v_s_115_, v_i_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_curr_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_114_ = stack[0].m_obj;
uint32_t v_res_118_;
v_res_118_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_114_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object* v_it_119_){
_start:
{
uint32_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_119_);
lean_dec_ref(v_it_119_);
v_r_121_ = lean_box_uint32(v_res_120_);
return v_r_121_;
}
}
uint32_t l_String_Legacy_Iterator_curr_x27(lean_object* v_it_122_, lean_object* v_h_123_){
_start:
{
lean_object* v_s_124_; lean_object* v_i_125_; uint32_t v___x_126_; 
v_s_124_ = lean_ctor_get(v_it_122_, 0);
v_i_125_ = lean_ctor_get(v_it_122_, 1);
v___x_126_ = lean_string_utf8_get_fast(v_s_124_, v_i_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_curr_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_122_ = stack[0].m_obj;
uint32_t v_res_127_;
v_res_127_ = l_String_Legacy_Iterator_curr_x27(v_it_122_, lean_box(0));
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object* v_it_128_, lean_object* v_h_129_){
_start:
{
uint32_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_String_Legacy_Iterator_curr_x27(v_it_128_, v_h_129_);
lean_dec_ref(v_it_128_);
v_r_131_ = lean_box_uint32(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object* v_it_132_){
_start:
{
lean_object* v_s_133_; lean_object* v_i_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_s_133_ = lean_ctor_get(v_it_132_, 0);
v_i_134_ = lean_ctor_get(v_it_132_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_it_132_);
if (v_isSharedCheck_142_ == 0)
{
v___x_136_ = v_it_132_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_i_134_);
lean_inc(v_s_133_);
lean_dec(v_it_132_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_string_utf8_next_fast(v_s_133_, v_i_134_);
lean_dec(v_i_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_s_133_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object* v_it_143_, lean_object* v_h_144_){
_start:
{
lean_object* v_s_145_; lean_object* v_i_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_s_145_ = lean_ctor_get(v_it_143_, 0);
v_i_146_ = lean_ctor_get(v_it_143_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_it_143_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v_it_143_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_i_146_);
lean_inc(v_s_145_);
lean_dec(v_it_143_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_string_utf8_next_fast(v_s_145_, v_i_146_);
lean_dec(v_i_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_s_145_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object* v_x_155_){
_start:
{
lean_object* v_s_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_s_156_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_x_155_, 1);
lean_dec(v_unused_165_);
v___x_158_ = v_x_155_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_s_156_);
lean_dec(v_x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_string_utf8_byte_size(v_s_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_s_156_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_s_168_; lean_object* v_i_169_; lean_object* v_s_170_; lean_object* v_i_171_; uint8_t v___x_172_; 
v_s_168_ = lean_ctor_get(v_x_166_, 0);
v_i_169_ = lean_ctor_get(v_x_166_, 1);
v_s_170_ = lean_ctor_get(v_x_167_, 0);
v_i_171_ = lean_ctor_get(v_x_167_, 1);
v___x_172_ = lean_string_dec_eq(v_s_168_, v_s_170_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_i_171_, v___x_174_);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_i_169_);
lean_dec(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_string_utf8_extract(v_s_168_, v_i_169_, v_i_171_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_String_Legacy_Iterator_extract(v_x_179_, v_x_180_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_zero_184_; uint8_t v_isZero_185_; 
v_zero_184_ = lean_unsigned_to_nat(0u);
v_isZero_185_ = lean_nat_dec_eq(v_x_183_, v_zero_184_);
if (v_isZero_185_ == 1)
{
lean_dec(v_x_183_);
return v_x_182_;
}
else
{
lean_object* v_s_186_; lean_object* v_i_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v_s_186_ = lean_ctor_get(v_x_182_, 0);
v_i_187_ = lean_ctor_get(v_x_182_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_198_ == 0)
{
v___x_189_ = v_x_182_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_i_187_);
lean_inc(v_s_186_);
lean_dec(v_x_182_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_one_191_; lean_object* v_n_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v_one_191_ = lean_unsigned_to_nat(1u);
v_n_192_ = lean_nat_sub(v_x_183_, v_one_191_);
lean_dec(v_x_183_);
v___x_193_ = lean_string_utf8_next(v_s_186_, v_i_187_);
lean_dec(v_i_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_s_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v_x_182_ = v___x_195_;
v_x_183_ = v_n_192_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object* v_x_199_){
_start:
{
lean_object* v_s_200_; lean_object* v_i_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_s_200_ = lean_ctor_get(v_x_199_, 0);
v_i_201_ = lean_ctor_get(v_x_199_, 1);
v___x_202_ = lean_string_utf8_byte_size(v_s_200_);
v___x_203_ = lean_string_utf8_extract(v_s_200_, v_i_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_String_Legacy_Iterator_remainingToString(v_x_204_);
lean_dec_ref(v_x_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_zero_208_; uint8_t v_isZero_209_; 
v_zero_208_ = lean_unsigned_to_nat(0u);
v_isZero_209_ = lean_nat_dec_eq(v_x_207_, v_zero_208_);
if (v_isZero_209_ == 1)
{
lean_dec(v_x_207_);
return v_x_206_;
}
else
{
lean_object* v_s_210_; lean_object* v_i_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_222_; 
v_s_210_ = lean_ctor_get(v_x_206_, 0);
v_i_211_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_222_ == 0)
{
v___x_213_ = v_x_206_;
v_isShared_214_ = v_isSharedCheck_222_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_i_211_);
lean_inc(v_s_210_);
lean_dec(v_x_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_222_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_one_215_; lean_object* v_n_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v_one_215_ = lean_unsigned_to_nat(1u);
v_n_216_ = lean_nat_sub(v_x_207_, v_one_215_);
lean_dec(v_x_207_);
v___x_217_ = lean_string_utf8_next(v_s_210_, v_i_211_);
lean_dec(v_i_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_217_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_s_210_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_221_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_x_206_ = v___x_219_;
v_x_207_ = v_n_216_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_zero_225_; uint8_t v_isZero_226_; 
v_zero_225_ = lean_unsigned_to_nat(0u);
v_isZero_226_ = lean_nat_dec_eq(v_x_224_, v_zero_225_);
if (v_isZero_226_ == 1)
{
lean_dec(v_x_224_);
return v_x_223_;
}
else
{
lean_object* v_s_227_; lean_object* v_i_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_239_; 
v_s_227_ = lean_ctor_get(v_x_223_, 0);
v_i_228_ = lean_ctor_get(v_x_223_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_239_ == 0)
{
v___x_230_ = v_x_223_;
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_i_228_);
lean_inc(v_s_227_);
lean_dec(v_x_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_one_232_; lean_object* v_n_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v_one_232_ = lean_unsigned_to_nat(1u);
v_n_233_ = lean_nat_sub(v_x_224_, v_one_232_);
lean_dec(v_x_224_);
v___x_234_ = lean_string_utf8_prev(v_s_227_, v_i_228_);
lean_dec(v_i_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_234_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_s_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v_x_223_ = v___x_236_;
v_x_224_ = v_n_233_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_276_ = l_String_toRawSubstring_x27(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_303_ = l_Lean_Syntax_isOfKind(v_x_299_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(1);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_301_);
return v___x_305_;
}
else
{
lean_object* v_quotContext_306_; lean_object* v_currMacroScope_307_; lean_object* v_ref_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_quotContext_306_ = lean_ctor_get(v_a_300_, 1);
v_currMacroScope_307_ = lean_ctor_get(v_a_300_, 2);
v_ref_308_ = lean_ctor_get(v_a_300_, 5);
v___x_309_ = 0;
v___x_310_ = l_Lean_SourceInfo_fromRef(v_ref_308_, v___x_309_);
v___x_311_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_312_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_310_, 10);
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_315_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_316_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_317_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_318_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_310_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
v___x_320_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
v___x_321_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22));
lean_inc(v_currMacroScope_307_);
lean_inc(v_quotContext_306_);
v___x_322_ = l_Lean_addMacroScope(v_quotContext_306_, v___x_321_, v_currMacroScope_307_);
v___x_323_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24));
v___x_324_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_324_, 0, v___x_310_);
lean_ctor_set(v___x_324_, 1, v___x_320_);
lean_ctor_set(v___x_324_, 2, v___x_322_);
lean_ctor_set(v___x_324_, 3, v___x_323_);
v___x_325_ = l_Lean_Syntax_node2(v___x_310_, v___x_318_, v___x_319_, v___x_324_);
v___x_326_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_310_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_329_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_310_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
v___x_331_ = l_Lean_Syntax_node1(v___x_310_, v___x_329_, v___x_330_);
v___x_332_ = l_Lean_Syntax_node3(v___x_310_, v___x_316_, v___x_325_, v___x_327_, v___x_331_);
v___x_333_ = l_Lean_Syntax_node1(v___x_310_, v___x_315_, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v___x_310_, v___x_314_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node2(v___x_310_, v___x_311_, v___x_313_, v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_301_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_337_, v_a_338_, v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_340_;
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_343_ = l_String_toRawSubstring_x27(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_360_ = l_Lean_Syntax_isOfKind(v_x_356_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(1);
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
return v___x_362_;
}
else
{
lean_object* v_quotContext_363_; lean_object* v_currMacroScope_364_; lean_object* v_ref_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_quotContext_363_ = lean_ctor_get(v_a_357_, 1);
v_currMacroScope_364_ = lean_ctor_get(v_a_357_, 2);
v_ref_365_ = lean_ctor_get(v_a_357_, 5);
v___x_366_ = 0;
v___x_367_ = l_Lean_SourceInfo_fromRef(v_ref_365_, v___x_366_);
v___x_368_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_369_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_367_, 10);
v___x_370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_372_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_373_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_374_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_375_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_367_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
v___x_377_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_378_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc(v_currMacroScope_364_);
lean_inc(v_quotContext_363_);
v___x_379_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_378_, v_currMacroScope_364_);
v___x_380_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5));
v___x_381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_381_, 0, v___x_367_);
lean_ctor_set(v___x_381_, 1, v___x_377_);
lean_ctor_set(v___x_381_, 2, v___x_379_);
lean_ctor_set(v___x_381_, 3, v___x_380_);
v___x_382_ = l_Lean_Syntax_node2(v___x_367_, v___x_375_, v___x_376_, v___x_381_);
v___x_383_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_367_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_386_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_367_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
v___x_388_ = l_Lean_Syntax_node1(v___x_367_, v___x_386_, v___x_387_);
v___x_389_ = l_Lean_Syntax_node3(v___x_367_, v___x_373_, v___x_382_, v___x_384_, v___x_388_);
v___x_390_ = l_Lean_Syntax_node1(v___x_367_, v___x_372_, v___x_389_);
v___x_391_ = l_Lean_Syntax_node1(v___x_367_, v___x_371_, v___x_390_);
v___x_392_ = l_Lean_Syntax_node2(v___x_367_, v___x_368_, v___x_370_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_a_358_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_394_, v_a_395_, v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_397_;
}
}
lean_object* l_String_Legacy_Iterator_setCurr(lean_object* v_x_398_, uint32_t v_x_399_){
_start:
{
lean_object* v_s_400_; lean_object* v_i_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_s_400_ = lean_ctor_get(v_x_398_, 0);
v_i_401_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v_x_398_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_i_401_);
lean_inc(v_s_400_);
lean_dec(v_x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_string_utf8_set(v_s_400_, v_i_401_, v_x_399_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_i_401_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
LEAN_EXPORT void l_String_Legacy_Iterator_setCurr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_398_ = stack[0].m_obj;
uint32_t v_x_399_ = stack[1].m_num;
lean_object* v_res_410_;
v_res_410_ = l_String_Legacy_Iterator_setCurr(v_x_398_, v_x_399_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint32_t v_x_15__boxed_413_; lean_object* v_res_414_; 
v_x_15__boxed_413_ = lean_unbox_uint32(v_x_412_);
lean_dec(v_x_412_);
v_res_414_ = l_String_Legacy_Iterator_setCurr(v_x_411_, v_x_15__boxed_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object* v_it_415_, lean_object* v_p_416_){
_start:
{
lean_object* v_s_417_; lean_object* v_i_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_s_417_ = lean_ctor_get(v_it_415_, 0);
v_i_418_ = lean_ctor_get(v_it_415_, 1);
v___x_419_ = lean_string_utf8_byte_size(v_s_417_);
v___x_420_ = lean_nat_dec_le(v___x_419_, v_i_418_);
if (v___x_420_ == 0)
{
uint32_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_string_utf8_get(v_s_417_, v_i_418_);
v___x_422_ = lean_box_uint32(v___x_421_);
lean_inc_ref(v_p_416_);
v___x_423_ = lean_apply_1(v_p_416_, v___x_422_);
v___x_424_ = lean_unbox(v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
lean_inc(v_i_418_);
lean_inc_ref(v_s_417_);
v_isSharedCheck_433_ = !lean_is_exclusive(v_it_415_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_434_ = lean_ctor_get(v_it_415_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_it_415_, 0);
lean_dec(v_unused_435_);
v___x_426_ = v_it_415_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_dec(v_it_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_string_utf8_next(v_s_417_, v_i_418_);
lean_dec(v_i_418_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_s_417_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v_it_415_ = v___x_430_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_416_);
return v_it_415_;
}
}
else
{
lean_dec_ref(v_p_416_);
return v_it_415_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object* v_it_436_, lean_object* v_init_437_, lean_object* v_f_438_){
_start:
{
lean_object* v_s_439_; lean_object* v_i_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_s_439_ = lean_ctor_get(v_it_436_, 0);
v_i_440_ = lean_ctor_get(v_it_436_, 1);
v___x_441_ = lean_string_utf8_byte_size(v_s_439_);
v___x_442_ = lean_nat_dec_le(v___x_441_, v_i_440_);
if (v___x_442_ == 0)
{
uint32_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_string_utf8_get(v_s_439_, v_i_440_);
v___x_444_ = lean_box_uint32(v___x_443_);
lean_inc_ref(v_f_438_);
lean_inc(v_init_437_);
v___x_445_ = lean_apply_2(v_f_438_, v_init_437_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
lean_inc(v_i_440_);
lean_inc_ref(v_s_439_);
lean_dec(v_init_437_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_it_436_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; 
v_unused_456_ = lean_ctor_get(v_it_436_, 1);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_it_436_, 0);
lean_dec(v_unused_457_);
v___x_447_ = v_it_436_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_it_436_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_val_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v_val_449_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_445_, 1);
v___x_450_ = lean_string_utf8_next(v_s_439_, v_i_440_);
lean_dec(v_i_440_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_s_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v_it_436_ = v___x_452_;
v_init_437_ = v_val_449_;
goto _start;
}
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v___x_445_);
lean_dec_ref(v_f_438_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_init_437_);
lean_ctor_set(v___x_458_, 1, v_it_436_);
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v_f_438_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_init_437_);
lean_ctor_set(v___x_459_, 1, v_it_436_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object* v_00_u03b1_460_, lean_object* v_it_461_, lean_object* v_init_462_, lean_object* v_f_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_461_, v_init_462_, v_f_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object* v_x_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
if (lean_obj_tag(v_x_465_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; 
lean_dec(v_h__2_467_);
v_val_468_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v_x_465_, 1);
v___x_469_ = lean_apply_1(v_h__1_466_, v_val_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_h__1_466_);
v___x_470_ = lean_apply_2(v_h__2_467_, v_x_465_, lean_box(0));
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object* v_00_u03b1_471_, lean_object* v_motive_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_){
_start:
{
if (lean_obj_tag(v_x_473_) == 1)
{
lean_object* v_val_476_; lean_object* v___x_477_; 
lean_dec(v_h__2_475_);
v_val_476_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_x_473_, 1);
v___x_477_ = lean_apply_1(v_h__1_474_, v_val_476_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
lean_dec(v_h__1_474_);
v___x_478_ = lean_apply_2(v_h__2_475_, v_x_473_, lean_box(0));
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object* v_x_479_){
_start:
{
lean_object* v_str_480_; lean_object* v_startPos_481_; lean_object* v___x_482_; 
v_str_480_ = lean_ctor_get(v_x_479_, 0);
v_startPos_481_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_startPos_481_);
lean_inc_ref(v_str_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_str_480_);
lean_ctor_set(v___x_482_, 1, v_startPos_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Substring_Raw_toLegacyIterator(v_x_483_);
lean_dec_ref(v_x_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
lean_object* v_s_499_; lean_object* v_i_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_520_; 
v_s_499_ = lean_ctor_get(v_x_497_, 0);
v_i_500_ = lean_ctor_get(v_x_497_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_520_ == 0)
{
v___x_502_ = v_x_497_;
v_isShared_503_ = v_isSharedCheck_520_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_i_500_);
lean_inc(v_s_499_);
lean_dec(v_x_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_520_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_504_ = ((lean_object*)(l_instReprIterator___lam__0___closed__1));
v___x_505_ = l_String_quote(v_s_499_);
v___x_506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 5);
lean_ctor_set(v___x_502_, 1, v___x_506_);
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_519_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_509_ = ((lean_object*)(l_instReprIterator___lam__0___closed__3));
v___x_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = ((lean_object*)(l_instReprIterator___lam__0___closed__5));
v___x_512_ = l_Nat_reprFast(v_i_500_);
v___x_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = ((lean_object*)(l_instReprIterator___lam__0___closed__7));
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_510_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_x_498_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_instReprIterator___lam__0(v_x_521_, v_x_522_);
lean_dec(v_x_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* v_it_526_){
_start:
{
lean_object* v_s_527_; lean_object* v_i_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_s_527_ = lean_ctor_get(v_it_526_, 0);
v_i_528_ = lean_ctor_get(v_it_526_, 1);
v___x_529_ = lean_string_utf8_byte_size(v_s_527_);
v___x_530_ = lean_string_utf8_extract(v_s_527_, v_i_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* v_it_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_instToStringIterator___lam__0(v_it_531_);
lean_dec_ref(v_it_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* v_s_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_s_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* v_s_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_s_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
}
uint32_t l_String_Iterator_curr(lean_object* v_a_541_){
_start:
{
lean_object* v_s_542_; lean_object* v_i_543_; uint32_t v___x_544_; 
v_s_542_ = lean_ctor_get(v_a_541_, 0);
v_i_543_ = lean_ctor_get(v_a_541_, 1);
v___x_544_ = lean_string_utf8_get(v_s_542_, v_i_543_);
return v___x_544_;
}
}
LEAN_EXPORT void l_String_Iterator_curr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_541_ = stack[0].m_obj;
uint32_t v_res_545_;
v_res_545_ = l_String_Iterator_curr(v_a_541_);
stack->m_num = v_res_545_;
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* v_a_546_){
_start:
{
uint32_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_String_Iterator_curr(v_a_546_);
lean_dec_ref(v_a_546_);
v_r_548_ = lean_box_uint32(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* v_a_549_){
_start:
{
lean_object* v_s_550_; lean_object* v_i_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_s_550_ = lean_ctor_get(v_a_549_, 0);
v_i_551_ = lean_ctor_get(v_a_549_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_553_ = v_a_549_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_i_551_);
lean_inc(v_s_550_);
lean_dec(v_a_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_string_utf8_next(v_s_550_, v_i_551_);
lean_dec(v_i_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_s_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
uint8_t l_String_Iterator_hasNext(lean_object* v_a_560_){
_start:
{
lean_object* v_s_561_; lean_object* v_i_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_s_561_ = lean_ctor_get(v_a_560_, 0);
v_i_562_ = lean_ctor_get(v_a_560_, 1);
v___x_563_ = lean_string_utf8_byte_size(v_s_561_);
v___x_564_ = lean_nat_dec_lt(v_i_562_, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT void l_String_Iterator_hasNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_560_ = stack[0].m_obj;
uint8_t v_res_565_;
v_res_565_ = l_String_Iterator_hasNext(v_a_560_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object* v_a_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_String_Iterator_hasNext(v_a_566_);
lean_dec_ref(v_a_566_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object* v_a_569_){
_start:
{
lean_object* v_str_570_; lean_object* v_startPos_571_; lean_object* v___x_572_; 
v_str_570_ = lean_ctor_get(v_a_569_, 0);
v_startPos_571_ = lean_ctor_get(v_a_569_, 1);
lean_inc(v_startPos_571_);
lean_inc_ref(v_str_570_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_str_570_);
lean_ctor_set(v___x_572_, 1, v_startPos_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Substring_toIterator(v_a_573_);
lean_dec_ref(v_a_573_);
return v_res_574_;
}
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
