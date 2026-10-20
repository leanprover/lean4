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
LEAN_EXPORT uint8_t l_String_Legacy_instDecidableEqIterator_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_String_Legacy_instDecidableEqIterator(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_instDecidableEqIterator___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_String_Legacy_instDecidableEqIterator(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_mkIterator(lean_object* v_s_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_s_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_iter(lean_object* v_s_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v_s_29_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0(lean_object* v_i_32_){
_start:
{
lean_object* v_s_33_; lean_object* v_i_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_s_33_ = lean_ctor_get(v_i_32_, 0);
v_i_34_ = lean_ctor_get(v_i_32_, 1);
v___x_35_ = lean_string_utf8_byte_size(v_s_33_);
v___x_36_ = lean_nat_sub(v___x_35_, v_i_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_instSizeOfIterator___lam__0___boxed(lean_object* v_i_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_String_Legacy_instSizeOfIterator___lam__0(v_i_37_);
lean_dec_ref(v_i_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString(lean_object* v_self_41_){
_start:
{
lean_object* v_s_42_; 
v_s_42_ = lean_ctor_get(v_self_41_, 0);
lean_inc_ref(v_s_42_);
return v_s_42_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toString___boxed(lean_object* v_self_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_String_Legacy_Iterator_toString(v_self_43_);
lean_dec_ref(v_self_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes(lean_object* v_x_45_){
_start:
{
lean_object* v_s_46_; lean_object* v_i_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_s_46_ = lean_ctor_get(v_x_45_, 0);
v_i_47_ = lean_ctor_get(v_x_45_, 1);
v___x_48_ = lean_string_utf8_byte_size(v_s_46_);
v___x_49_ = lean_nat_sub(v___x_48_, v_i_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingBytes___boxed(lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_String_Legacy_Iterator_remainingBytes(v_x_50_);
lean_dec_ref(v_x_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos(lean_object* v_self_52_){
_start:
{
lean_object* v_i_53_; 
v_i_53_ = lean_ctor_get(v_self_52_, 1);
lean_inc(v_i_53_);
return v_i_53_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_pos___boxed(lean_object* v_self_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_String_Legacy_Iterator_pos(v_self_54_);
lean_dec_ref(v_self_54_);
return v_res_55_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr(lean_object* v_x_56_){
_start:
{
lean_object* v_s_57_; lean_object* v_i_58_; uint32_t v___x_59_; 
v_s_57_ = lean_ctor_get(v_x_56_, 0);
v_i_58_ = lean_ctor_get(v_x_56_, 1);
v___x_59_ = lean_string_utf8_get(v_s_57_, v_i_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr___boxed(lean_object* v_x_60_){
_start:
{
uint32_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_String_Legacy_Iterator_curr(v_x_60_);
lean_dec_ref(v_x_60_);
v_r_62_ = lean_box_uint32(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next(lean_object* v_x_63_){
_start:
{
lean_object* v_s_64_; lean_object* v_i_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_73_; 
v_s_64_ = lean_ctor_get(v_x_63_, 0);
v_i_65_ = lean_ctor_get(v_x_63_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_63_);
if (v_isSharedCheck_73_ == 0)
{
v___x_67_ = v_x_63_;
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_i_65_);
lean_inc(v_s_64_);
lean_dec(v_x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_string_utf8_next(v_s_64_, v_i_65_);
lean_dec(v_i_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_69_);
v___x_71_ = v___x_67_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_s_64_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prev(lean_object* v_x_74_){
_start:
{
lean_object* v_s_75_; lean_object* v_i_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_s_75_ = lean_ctor_get(v_x_74_, 0);
v_i_76_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_x_74_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_i_76_);
lean_inc(v_s_75_);
lean_dec(v_x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_string_utf8_prev(v_s_75_, v_i_76_);
lean_dec(v_i_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_s_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_atEnd(lean_object* v_x_85_){
_start:
{
lean_object* v_s_86_; lean_object* v_i_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_s_86_ = lean_ctor_get(v_x_85_, 0);
v_i_87_ = lean_ctor_get(v_x_85_, 1);
v___x_88_ = lean_string_utf8_byte_size(v_s_86_);
v___x_89_ = lean_nat_dec_le(v___x_88_, v_i_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_atEnd___boxed(lean_object* v_x_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_String_Legacy_Iterator_atEnd(v_x_90_);
lean_dec_ref(v_x_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_hasNext(lean_object* v_x_93_){
_start:
{
lean_object* v_s_94_; lean_object* v_i_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_s_94_ = lean_ctor_get(v_x_93_, 0);
v_i_95_ = lean_ctor_get(v_x_93_, 1);
v___x_96_ = lean_string_utf8_byte_size(v_s_94_);
v___x_97_ = lean_nat_dec_lt(v_i_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasNext___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_String_Legacy_Iterator_hasNext(v_x_98_);
lean_dec_ref(v_x_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_String_Legacy_Iterator_hasPrev(lean_object* v_x_101_){
_start:
{
lean_object* v_i_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_i_102_ = lean_ctor_get(v_x_101_, 1);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_lt(v___x_103_, v_i_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_hasPrev___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_String_Legacy_Iterator_hasPrev(v_x_105_);
lean_dec_ref(v_x_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object* v_it_108_){
_start:
{
lean_object* v_s_109_; lean_object* v_i_110_; uint32_t v___x_111_; 
v_s_109_ = lean_ctor_get(v_it_108_, 0);
v_i_110_ = lean_ctor_get(v_it_108_, 1);
v___x_111_ = lean_string_utf8_get_fast(v_s_109_, v_i_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object* v_it_112_){
_start:
{
uint32_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_112_);
lean_dec_ref(v_it_112_);
v_r_114_ = lean_box_uint32(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27(lean_object* v_it_115_, lean_object* v_h_116_){
_start:
{
lean_object* v_s_117_; lean_object* v_i_118_; uint32_t v___x_119_; 
v_s_117_ = lean_ctor_get(v_it_115_, 0);
v_i_118_ = lean_ctor_get(v_it_115_, 1);
v___x_119_ = lean_string_utf8_get_fast(v_s_117_, v_i_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object* v_it_120_, lean_object* v_h_121_){
_start:
{
uint32_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_String_Legacy_Iterator_curr_x27(v_it_120_, v_h_121_);
lean_dec_ref(v_it_120_);
v_r_123_ = lean_box_uint32(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object* v_it_124_){
_start:
{
lean_object* v_s_125_; lean_object* v_i_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
v_s_125_ = lean_ctor_get(v_it_124_, 0);
v_i_126_ = lean_ctor_get(v_it_124_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_it_124_);
if (v_isSharedCheck_134_ == 0)
{
v___x_128_ = v_it_124_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_i_126_);
lean_inc(v_s_125_);
lean_dec(v_it_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_string_utf8_next_fast(v_s_125_, v_i_126_);
lean_dec(v_i_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_s_125_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object* v_it_135_, lean_object* v_h_136_){
_start:
{
lean_object* v_s_137_; lean_object* v_i_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_s_137_ = lean_ctor_get(v_it_135_, 0);
v_i_138_ = lean_ctor_get(v_it_135_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_it_135_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_it_135_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_i_138_);
lean_inc(v_s_137_);
lean_dec(v_it_135_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_string_utf8_next_fast(v_s_137_, v_i_138_);
lean_dec(v_i_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_s_137_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object* v_x_147_){
_start:
{
lean_object* v_s_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
v_s_148_ = lean_ctor_get(v_x_147_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_x_147_, 1);
lean_dec(v_unused_157_);
v___x_150_ = v_x_147_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_s_148_);
lean_dec(v_x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_string_utf8_byte_size(v_s_148_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_s_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_s_160_; lean_object* v_i_161_; lean_object* v_s_162_; lean_object* v_i_163_; uint8_t v___x_164_; 
v_s_160_ = lean_ctor_get(v_x_158_, 0);
v_i_161_ = lean_ctor_get(v_x_158_, 1);
v_s_162_ = lean_ctor_get(v_x_159_, 0);
v_i_163_ = lean_ctor_get(v_x_159_, 1);
v___x_164_ = lean_string_dec_eq(v_s_160_, v_s_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_i_163_, v___x_166_);
v___x_168_ = lean_nat_dec_le(v___x_167_, v_i_161_);
lean_dec(v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_string_utf8_extract(v_s_160_, v_i_161_, v_i_163_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_String_Legacy_Iterator_extract(v_x_171_, v_x_172_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_x_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_zero_176_; uint8_t v_isZero_177_; 
v_zero_176_ = lean_unsigned_to_nat(0u);
v_isZero_177_ = lean_nat_dec_eq(v_x_175_, v_zero_176_);
if (v_isZero_177_ == 1)
{
lean_dec(v_x_175_);
return v_x_174_;
}
else
{
lean_object* v_s_178_; lean_object* v_i_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_190_; 
v_s_178_ = lean_ctor_get(v_x_174_, 0);
v_i_179_ = lean_ctor_get(v_x_174_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_190_ == 0)
{
v___x_181_ = v_x_174_;
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_i_179_);
lean_inc(v_s_178_);
lean_dec(v_x_174_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_one_183_; lean_object* v_n_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v_one_183_ = lean_unsigned_to_nat(1u);
v_n_184_ = lean_nat_sub(v_x_175_, v_one_183_);
lean_dec(v_x_175_);
v___x_185_ = lean_string_utf8_next(v_s_178_, v_i_179_);
lean_dec(v_i_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_185_);
v___x_187_ = v___x_181_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_s_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v_x_174_ = v___x_187_;
v_x_175_ = v_n_184_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object* v_x_191_){
_start:
{
lean_object* v_s_192_; lean_object* v_i_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_s_192_ = lean_ctor_get(v_x_191_, 0);
v_i_193_ = lean_ctor_get(v_x_191_, 1);
v___x_194_ = lean_string_utf8_byte_size(v_s_192_);
v___x_195_ = lean_string_utf8_extract(v_s_192_, v_i_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_String_Legacy_Iterator_remainingToString(v_x_196_);
lean_dec_ref(v_x_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v_zero_200_; uint8_t v_isZero_201_; 
v_zero_200_ = lean_unsigned_to_nat(0u);
v_isZero_201_ = lean_nat_dec_eq(v_x_199_, v_zero_200_);
if (v_isZero_201_ == 1)
{
lean_dec(v_x_199_);
return v_x_198_;
}
else
{
lean_object* v_s_202_; lean_object* v_i_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_214_; 
v_s_202_ = lean_ctor_get(v_x_198_, 0);
v_i_203_ = lean_ctor_get(v_x_198_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_214_ == 0)
{
v___x_205_ = v_x_198_;
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_i_203_);
lean_inc(v_s_202_);
lean_dec(v_x_198_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_one_207_; lean_object* v_n_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v_one_207_ = lean_unsigned_to_nat(1u);
v_n_208_ = lean_nat_sub(v_x_199_, v_one_207_);
lean_dec(v_x_199_);
v___x_209_ = lean_string_utf8_next(v_s_202_, v_i_203_);
lean_dec(v_i_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_209_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_s_202_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v_x_198_ = v___x_211_;
v_x_199_ = v_n_208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_zero_217_; uint8_t v_isZero_218_; 
v_zero_217_ = lean_unsigned_to_nat(0u);
v_isZero_218_ = lean_nat_dec_eq(v_x_216_, v_zero_217_);
if (v_isZero_218_ == 1)
{
lean_dec(v_x_216_);
return v_x_215_;
}
else
{
lean_object* v_s_219_; lean_object* v_i_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_231_; 
v_s_219_ = lean_ctor_get(v_x_215_, 0);
v_i_220_ = lean_ctor_get(v_x_215_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_231_ == 0)
{
v___x_222_ = v_x_215_;
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_i_220_);
lean_inc(v_s_219_);
lean_dec(v_x_215_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_one_224_; lean_object* v_n_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v_one_224_ = lean_unsigned_to_nat(1u);
v_n_225_ = lean_nat_sub(v_x_216_, v_one_224_);
lean_dec(v_x_216_);
v___x_226_ = lean_string_utf8_prev(v_s_219_, v_i_220_);
lean_dec(v_i_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_226_);
v___x_228_ = v___x_222_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_s_219_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_x_215_ = v___x_228_;
v_x_216_ = v_n_225_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_268_ = l_String_toRawSubstring_x27(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_295_ = l_Lean_Syntax_isOfKind(v_x_291_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_box(1);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_293_);
return v___x_297_;
}
else
{
lean_object* v_quotContext_298_; lean_object* v_currMacroScope_299_; lean_object* v_ref_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_quotContext_298_ = lean_ctor_get(v_a_292_, 1);
v_currMacroScope_299_ = lean_ctor_get(v_a_292_, 2);
v_ref_300_ = lean_ctor_get(v_a_292_, 5);
v___x_301_ = 0;
v___x_302_ = l_Lean_SourceInfo_fromRef(v_ref_300_, v___x_301_);
v___x_303_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_304_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_302_, 10);
v___x_305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_307_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_308_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_309_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_310_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_302_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
v___x_312_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
v___x_313_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22));
lean_inc(v_currMacroScope_299_);
lean_inc(v_quotContext_298_);
v___x_314_ = l_Lean_addMacroScope(v_quotContext_298_, v___x_313_, v_currMacroScope_299_);
v___x_315_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24));
v___x_316_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_316_, 0, v___x_302_);
lean_ctor_set(v___x_316_, 1, v___x_312_);
lean_ctor_set(v___x_316_, 2, v___x_314_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
v___x_317_ = l_Lean_Syntax_node2(v___x_302_, v___x_310_, v___x_311_, v___x_316_);
v___x_318_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_302_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_321_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_302_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
v___x_323_ = l_Lean_Syntax_node1(v___x_302_, v___x_321_, v___x_322_);
v___x_324_ = l_Lean_Syntax_node3(v___x_302_, v___x_308_, v___x_317_, v___x_319_, v___x_323_);
v___x_325_ = l_Lean_Syntax_node1(v___x_302_, v___x_307_, v___x_324_);
v___x_326_ = l_Lean_Syntax_node1(v___x_302_, v___x_306_, v___x_325_);
v___x_327_ = l_Lean_Syntax_node2(v___x_302_, v___x_303_, v___x_305_, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v_a_293_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_332_;
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_335_ = l_String_toRawSubstring_x27(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_352_ = l_Lean_Syntax_isOfKind(v_x_348_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(1);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
return v___x_354_;
}
else
{
lean_object* v_quotContext_355_; lean_object* v_currMacroScope_356_; lean_object* v_ref_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_quotContext_355_ = lean_ctor_get(v_a_349_, 1);
v_currMacroScope_356_ = lean_ctor_get(v_a_349_, 2);
v_ref_357_ = lean_ctor_get(v_a_349_, 5);
v___x_358_ = 0;
v___x_359_ = l_Lean_SourceInfo_fromRef(v_ref_357_, v___x_358_);
v___x_360_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_361_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_359_, 10);
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_364_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_365_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_366_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_367_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_359_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
v___x_369_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_370_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc(v_currMacroScope_356_);
lean_inc(v_quotContext_355_);
v___x_371_ = l_Lean_addMacroScope(v_quotContext_355_, v___x_370_, v_currMacroScope_356_);
v___x_372_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5));
v___x_373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_373_, 0, v___x_359_);
lean_ctor_set(v___x_373_, 1, v___x_369_);
lean_ctor_set(v___x_373_, 2, v___x_371_);
lean_ctor_set(v___x_373_, 3, v___x_372_);
v___x_374_ = l_Lean_Syntax_node2(v___x_359_, v___x_367_, v___x_368_, v___x_373_);
v___x_375_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_359_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_378_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_359_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
v___x_380_ = l_Lean_Syntax_node1(v___x_359_, v___x_378_, v___x_379_);
v___x_381_ = l_Lean_Syntax_node3(v___x_359_, v___x_365_, v___x_374_, v___x_376_, v___x_380_);
v___x_382_ = l_Lean_Syntax_node1(v___x_359_, v___x_364_, v___x_381_);
v___x_383_ = l_Lean_Syntax_node1(v___x_359_, v___x_363_, v___x_382_);
v___x_384_ = l_Lean_Syntax_node2(v___x_359_, v___x_360_, v___x_362_, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_a_350_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_386_, v_a_387_, v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr(lean_object* v_x_390_, uint32_t v_x_391_){
_start:
{
lean_object* v_s_392_; lean_object* v_i_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_s_392_ = lean_ctor_get(v_x_390_, 0);
v_i_393_ = lean_ctor_get(v_x_390_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_x_390_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_i_393_);
lean_inc(v_s_392_);
lean_dec(v_x_390_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_string_utf8_set(v_s_392_, v_i_393_, v_x_391_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_i_393_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
uint32_t v_x_15__boxed_404_; lean_object* v_res_405_; 
v_x_15__boxed_404_ = lean_unbox_uint32(v_x_403_);
lean_dec(v_x_403_);
v_res_405_ = l_String_Legacy_Iterator_setCurr(v_x_402_, v_x_15__boxed_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object* v_it_406_, lean_object* v_p_407_){
_start:
{
lean_object* v_s_408_; lean_object* v_i_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_s_408_ = lean_ctor_get(v_it_406_, 0);
v_i_409_ = lean_ctor_get(v_it_406_, 1);
v___x_410_ = lean_string_utf8_byte_size(v_s_408_);
v___x_411_ = lean_nat_dec_le(v___x_410_, v_i_409_);
if (v___x_411_ == 0)
{
uint32_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_412_ = lean_string_utf8_get(v_s_408_, v_i_409_);
v___x_413_ = lean_box_uint32(v___x_412_);
lean_inc_ref(v_p_407_);
v___x_414_ = lean_apply_1(v_p_407_, v___x_413_);
v___x_415_ = lean_unbox(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
lean_inc(v_i_409_);
lean_inc_ref(v_s_408_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_it_406_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_it_406_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_it_406_, 0);
lean_dec(v_unused_426_);
v___x_417_ = v_it_406_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_it_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_string_utf8_next(v_s_408_, v_i_409_);
lean_dec(v_i_409_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_s_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_it_406_ = v___x_421_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_407_);
return v_it_406_;
}
}
else
{
lean_dec_ref(v_p_407_);
return v_it_406_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object* v_it_427_, lean_object* v_init_428_, lean_object* v_f_429_){
_start:
{
lean_object* v_s_430_; lean_object* v_i_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_s_430_ = lean_ctor_get(v_it_427_, 0);
v_i_431_ = lean_ctor_get(v_it_427_, 1);
v___x_432_ = lean_string_utf8_byte_size(v_s_430_);
v___x_433_ = lean_nat_dec_le(v___x_432_, v_i_431_);
if (v___x_433_ == 0)
{
uint32_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_string_utf8_get(v_s_430_, v_i_431_);
v___x_435_ = lean_box_uint32(v___x_434_);
lean_inc_ref(v_f_429_);
lean_inc(v_init_428_);
v___x_436_ = lean_apply_2(v_f_429_, v_init_428_, v___x_435_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
lean_inc(v_i_431_);
lean_inc_ref(v_s_430_);
lean_dec(v_init_428_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_it_427_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_447_ = lean_ctor_get(v_it_427_, 1);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_it_427_, 0);
lean_dec(v_unused_448_);
v___x_438_ = v_it_427_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_it_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v_val_440_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_436_, 1);
v___x_441_ = lean_string_utf8_next(v_s_430_, v_i_431_);
lean_dec(v_i_431_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_s_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v_it_427_ = v___x_443_;
v_init_428_ = v_val_440_;
goto _start;
}
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_436_);
lean_dec_ref(v_f_429_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_init_428_);
lean_ctor_set(v___x_449_, 1, v_it_427_);
return v___x_449_;
}
}
else
{
lean_object* v___x_450_; 
lean_dec_ref(v_f_429_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_init_428_);
lean_ctor_set(v___x_450_, 1, v_it_427_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object* v_00_u03b1_451_, lean_object* v_it_452_, lean_object* v_init_453_, lean_object* v_f_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_452_, v_init_453_, v_f_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object* v_x_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
if (lean_obj_tag(v_x_456_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_460_; 
lean_dec(v_h__2_458_);
v_val_459_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v_x_456_, 1);
v___x_460_ = lean_apply_1(v_h__1_457_, v_val_459_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_h__1_457_);
v___x_461_ = lean_apply_2(v_h__2_458_, v_x_456_, lean_box(0));
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object* v_00_u03b1_462_, lean_object* v_motive_463_, lean_object* v_x_464_, lean_object* v_h__1_465_, lean_object* v_h__2_466_){
_start:
{
if (lean_obj_tag(v_x_464_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; 
lean_dec(v_h__2_466_);
v_val_467_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_x_464_, 1);
v___x_468_ = lean_apply_1(v_h__1_465_, v_val_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_h__1_465_);
v___x_469_ = lean_apply_2(v_h__2_466_, v_x_464_, lean_box(0));
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object* v_x_470_){
_start:
{
lean_object* v_str_471_; lean_object* v_startPos_472_; lean_object* v___x_473_; 
v_str_471_ = lean_ctor_get(v_x_470_, 0);
v_startPos_472_ = lean_ctor_get(v_x_470_, 1);
lean_inc(v_startPos_472_);
lean_inc_ref(v_str_471_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v_str_471_);
lean_ctor_set(v___x_473_, 1, v_startPos_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Substring_Raw_toLegacyIterator(v_x_474_);
lean_dec_ref(v_x_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_s_490_; lean_object* v_i_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_511_; 
v_s_490_ = lean_ctor_get(v_x_488_, 0);
v_i_491_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_511_ == 0)
{
v___x_493_ = v_x_488_;
v_isShared_494_ = v_isSharedCheck_511_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_i_491_);
lean_inc(v_s_490_);
lean_dec(v_x_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_511_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_495_ = ((lean_object*)(l_instReprIterator___lam__0___closed__1));
v___x_496_ = l_String_quote(v_s_490_);
v___x_497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 5);
lean_ctor_set(v___x_493_, 1, v___x_497_);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_510_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_500_ = ((lean_object*)(l_instReprIterator___lam__0___closed__3));
v___x_501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = ((lean_object*)(l_instReprIterator___lam__0___closed__5));
v___x_503_ = l_Nat_reprFast(v_i_491_);
v___x_504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_502_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = ((lean_object*)(l_instReprIterator___lam__0___closed__7));
v___x_507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_501_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Repr_addAppParen(v___x_508_, v_x_489_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_instReprIterator___lam__0(v_x_512_, v_x_513_);
lean_dec(v_x_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* v_it_517_){
_start:
{
lean_object* v_s_518_; lean_object* v_i_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_s_518_ = lean_ctor_get(v_it_517_, 0);
v_i_519_ = lean_ctor_get(v_it_517_, 1);
v___x_520_ = lean_string_utf8_byte_size(v_s_518_);
v___x_521_ = lean_string_utf8_extract(v_s_518_, v_i_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* v_it_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_instToStringIterator___lam__0(v_it_522_);
lean_dec_ref(v_it_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* v_s_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_s_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* v_s_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_s_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object* v_a_532_){
_start:
{
lean_object* v_s_533_; lean_object* v_i_534_; uint32_t v___x_535_; 
v_s_533_ = lean_ctor_get(v_a_532_, 0);
v_i_534_ = lean_ctor_get(v_a_532_, 1);
v___x_535_ = lean_string_utf8_get(v_s_533_, v_i_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* v_a_536_){
_start:
{
uint32_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_String_Iterator_curr(v_a_536_);
lean_dec_ref(v_a_536_);
v_r_538_ = lean_box_uint32(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* v_a_539_){
_start:
{
lean_object* v_s_540_; lean_object* v_i_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_s_540_ = lean_ctor_get(v_a_539_, 0);
v_i_541_ = lean_ctor_get(v_a_539_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_543_ = v_a_539_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_i_541_);
lean_inc(v_s_540_);
lean_dec(v_a_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_string_utf8_next(v_s_540_, v_i_541_);
lean_dec(v_i_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_s_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object* v_a_550_){
_start:
{
lean_object* v_s_551_; lean_object* v_i_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_s_551_ = lean_ctor_get(v_a_550_, 0);
v_i_552_ = lean_ctor_get(v_a_550_, 1);
v___x_553_ = lean_string_utf8_byte_size(v_s_551_);
v___x_554_ = lean_nat_dec_lt(v_i_552_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object* v_a_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_String_Iterator_hasNext(v_a_555_);
lean_dec_ref(v_a_555_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object* v_a_558_){
_start:
{
lean_object* v_str_559_; lean_object* v_startPos_560_; lean_object* v___x_561_; 
v_str_559_ = lean_ctor_get(v_a_558_, 0);
v_startPos_560_ = lean_ctor_get(v_a_558_, 1);
lean_inc(v_startPos_560_);
lean_inc_ref(v_str_559_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_str_559_);
lean_ctor_set(v___x_561_, 1, v_startPos_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Substring_toIterator(v_a_562_);
lean_dec_ref(v_a_562_);
return v_res_563_;
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
