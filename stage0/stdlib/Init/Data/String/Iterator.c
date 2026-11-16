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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* v_x_108_, lean_object* v_h__1_109_){
_start:
{
lean_object* v_s_110_; lean_object* v_i_111_; lean_object* v___x_112_; 
v_s_110_ = lean_ctor_get(v_x_108_, 0);
lean_inc_ref(v_s_110_);
v_i_111_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_i_111_);
lean_dec_ref(v_x_108_);
v___x_112_ = lean_apply_2(v_h__1_109_, v_s_110_, v_i_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter(lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_){
_start:
{
lean_object* v_s_116_; lean_object* v_i_117_; lean_object* v___x_118_; 
v_s_116_ = lean_ctor_get(v_x_114_, 0);
lean_inc_ref(v_s_116_);
v_i_117_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_i_117_);
lean_dec_ref(v_x_114_);
v___x_118_ = lean_apply_2(v_h__1_115_, v_s_116_, v_i_117_);
return v___x_118_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object* v_it_119_){
_start:
{
lean_object* v_s_120_; lean_object* v_i_121_; uint32_t v___x_122_; 
v_s_120_ = lean_ctor_get(v_it_119_, 0);
v_i_121_ = lean_ctor_get(v_it_119_, 1);
v___x_122_ = lean_string_utf8_get_fast(v_s_120_, v_i_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object* v_it_123_){
_start:
{
uint32_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_123_);
lean_dec_ref(v_it_123_);
v_r_125_ = lean_box_uint32(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27(lean_object* v_it_126_, lean_object* v_h_127_){
_start:
{
lean_object* v_s_128_; lean_object* v_i_129_; uint32_t v___x_130_; 
v_s_128_ = lean_ctor_get(v_it_126_, 0);
v_i_129_ = lean_ctor_get(v_it_126_, 1);
v___x_130_ = lean_string_utf8_get_fast(v_s_128_, v_i_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object* v_it_131_, lean_object* v_h_132_){
_start:
{
uint32_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_String_Legacy_Iterator_curr_x27(v_it_131_, v_h_132_);
lean_dec_ref(v_it_131_);
v_r_134_ = lean_box_uint32(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object* v_it_135_){
_start:
{
lean_object* v_s_136_; lean_object* v_i_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
v_s_136_ = lean_ctor_get(v_it_135_, 0);
v_i_137_ = lean_ctor_get(v_it_135_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_it_135_);
if (v_isSharedCheck_145_ == 0)
{
v___x_139_ = v_it_135_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_i_137_);
lean_inc(v_s_136_);
lean_dec(v_it_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_string_utf8_next_fast(v_s_136_, v_i_137_);
lean_dec(v_i_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_s_136_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object* v_it_146_, lean_object* v_h_147_){
_start:
{
lean_object* v_s_148_; lean_object* v_i_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_s_148_ = lean_ctor_get(v_it_146_, 0);
v_i_149_ = lean_ctor_get(v_it_146_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_it_146_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_it_146_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_i_149_);
lean_inc(v_s_148_);
lean_dec(v_it_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_string_utf8_next_fast(v_s_148_, v_i_149_);
lean_dec(v_i_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_s_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object* v_x_158_){
_start:
{
lean_object* v_s_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_s_159_ = lean_ctor_get(v_x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v_x_158_, 1);
lean_dec(v_unused_168_);
v___x_161_ = v_x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_s_159_);
lean_dec(v_x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_string_utf8_byte_size(v_s_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_s_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
lean_object* v_s_171_; lean_object* v_i_172_; lean_object* v_s_173_; lean_object* v_i_174_; uint8_t v___x_175_; 
v_s_171_ = lean_ctor_get(v_x_169_, 0);
v_i_172_ = lean_ctor_get(v_x_169_, 1);
v_s_173_ = lean_ctor_get(v_x_170_, 0);
v_i_174_ = lean_ctor_get(v_x_170_, 1);
v___x_175_ = lean_string_dec_eq(v_s_171_, v_s_173_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_i_174_, v___x_177_);
v___x_179_ = lean_nat_dec_le(v___x_178_, v_i_172_);
lean_dec(v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_string_utf8_extract(v_s_171_, v_i_172_, v_i_174_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_String_Legacy_Iterator_extract(v_x_182_, v_x_183_);
lean_dec_ref(v_x_183_);
lean_dec_ref(v_x_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_zero_187_; uint8_t v_isZero_188_; 
v_zero_187_ = lean_unsigned_to_nat(0u);
v_isZero_188_ = lean_nat_dec_eq(v_x_186_, v_zero_187_);
if (v_isZero_188_ == 1)
{
lean_dec(v_x_186_);
return v_x_185_;
}
else
{
lean_object* v_s_189_; lean_object* v_i_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_201_; 
v_s_189_ = lean_ctor_get(v_x_185_, 0);
v_i_190_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_201_ == 0)
{
v___x_192_ = v_x_185_;
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_i_190_);
lean_inc(v_s_189_);
lean_dec(v_x_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_one_194_; lean_object* v_n_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v_one_194_ = lean_unsigned_to_nat(1u);
v_n_195_ = lean_nat_sub(v_x_186_, v_one_194_);
lean_dec(v_x_186_);
v___x_196_ = lean_string_utf8_next(v_s_189_, v_i_190_);
lean_dec(v_i_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_196_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_s_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_x_185_ = v___x_198_;
v_x_186_ = v_n_195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object* v_x_202_){
_start:
{
lean_object* v_s_203_; lean_object* v_i_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_s_203_ = lean_ctor_get(v_x_202_, 0);
v_i_204_ = lean_ctor_get(v_x_202_, 1);
v___x_205_ = lean_string_utf8_byte_size(v_s_203_);
v___x_206_ = lean_string_utf8_extract(v_s_203_, v_i_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_Legacy_Iterator_remainingToString(v_x_207_);
lean_dec_ref(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_zero_211_; uint8_t v_isZero_212_; 
v_zero_211_ = lean_unsigned_to_nat(0u);
v_isZero_212_ = lean_nat_dec_eq(v_x_210_, v_zero_211_);
if (v_isZero_212_ == 1)
{
lean_dec(v_x_210_);
return v_x_209_;
}
else
{
lean_object* v_s_213_; lean_object* v_i_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_225_; 
v_s_213_ = lean_ctor_get(v_x_209_, 0);
v_i_214_ = lean_ctor_get(v_x_209_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_225_ == 0)
{
v___x_216_ = v_x_209_;
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_i_214_);
lean_inc(v_s_213_);
lean_dec(v_x_209_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_one_218_; lean_object* v_n_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_one_218_ = lean_unsigned_to_nat(1u);
v_n_219_ = lean_nat_sub(v_x_210_, v_one_218_);
lean_dec(v_x_210_);
v___x_220_ = lean_string_utf8_next(v_s_213_, v_i_214_);
lean_dec(v_i_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_220_);
v___x_222_ = v___x_216_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_s_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v_x_209_ = v___x_222_;
v_x_210_ = v_n_219_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_zero_228_; uint8_t v_isZero_229_; 
v_zero_228_ = lean_unsigned_to_nat(0u);
v_isZero_229_ = lean_nat_dec_eq(v_x_227_, v_zero_228_);
if (v_isZero_229_ == 1)
{
lean_dec(v_x_227_);
return v_x_226_;
}
else
{
lean_object* v_s_230_; lean_object* v_i_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_242_; 
v_s_230_ = lean_ctor_get(v_x_226_, 0);
v_i_231_ = lean_ctor_get(v_x_226_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_242_ == 0)
{
v___x_233_ = v_x_226_;
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_i_231_);
lean_inc(v_s_230_);
lean_dec(v_x_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_one_235_; lean_object* v_n_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_one_235_ = lean_unsigned_to_nat(1u);
v_n_236_ = lean_nat_sub(v_x_227_, v_one_235_);
lean_dec(v_x_227_);
v___x_237_ = lean_string_utf8_prev(v_s_230_, v_i_231_);
lean_dec(v_i_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_s_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
v_x_226_ = v___x_239_;
v_x_227_ = v_n_236_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_279_ = l_String_toRawSubstring_x27(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_306_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(1);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_304_);
return v___x_308_;
}
else
{
lean_object* v_quotContext_309_; lean_object* v_currMacroScope_310_; lean_object* v_ref_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_quotContext_309_ = lean_ctor_get(v_a_303_, 1);
v_currMacroScope_310_ = lean_ctor_get(v_a_303_, 2);
v_ref_311_ = lean_ctor_get(v_a_303_, 5);
v___x_312_ = 0;
v___x_313_ = l_Lean_SourceInfo_fromRef(v_ref_311_, v___x_312_);
v___x_314_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_315_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_313_, 10);
v___x_316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_318_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_319_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_320_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_321_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_313_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
v___x_323_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
v___x_324_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22));
lean_inc(v_currMacroScope_310_);
lean_inc(v_quotContext_309_);
v___x_325_ = l_Lean_addMacroScope(v_quotContext_309_, v___x_324_, v_currMacroScope_310_);
v___x_326_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24));
v___x_327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_313_);
lean_ctor_set(v___x_327_, 1, v___x_323_);
lean_ctor_set(v___x_327_, 2, v___x_325_);
lean_ctor_set(v___x_327_, 3, v___x_326_);
v___x_328_ = l_Lean_Syntax_node2(v___x_313_, v___x_321_, v___x_322_, v___x_327_);
v___x_329_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_313_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_332_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_313_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
v___x_334_ = l_Lean_Syntax_node1(v___x_313_, v___x_332_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node3(v___x_313_, v___x_319_, v___x_328_, v___x_330_, v___x_334_);
v___x_336_ = l_Lean_Syntax_node1(v___x_313_, v___x_318_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node1(v___x_313_, v___x_317_, v___x_336_);
v___x_338_ = l_Lean_Syntax_node2(v___x_313_, v___x_314_, v___x_316_, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_304_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_340_, v_a_341_, v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_346_ = l_String_toRawSubstring_x27(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_363_ = l_Lean_Syntax_isOfKind(v_x_359_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_box(1);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_361_);
return v___x_365_;
}
else
{
lean_object* v_quotContext_366_; lean_object* v_currMacroScope_367_; lean_object* v_ref_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_quotContext_366_ = lean_ctor_get(v_a_360_, 1);
v_currMacroScope_367_ = lean_ctor_get(v_a_360_, 2);
v_ref_368_ = lean_ctor_get(v_a_360_, 5);
v___x_369_ = 0;
v___x_370_ = l_Lean_SourceInfo_fromRef(v_ref_368_, v___x_369_);
v___x_371_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_372_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_370_, 10);
v___x_373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_375_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_376_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_377_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_378_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_370_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
v___x_380_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_381_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc(v_currMacroScope_367_);
lean_inc(v_quotContext_366_);
v___x_382_ = l_Lean_addMacroScope(v_quotContext_366_, v___x_381_, v_currMacroScope_367_);
v___x_383_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5));
v___x_384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_384_, 0, v___x_370_);
lean_ctor_set(v___x_384_, 1, v___x_380_);
lean_ctor_set(v___x_384_, 2, v___x_382_);
lean_ctor_set(v___x_384_, 3, v___x_383_);
v___x_385_ = l_Lean_Syntax_node2(v___x_370_, v___x_378_, v___x_379_, v___x_384_);
v___x_386_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_370_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_389_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_370_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
v___x_391_ = l_Lean_Syntax_node1(v___x_370_, v___x_389_, v___x_390_);
v___x_392_ = l_Lean_Syntax_node3(v___x_370_, v___x_376_, v___x_385_, v___x_387_, v___x_391_);
v___x_393_ = l_Lean_Syntax_node1(v___x_370_, v___x_375_, v___x_392_);
v___x_394_ = l_Lean_Syntax_node1(v___x_370_, v___x_374_, v___x_393_);
v___x_395_ = l_Lean_Syntax_node2(v___x_370_, v___x_371_, v___x_373_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_361_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_397_, v_a_398_, v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr(lean_object* v_x_401_, uint32_t v_x_402_){
_start:
{
lean_object* v_s_403_; lean_object* v_i_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_s_403_ = lean_ctor_get(v_x_401_, 0);
v_i_404_ = lean_ctor_get(v_x_401_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_401_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v_x_401_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_i_404_);
lean_inc(v_s_403_);
lean_dec(v_x_401_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_string_utf8_set(v_s_403_, v_i_404_, v_x_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_i_404_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
uint32_t v_x_15__boxed_415_; lean_object* v_res_416_; 
v_x_15__boxed_415_ = lean_unbox_uint32(v_x_414_);
lean_dec(v_x_414_);
v_res_416_ = l_String_Legacy_Iterator_setCurr(v_x_413_, v_x_15__boxed_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object* v_it_417_, lean_object* v_p_418_){
_start:
{
lean_object* v_s_419_; lean_object* v_i_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_s_419_ = lean_ctor_get(v_it_417_, 0);
v_i_420_ = lean_ctor_get(v_it_417_, 1);
v___x_421_ = lean_string_utf8_byte_size(v_s_419_);
v___x_422_ = lean_nat_dec_le(v___x_421_, v_i_420_);
if (v___x_422_ == 0)
{
uint32_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_423_ = lean_string_utf8_get(v_s_419_, v_i_420_);
v___x_424_ = lean_box_uint32(v___x_423_);
lean_inc_ref(v_p_418_);
v___x_425_ = lean_apply_1(v_p_418_, v___x_424_);
v___x_426_ = lean_unbox(v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_435_; 
lean_inc(v_i_420_);
lean_inc_ref(v_s_419_);
v_isSharedCheck_435_ = !lean_is_exclusive(v_it_417_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; lean_object* v_unused_437_; 
v_unused_436_ = lean_ctor_get(v_it_417_, 1);
lean_dec(v_unused_436_);
v_unused_437_ = lean_ctor_get(v_it_417_, 0);
lean_dec(v_unused_437_);
v___x_428_ = v_it_417_;
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_it_417_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_string_utf8_next(v_s_419_, v_i_420_);
lean_dec(v_i_420_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_s_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_430_);
v___x_432_ = v_reuseFailAlloc_434_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v_it_417_ = v___x_432_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_418_);
return v_it_417_;
}
}
else
{
lean_dec_ref(v_p_418_);
return v_it_417_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object* v_it_438_, lean_object* v_init_439_, lean_object* v_f_440_){
_start:
{
lean_object* v_s_441_; lean_object* v_i_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_s_441_ = lean_ctor_get(v_it_438_, 0);
v_i_442_ = lean_ctor_get(v_it_438_, 1);
v___x_443_ = lean_string_utf8_byte_size(v_s_441_);
v___x_444_ = lean_nat_dec_le(v___x_443_, v_i_442_);
if (v___x_444_ == 0)
{
uint32_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_string_utf8_get(v_s_441_, v_i_442_);
v___x_446_ = lean_box_uint32(v___x_445_);
lean_inc_ref(v_f_440_);
lean_inc(v_init_439_);
v___x_447_ = lean_apply_2(v_f_440_, v_init_439_, v___x_446_);
if (lean_obj_tag(v___x_447_) == 1)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
lean_inc(v_i_442_);
lean_inc_ref(v_s_441_);
lean_dec(v_init_439_);
v_isSharedCheck_457_ = !lean_is_exclusive(v_it_438_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_458_ = lean_ctor_get(v_it_438_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_it_438_, 0);
lean_dec(v_unused_459_);
v___x_449_ = v_it_438_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_it_438_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_val_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v_val_451_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_447_, 1);
v___x_452_ = lean_string_utf8_next(v_s_441_, v_i_442_);
lean_dec(v_i_442_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_s_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
v_it_438_ = v___x_454_;
v_init_439_ = v_val_451_;
goto _start;
}
}
}
else
{
lean_object* v___x_460_; 
lean_dec(v___x_447_);
lean_dec_ref(v_f_440_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_init_439_);
lean_ctor_set(v___x_460_, 1, v_it_438_);
return v___x_460_;
}
}
else
{
lean_object* v___x_461_; 
lean_dec_ref(v_f_440_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_init_439_);
lean_ctor_set(v___x_461_, 1, v_it_438_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object* v_00_u03b1_462_, lean_object* v_it_463_, lean_object* v_init_464_, lean_object* v_f_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_463_, v_init_464_, v_f_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 1)
{
lean_object* v_val_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_469_);
v_val_470_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v_x_467_, 1);
v___x_471_ = lean_apply_1(v_h__1_468_, v_val_470_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_h__1_468_);
v___x_472_ = lean_apply_2(v_h__2_469_, v_x_467_, lean_box(0));
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object* v_00_u03b1_473_, lean_object* v_motive_474_, lean_object* v_x_475_, lean_object* v_h__1_476_, lean_object* v_h__2_477_){
_start:
{
if (lean_obj_tag(v_x_475_) == 1)
{
lean_object* v_val_478_; lean_object* v___x_479_; 
lean_dec(v_h__2_477_);
v_val_478_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v_x_475_, 1);
v___x_479_ = lean_apply_1(v_h__1_476_, v_val_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_h__1_476_);
v___x_480_ = lean_apply_2(v_h__2_477_, v_x_475_, lean_box(0));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object* v_x_481_){
_start:
{
lean_object* v_str_482_; lean_object* v_startPos_483_; lean_object* v___x_484_; 
v_str_482_ = lean_ctor_get(v_x_481_, 0);
v_startPos_483_ = lean_ctor_get(v_x_481_, 1);
lean_inc(v_startPos_483_);
lean_inc_ref(v_str_482_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_str_482_);
lean_ctor_set(v___x_484_, 1, v_startPos_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Substring_Raw_toLegacyIterator(v_x_485_);
lean_dec_ref(v_x_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_s_501_; lean_object* v_i_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_522_; 
v_s_501_ = lean_ctor_get(v_x_499_, 0);
v_i_502_ = lean_ctor_get(v_x_499_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_522_ == 0)
{
v___x_504_ = v_x_499_;
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_i_502_);
lean_inc(v_s_501_);
lean_dec(v_x_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_506_ = ((lean_object*)(l_instReprIterator___lam__0___closed__1));
v___x_507_ = l_String_quote(v_s_501_);
v___x_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 5);
lean_ctor_set(v___x_504_, 1, v___x_508_);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_510_ = v___x_504_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_521_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_511_ = ((lean_object*)(l_instReprIterator___lam__0___closed__3));
v___x_512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = ((lean_object*)(l_instReprIterator___lam__0___closed__5));
v___x_514_ = l_Nat_reprFast(v_i_502_);
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = ((lean_object*)(l_instReprIterator___lam__0___closed__7));
v___x_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_512_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Repr_addAppParen(v___x_519_, v_x_500_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_instReprIterator___lam__0(v_x_523_, v_x_524_);
lean_dec(v_x_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* v_it_528_){
_start:
{
lean_object* v_s_529_; lean_object* v_i_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_s_529_ = lean_ctor_get(v_it_528_, 0);
v_i_530_ = lean_ctor_get(v_it_528_, 1);
v___x_531_ = lean_string_utf8_byte_size(v_s_529_);
v___x_532_ = lean_string_utf8_extract(v_s_529_, v_i_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* v_it_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_instToStringIterator___lam__0(v_it_533_);
lean_dec_ref(v_it_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* v_s_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_s_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* v_s_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_s_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object* v_a_543_){
_start:
{
lean_object* v_s_544_; lean_object* v_i_545_; uint32_t v___x_546_; 
v_s_544_ = lean_ctor_get(v_a_543_, 0);
v_i_545_ = lean_ctor_get(v_a_543_, 1);
v___x_546_ = lean_string_utf8_get(v_s_544_, v_i_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* v_a_547_){
_start:
{
uint32_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_String_Iterator_curr(v_a_547_);
lean_dec_ref(v_a_547_);
v_r_549_ = lean_box_uint32(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* v_a_550_){
_start:
{
lean_object* v_s_551_; lean_object* v_i_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_s_551_ = lean_ctor_get(v_a_550_, 0);
v_i_552_ = lean_ctor_get(v_a_550_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_a_550_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v_a_550_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_i_552_);
lean_inc(v_s_551_);
lean_dec(v_a_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_string_utf8_next(v_s_551_, v_i_552_);
lean_dec(v_i_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_s_551_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object* v_a_561_){
_start:
{
lean_object* v_s_562_; lean_object* v_i_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_s_562_ = lean_ctor_get(v_a_561_, 0);
v_i_563_ = lean_ctor_get(v_a_561_, 1);
v___x_564_ = lean_string_utf8_byte_size(v_s_562_);
v___x_565_ = lean_nat_dec_lt(v_i_563_, v___x_564_);
return v___x_565_;
}
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
