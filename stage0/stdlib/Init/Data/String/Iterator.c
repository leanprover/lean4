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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_i_4_, v_i_6_);
return v___x_8_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_apply_2(v_h__1_121_, v_x_119_, v_x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_h__1_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_apply_2(v_h__1_126_, v_x_124_, v_x_125_);
return v___x_127_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object* v_it_128_){
_start:
{
lean_object* v_s_129_; lean_object* v_i_130_; uint32_t v___x_131_; 
v_s_129_ = lean_ctor_get(v_it_128_, 0);
v_i_130_ = lean_ctor_get(v_it_128_, 1);
v___x_131_ = lean_string_utf8_get_fast(v_s_129_, v_i_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object* v_it_132_){
_start:
{
uint32_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_132_);
lean_dec_ref(v_it_132_);
v_r_134_ = lean_box_uint32(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27(lean_object* v_it_135_, lean_object* v_h_136_){
_start:
{
lean_object* v_s_137_; lean_object* v_i_138_; uint32_t v___x_139_; 
v_s_137_ = lean_ctor_get(v_it_135_, 0);
v_i_138_ = lean_ctor_get(v_it_135_, 1);
v___x_139_ = lean_string_utf8_get_fast(v_s_137_, v_i_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object* v_it_140_, lean_object* v_h_141_){
_start:
{
uint32_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_String_Legacy_Iterator_curr_x27(v_it_140_, v_h_141_);
lean_dec_ref(v_it_140_);
v_r_143_ = lean_box_uint32(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object* v_it_144_){
_start:
{
lean_object* v_s_145_; lean_object* v_i_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_s_145_ = lean_ctor_get(v_it_144_, 0);
v_i_146_ = lean_ctor_get(v_it_144_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_it_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v_it_144_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_i_146_);
lean_inc(v_s_145_);
lean_dec(v_it_144_);
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
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object* v_it_155_, lean_object* v_h_156_){
_start:
{
lean_object* v_s_157_; lean_object* v_i_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_s_157_ = lean_ctor_get(v_it_155_, 0);
v_i_158_ = lean_ctor_get(v_it_155_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_it_155_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v_it_155_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_i_158_);
lean_inc(v_s_157_);
lean_dec(v_it_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_string_utf8_next_fast(v_s_157_, v_i_158_);
lean_dec(v_i_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_s_157_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object* v_x_167_){
_start:
{
lean_object* v_s_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_s_168_ = lean_ctor_get(v_x_167_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_x_167_, 1);
lean_dec(v_unused_177_);
v___x_170_ = v_x_167_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_s_168_);
lean_dec(v_x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_string_utf8_byte_size(v_s_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_s_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_s_180_; lean_object* v_i_181_; lean_object* v_s_182_; lean_object* v_i_183_; uint8_t v___x_184_; 
v_s_180_ = lean_ctor_get(v_x_178_, 0);
v_i_181_ = lean_ctor_get(v_x_178_, 1);
v_s_182_ = lean_ctor_get(v_x_179_, 0);
v_i_183_ = lean_ctor_get(v_x_179_, 1);
v___x_184_ = lean_string_dec_eq(v_s_180_, v_s_182_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = lean_nat_dec_lt(v_i_183_, v_i_181_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_string_utf8_extract(v_s_180_, v_i_181_, v_i_183_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_String_Legacy_Iterator_extract(v_x_189_, v_x_190_);
lean_dec_ref(v_x_190_);
lean_dec_ref(v_x_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v_zero_194_; uint8_t v_isZero_195_; 
v_zero_194_ = lean_unsigned_to_nat(0u);
v_isZero_195_ = lean_nat_dec_eq(v_x_193_, v_zero_194_);
if (v_isZero_195_ == 1)
{
lean_dec(v_x_193_);
return v_x_192_;
}
else
{
lean_object* v_s_196_; lean_object* v_i_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_s_196_ = lean_ctor_get(v_x_192_, 0);
v_i_197_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v_x_192_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_i_197_);
lean_inc(v_s_196_);
lean_dec(v_x_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_one_201_; lean_object* v_n_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v_one_201_ = lean_unsigned_to_nat(1u);
v_n_202_ = lean_nat_sub(v_x_193_, v_one_201_);
lean_dec(v_x_193_);
v___x_203_ = lean_string_utf8_next(v_s_196_, v_i_197_);
lean_dec(v_i_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_203_);
v___x_205_ = v___x_199_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_s_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v_x_192_ = v___x_205_;
v_x_193_ = v_n_202_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object* v_x_209_){
_start:
{
lean_object* v_s_210_; lean_object* v_i_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_s_210_ = lean_ctor_get(v_x_209_, 0);
v_i_211_ = lean_ctor_get(v_x_209_, 1);
v___x_212_ = lean_string_utf8_byte_size(v_s_210_);
v___x_213_ = lean_string_utf8_extract(v_s_210_, v_i_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_String_Legacy_Iterator_remainingToString(v_x_214_);
lean_dec_ref(v_x_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_zero_218_; uint8_t v_isZero_219_; 
v_zero_218_ = lean_unsigned_to_nat(0u);
v_isZero_219_ = lean_nat_dec_eq(v_x_217_, v_zero_218_);
if (v_isZero_219_ == 1)
{
lean_dec(v_x_217_);
return v_x_216_;
}
else
{
lean_object* v_s_220_; lean_object* v_i_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_232_; 
v_s_220_ = lean_ctor_get(v_x_216_, 0);
v_i_221_ = lean_ctor_get(v_x_216_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_232_ == 0)
{
v___x_223_ = v_x_216_;
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_i_221_);
lean_inc(v_s_220_);
lean_dec(v_x_216_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_one_225_; lean_object* v_n_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v_one_225_ = lean_unsigned_to_nat(1u);
v_n_226_ = lean_nat_sub(v_x_217_, v_one_225_);
lean_dec(v_x_217_);
v___x_227_ = lean_string_utf8_next(v_s_220_, v_i_221_);
lean_dec(v_i_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_227_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_s_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v_x_216_ = v___x_229_;
v_x_217_ = v_n_226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_zero_235_; uint8_t v_isZero_236_; 
v_zero_235_ = lean_unsigned_to_nat(0u);
v_isZero_236_ = lean_nat_dec_eq(v_x_234_, v_zero_235_);
if (v_isZero_236_ == 1)
{
lean_dec(v_x_234_);
return v_x_233_;
}
else
{
lean_object* v_s_237_; lean_object* v_i_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
v_s_237_ = lean_ctor_get(v_x_233_, 0);
v_i_238_ = lean_ctor_get(v_x_233_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_249_ == 0)
{
v___x_240_ = v_x_233_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_i_238_);
lean_inc(v_s_237_);
lean_dec(v_x_233_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_one_242_; lean_object* v_n_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v_one_242_ = lean_unsigned_to_nat(1u);
v_n_243_ = lean_nat_sub(v_x_234_, v_one_242_);
lean_dec(v_x_234_);
v___x_244_ = lean_string_utf8_prev(v_s_237_, v_i_238_);
lean_dec(v_i_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_244_);
v___x_246_ = v___x_240_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_s_237_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_x_233_ = v___x_246_;
v_x_234_ = v_n_243_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_286_ = l_String_toRawSubstring_x27(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_313_ = l_Lean_Syntax_isOfKind(v_x_309_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(1);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
return v___x_315_;
}
else
{
lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v_ref_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_quotContext_316_ = lean_ctor_get(v_a_310_, 1);
v_currMacroScope_317_ = lean_ctor_get(v_a_310_, 2);
v_ref_318_ = lean_ctor_get(v_a_310_, 5);
v___x_319_ = 0;
v___x_320_ = l_Lean_SourceInfo_fromRef(v_ref_318_, v___x_319_);
v___x_321_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_322_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_320_, 10);
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_325_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_326_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_327_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_328_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_320_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
v___x_330_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
v___x_331_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_332_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_331_, v_currMacroScope_317_);
v___x_333_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24));
v___x_334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_334_, 0, v___x_320_);
lean_ctor_set(v___x_334_, 1, v___x_330_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
v___x_335_ = l_Lean_Syntax_node2(v___x_320_, v___x_328_, v___x_329_, v___x_334_);
v___x_336_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_320_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_339_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_320_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
v___x_341_ = l_Lean_Syntax_node1(v___x_320_, v___x_339_, v___x_340_);
v___x_342_ = l_Lean_Syntax_node3(v___x_320_, v___x_326_, v___x_335_, v___x_337_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node1(v___x_320_, v___x_325_, v___x_342_);
v___x_344_ = l_Lean_Syntax_node1(v___x_320_, v___x_324_, v___x_343_);
v___x_345_ = l_Lean_Syntax_node2(v___x_320_, v___x_321_, v___x_323_, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_a_311_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_347_, v_a_348_, v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_350_;
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_353_ = l_String_toRawSubstring_x27(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_370_ = l_Lean_Syntax_isOfKind(v_x_366_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(1);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_368_);
return v___x_372_;
}
else
{
lean_object* v_quotContext_373_; lean_object* v_currMacroScope_374_; lean_object* v_ref_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_quotContext_373_ = lean_ctor_get(v_a_367_, 1);
v_currMacroScope_374_ = lean_ctor_get(v_a_367_, 2);
v_ref_375_ = lean_ctor_get(v_a_367_, 5);
v___x_376_ = 0;
v___x_377_ = l_Lean_SourceInfo_fromRef(v_ref_375_, v___x_376_);
v___x_378_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_379_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc_n(v___x_377_, 10);
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_377_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_382_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_383_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_384_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_385_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_377_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
v___x_387_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_388_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc(v_currMacroScope_374_);
lean_inc(v_quotContext_373_);
v___x_389_ = l_Lean_addMacroScope(v_quotContext_373_, v___x_388_, v_currMacroScope_374_);
v___x_390_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5));
v___x_391_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_391_, 0, v___x_377_);
lean_ctor_set(v___x_391_, 1, v___x_387_);
lean_ctor_set(v___x_391_, 2, v___x_389_);
lean_ctor_set(v___x_391_, 3, v___x_390_);
v___x_392_ = l_Lean_Syntax_node2(v___x_377_, v___x_385_, v___x_386_, v___x_391_);
v___x_393_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_377_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_396_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
v___x_397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_377_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
v___x_398_ = l_Lean_Syntax_node1(v___x_377_, v___x_396_, v___x_397_);
v___x_399_ = l_Lean_Syntax_node3(v___x_377_, v___x_383_, v___x_392_, v___x_394_, v___x_398_);
v___x_400_ = l_Lean_Syntax_node1(v___x_377_, v___x_382_, v___x_399_);
v___x_401_ = l_Lean_Syntax_node1(v___x_377_, v___x_381_, v___x_400_);
v___x_402_ = l_Lean_Syntax_node2(v___x_377_, v___x_378_, v___x_380_, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_368_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_404_, v_a_405_, v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr(lean_object* v_x_408_, uint32_t v_x_409_){
_start:
{
lean_object* v_s_410_; lean_object* v_i_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_s_410_ = lean_ctor_get(v_x_408_, 0);
v_i_411_ = lean_ctor_get(v_x_408_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v_x_408_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_i_411_);
lean_inc(v_s_410_);
lean_dec(v_x_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_string_utf8_set(v_s_410_, v_i_411_, v_x_409_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_i_411_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint32_t v_x_15__boxed_422_; lean_object* v_res_423_; 
v_x_15__boxed_422_ = lean_unbox_uint32(v_x_421_);
lean_dec(v_x_421_);
v_res_423_ = l_String_Legacy_Iterator_setCurr(v_x_420_, v_x_15__boxed_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object* v_it_424_, lean_object* v_p_425_){
_start:
{
lean_object* v_s_426_; lean_object* v_i_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_s_426_ = lean_ctor_get(v_it_424_, 0);
v_i_427_ = lean_ctor_get(v_it_424_, 1);
v___x_428_ = lean_string_utf8_byte_size(v_s_426_);
v___x_429_ = lean_nat_dec_le(v___x_428_, v_i_427_);
if (v___x_429_ == 0)
{
uint32_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_430_ = lean_string_utf8_get(v_s_426_, v_i_427_);
v___x_431_ = lean_box_uint32(v___x_430_);
lean_inc_ref(v_p_425_);
v___x_432_ = lean_apply_1(v_p_425_, v___x_431_);
v___x_433_ = lean_unbox(v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_i_427_);
lean_inc_ref(v_s_426_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_it_424_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_it_424_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_it_424_, 0);
lean_dec(v_unused_444_);
v___x_435_ = v_it_424_;
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_it_424_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_string_utf8_next(v_s_426_, v_i_427_);
lean_dec(v_i_427_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_s_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_441_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v_it_424_ = v___x_439_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_425_);
return v_it_424_;
}
}
else
{
lean_dec_ref(v_p_425_);
return v_it_424_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object* v_it_445_, lean_object* v_init_446_, lean_object* v_f_447_){
_start:
{
lean_object* v_s_448_; lean_object* v_i_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_s_448_ = lean_ctor_get(v_it_445_, 0);
v_i_449_ = lean_ctor_get(v_it_445_, 1);
v___x_450_ = lean_string_utf8_byte_size(v_s_448_);
v___x_451_ = lean_nat_dec_le(v___x_450_, v_i_449_);
if (v___x_451_ == 0)
{
uint32_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_string_utf8_get(v_s_448_, v_i_449_);
v___x_453_ = lean_box_uint32(v___x_452_);
lean_inc_ref(v_f_447_);
lean_inc(v_init_446_);
v___x_454_ = lean_apply_2(v_f_447_, v_init_446_, v___x_453_);
if (lean_obj_tag(v___x_454_) == 1)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_i_449_);
lean_inc_ref(v_s_448_);
lean_dec(v_init_446_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_it_445_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_465_ = lean_ctor_get(v_it_445_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_it_445_, 0);
lean_dec(v_unused_466_);
v___x_456_ = v_it_445_;
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_it_445_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_val_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v_val_458_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_val_458_);
lean_dec_ref(v___x_454_);
v___x_459_ = lean_string_utf8_next(v_s_448_, v_i_449_);
lean_dec(v_i_449_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_s_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v_it_445_ = v___x_461_;
v_init_446_ = v_val_458_;
goto _start;
}
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v___x_454_);
lean_dec_ref(v_f_447_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_init_446_);
lean_ctor_set(v___x_467_, 1, v_it_445_);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v_f_447_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_init_446_);
lean_ctor_set(v___x_468_, 1, v_it_445_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object* v_00_u03b1_469_, lean_object* v_it_470_, lean_object* v_init_471_, lean_object* v_f_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_470_, v_init_471_, v_f_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_){
_start:
{
if (lean_obj_tag(v_x_474_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; 
lean_dec(v_h__2_476_);
v_val_477_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v_x_474_);
v___x_478_ = lean_apply_1(v_h__1_475_, v_val_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_h__1_475_);
v___x_479_ = lean_apply_2(v_h__2_476_, v_x_474_, lean_box(0));
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object* v_00_u03b1_480_, lean_object* v_motive_481_, lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_){
_start:
{
if (lean_obj_tag(v_x_482_) == 1)
{
lean_object* v_val_485_; lean_object* v___x_486_; 
lean_dec(v_h__2_484_);
v_val_485_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_val_485_);
lean_dec_ref(v_x_482_);
v___x_486_ = lean_apply_1(v_h__1_483_, v_val_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; 
lean_dec(v_h__1_483_);
v___x_487_ = lean_apply_2(v_h__2_484_, v_x_482_, lean_box(0));
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object* v_x_488_){
_start:
{
lean_object* v_str_489_; lean_object* v_startPos_490_; lean_object* v___x_491_; 
v_str_489_ = lean_ctor_get(v_x_488_, 0);
v_startPos_490_ = lean_ctor_get(v_x_488_, 1);
lean_inc(v_startPos_490_);
lean_inc_ref(v_str_489_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_str_489_);
lean_ctor_set(v___x_491_, 1, v_startPos_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Substring_Raw_toLegacyIterator(v_x_492_);
lean_dec_ref(v_x_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_s_508_; lean_object* v_i_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_529_; 
v_s_508_ = lean_ctor_get(v_x_506_, 0);
v_i_509_ = lean_ctor_get(v_x_506_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_529_ == 0)
{
v___x_511_ = v_x_506_;
v_isShared_512_ = v_isSharedCheck_529_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_i_509_);
lean_inc(v_s_508_);
lean_dec(v_x_506_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_529_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_513_ = ((lean_object*)(l_instReprIterator___lam__0___closed__1));
v___x_514_ = l_String_quote(v_s_508_);
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 5);
lean_ctor_set(v___x_511_, 1, v___x_515_);
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_528_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_518_ = ((lean_object*)(l_instReprIterator___lam__0___closed__3));
v___x_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = ((lean_object*)(l_instReprIterator___lam__0___closed__5));
v___x_521_ = l_Nat_reprFast(v_i_509_);
v___x_522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = ((lean_object*)(l_instReprIterator___lam__0___closed__7));
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_519_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Repr_addAppParen(v___x_526_, v_x_507_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_instReprIterator___lam__0(v_x_530_, v_x_531_);
lean_dec(v_x_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* v_it_535_){
_start:
{
lean_object* v_s_536_; lean_object* v_i_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_s_536_ = lean_ctor_get(v_it_535_, 0);
v_i_537_ = lean_ctor_get(v_it_535_, 1);
v___x_538_ = lean_string_utf8_byte_size(v_s_536_);
v___x_539_ = lean_string_utf8_extract(v_s_536_, v_i_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* v_it_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_instToStringIterator___lam__0(v_it_540_);
lean_dec_ref(v_it_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* v_s_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_s_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* v_s_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_s_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object* v_a_550_){
_start:
{
lean_object* v_s_551_; lean_object* v_i_552_; uint32_t v___x_553_; 
v_s_551_ = lean_ctor_get(v_a_550_, 0);
v_i_552_ = lean_ctor_get(v_a_550_, 1);
v___x_553_ = lean_string_utf8_get(v_s_551_, v_i_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* v_a_554_){
_start:
{
uint32_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_String_Iterator_curr(v_a_554_);
lean_dec_ref(v_a_554_);
v_r_556_ = lean_box_uint32(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* v_a_557_){
_start:
{
lean_object* v_s_558_; lean_object* v_i_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_s_558_ = lean_ctor_get(v_a_557_, 0);
v_i_559_ = lean_ctor_get(v_a_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_a_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_i_559_);
lean_inc(v_s_558_);
lean_dec(v_a_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_string_utf8_next(v_s_558_, v_i_559_);
lean_dec(v_i_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_s_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object* v_a_568_){
_start:
{
lean_object* v_s_569_; lean_object* v_i_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_s_569_ = lean_ctor_get(v_a_568_, 0);
v_i_570_ = lean_ctor_get(v_a_568_, 1);
v___x_571_ = lean_string_utf8_byte_size(v_s_569_);
v___x_572_ = lean_nat_dec_lt(v_i_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object* v_a_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_String_Iterator_hasNext(v_a_573_);
lean_dec_ref(v_a_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object* v_a_576_){
_start:
{
lean_object* v_str_577_; lean_object* v_startPos_578_; lean_object* v___x_579_; 
v_str_577_ = lean_ctor_get(v_a_576_, 0);
v_startPos_578_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_startPos_578_);
lean_inc_ref(v_str_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_str_577_);
lean_ctor_set(v___x_579_, 1, v_startPos_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Substring_toIterator(v_a_580_);
lean_dec_ref(v_a_580_);
return v_res_581_;
}
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
