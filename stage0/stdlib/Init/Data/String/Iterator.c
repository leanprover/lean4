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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_116_; 
v___x_116_ = l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(v_x_114_, v_h__1_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_h__1_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_apply_2(v_h__1_119_, v_x_117_, v_x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_h__1_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_apply_2(v_h__1_124_, v_x_122_, v_x_123_);
return v___x_125_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27___redArg(lean_object* v_it_126_){
_start:
{
lean_object* v_s_127_; lean_object* v_i_128_; uint32_t v___x_129_; 
v_s_127_ = lean_ctor_get(v_it_126_, 0);
v_i_128_ = lean_ctor_get(v_it_126_, 1);
v___x_129_ = lean_string_utf8_get_fast(v_s_127_, v_i_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___redArg___boxed(lean_object* v_it_130_){
_start:
{
uint32_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_130_);
lean_dec_ref(v_it_130_);
v_r_132_ = lean_box_uint32(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint32_t l_String_Legacy_Iterator_curr_x27(lean_object* v_it_133_, lean_object* v_h_134_){
_start:
{
lean_object* v_s_135_; lean_object* v_i_136_; uint32_t v___x_137_; 
v_s_135_ = lean_ctor_get(v_it_133_, 0);
v_i_136_ = lean_ctor_get(v_it_133_, 1);
v___x_137_ = lean_string_utf8_get_fast(v_s_135_, v_i_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_curr_x27___boxed(lean_object* v_it_138_, lean_object* v_h_139_){
_start:
{
uint32_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_String_Legacy_Iterator_curr_x27(v_it_138_, v_h_139_);
lean_dec_ref(v_it_138_);
v_r_141_ = lean_box_uint32(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27___redArg(lean_object* v_it_142_){
_start:
{
lean_object* v_s_143_; lean_object* v_i_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_152_; 
v_s_143_ = lean_ctor_get(v_it_142_, 0);
v_i_144_ = lean_ctor_get(v_it_142_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_it_142_);
if (v_isSharedCheck_152_ == 0)
{
v___x_146_ = v_it_142_;
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_i_144_);
lean_inc(v_s_143_);
lean_dec(v_it_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_string_utf8_next_fast(v_s_143_, v_i_144_);
lean_dec(v_i_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_s_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_next_x27(lean_object* v_it_153_, lean_object* v_h_154_){
_start:
{
lean_object* v_s_155_; lean_object* v_i_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_s_155_ = lean_ctor_get(v_it_153_, 0);
v_i_156_ = lean_ctor_get(v_it_153_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_it_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v_it_153_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_i_156_);
lean_inc(v_s_155_);
lean_dec(v_it_153_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_string_utf8_next_fast(v_s_155_, v_i_156_);
lean_dec(v_i_156_);
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
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_s_155_);
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
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_toEnd(lean_object* v_x_165_){
_start:
{
lean_object* v_s_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_s_166_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_x_165_, 1);
lean_dec(v_unused_175_);
v___x_168_ = v_x_165_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_s_166_);
lean_dec(v_x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_string_utf8_byte_size(v_s_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_s_166_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_s_178_; lean_object* v_i_179_; lean_object* v_s_180_; lean_object* v_i_181_; uint8_t v___x_182_; 
v_s_178_ = lean_ctor_get(v_x_176_, 0);
v_i_179_ = lean_ctor_get(v_x_176_, 1);
v_s_180_ = lean_ctor_get(v_x_177_, 0);
v_i_181_ = lean_ctor_get(v_x_177_, 1);
v___x_182_ = lean_string_dec_eq(v_s_178_, v_s_180_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_lt(v_i_181_, v_i_179_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_string_utf8_extract(v_s_178_, v_i_179_, v_i_181_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l_String_Legacy_instInhabitedIterator_default___closed__0));
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_extract___boxed(lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_Legacy_Iterator_extract(v_x_187_, v_x_188_);
lean_dec_ref(v_x_188_);
lean_dec_ref(v_x_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_forward(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_zero_192_; uint8_t v_isZero_193_; 
v_zero_192_ = lean_unsigned_to_nat(0u);
v_isZero_193_ = lean_nat_dec_eq(v_x_191_, v_zero_192_);
if (v_isZero_193_ == 1)
{
lean_dec(v_x_191_);
return v_x_190_;
}
else
{
lean_object* v_s_194_; lean_object* v_i_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_206_; 
v_s_194_ = lean_ctor_get(v_x_190_, 0);
v_i_195_ = lean_ctor_get(v_x_190_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_206_ == 0)
{
v___x_197_ = v_x_190_;
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_i_195_);
lean_inc(v_s_194_);
lean_dec(v_x_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_one_199_; lean_object* v_n_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v_one_199_ = lean_unsigned_to_nat(1u);
v_n_200_ = lean_nat_sub(v_x_191_, v_one_199_);
lean_dec(v_x_191_);
v___x_201_ = lean_string_utf8_next(v_s_194_, v_i_195_);
lean_dec(v_i_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_201_);
v___x_203_ = v___x_197_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_s_194_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_x_190_ = v___x_203_;
v_x_191_ = v_n_200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString(lean_object* v_x_207_){
_start:
{
lean_object* v_s_208_; lean_object* v_i_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_s_208_ = lean_ctor_get(v_x_207_, 0);
v_i_209_ = lean_ctor_get(v_x_207_, 1);
v___x_210_ = lean_string_utf8_byte_size(v_s_208_);
v___x_211_ = lean_string_utf8_extract(v_s_208_, v_i_209_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_remainingToString___boxed(lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_String_Legacy_Iterator_remainingToString(v_x_212_);
lean_dec_ref(v_x_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_nextn(lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_zero_216_; uint8_t v_isZero_217_; 
v_zero_216_ = lean_unsigned_to_nat(0u);
v_isZero_217_ = lean_nat_dec_eq(v_x_215_, v_zero_216_);
if (v_isZero_217_ == 1)
{
lean_dec(v_x_215_);
return v_x_214_;
}
else
{
lean_object* v_s_218_; lean_object* v_i_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_230_; 
v_s_218_ = lean_ctor_get(v_x_214_, 0);
v_i_219_ = lean_ctor_get(v_x_214_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_230_ == 0)
{
v___x_221_ = v_x_214_;
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_i_219_);
lean_inc(v_s_218_);
lean_dec(v_x_214_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_one_223_; lean_object* v_n_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_one_223_ = lean_unsigned_to_nat(1u);
v_n_224_ = lean_nat_sub(v_x_215_, v_one_223_);
lean_dec(v_x_215_);
v___x_225_ = lean_string_utf8_next(v_s_218_, v_i_219_);
lean_dec(v_i_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_225_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_s_218_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
v_x_214_ = v___x_227_;
v_x_215_ = v_n_224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_prevn(lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_zero_233_; uint8_t v_isZero_234_; 
v_zero_233_ = lean_unsigned_to_nat(0u);
v_isZero_234_ = lean_nat_dec_eq(v_x_232_, v_zero_233_);
if (v_isZero_234_ == 1)
{
lean_dec(v_x_232_);
return v_x_231_;
}
else
{
lean_object* v_s_235_; lean_object* v_i_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_247_; 
v_s_235_ = lean_ctor_get(v_x_231_, 0);
v_i_236_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_247_ == 0)
{
v___x_238_ = v_x_231_;
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_i_236_);
lean_inc(v_s_235_);
lean_dec(v_x_231_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_one_240_; lean_object* v_n_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v_one_240_ = lean_unsigned_to_nat(1u);
v_n_241_ = lean_nat_sub(v_x_232_, v_one_240_);
lean_dec(v_x_232_);
v___x_242_ = lean_string_utf8_prev(v_s_235_, v_i_236_);
lean_dec(v_i_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_242_);
v___x_244_ = v___x_238_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_s_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v_x_231_ = v___x_244_;
v_x_232_ = v_n_241_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_284_ = l_String_toRawSubstring_x27(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_311_ = l_Lean_Syntax_isOfKind(v_x_307_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_a_308_);
v___x_312_ = lean_box(1);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_a_309_);
return v___x_313_;
}
else
{
lean_object* v_quotContext_314_; lean_object* v_currMacroScope_315_; lean_object* v_ref_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_quotContext_314_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_quotContext_314_);
v_currMacroScope_315_ = lean_ctor_get(v_a_308_, 2);
lean_inc(v_currMacroScope_315_);
v_ref_316_ = lean_ctor_get(v_a_308_, 5);
lean_inc(v_ref_316_);
lean_dec_ref(v_a_308_);
v___x_317_ = 0;
v___x_318_ = l_Lean_SourceInfo_fromRef(v_ref_316_, v___x_317_);
lean_dec(v_ref_316_);
v___x_319_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_320_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc(v___x_318_);
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_318_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_323_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_324_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_325_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_326_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
lean_inc(v___x_318_);
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_318_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
v___x_328_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
v___x_329_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22));
v___x_330_ = l_Lean_addMacroScope(v_quotContext_314_, v___x_329_, v_currMacroScope_315_);
v___x_331_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24));
lean_inc(v___x_318_);
v___x_332_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_332_, 0, v___x_318_);
lean_ctor_set(v___x_332_, 1, v___x_328_);
lean_ctor_set(v___x_332_, 2, v___x_330_);
lean_ctor_set(v___x_332_, 3, v___x_331_);
lean_inc(v___x_318_);
v___x_333_ = l_Lean_Syntax_node2(v___x_318_, v___x_326_, v___x_327_, v___x_332_);
v___x_334_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
lean_inc(v___x_318_);
v___x_335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_318_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_337_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc(v___x_318_);
v___x_338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_318_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_inc(v___x_318_);
v___x_339_ = l_Lean_Syntax_node1(v___x_318_, v___x_337_, v___x_338_);
lean_inc(v___x_318_);
v___x_340_ = l_Lean_Syntax_node3(v___x_318_, v___x_324_, v___x_333_, v___x_335_, v___x_339_);
lean_inc(v___x_318_);
v___x_341_ = l_Lean_Syntax_node1(v___x_318_, v___x_323_, v___x_340_);
lean_inc(v___x_318_);
v___x_342_ = l_Lean_Syntax_node1(v___x_318_, v___x_322_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node2(v___x_318_, v___x_319_, v___x_321_, v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_a_309_);
return v___x_344_;
}
}
}
static lean_object* _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_347_ = l_String_toRawSubstring_x27(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_364_ = l_Lean_Syntax_isOfKind(v_x_360_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v_a_361_);
v___x_365_ = lean_box(1);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_362_);
return v___x_366_;
}
else
{
lean_object* v_quotContext_367_; lean_object* v_currMacroScope_368_; lean_object* v_ref_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_quotContext_367_ = lean_ctor_get(v_a_361_, 1);
lean_inc(v_quotContext_367_);
v_currMacroScope_368_ = lean_ctor_get(v_a_361_, 2);
lean_inc(v_currMacroScope_368_);
v_ref_369_ = lean_ctor_get(v_a_361_, 5);
lean_inc(v_ref_369_);
lean_dec_ref(v_a_361_);
v___x_370_ = 0;
v___x_371_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_370_);
lean_dec(v_ref_369_);
v___x_372_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6));
v___x_373_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7));
lean_inc(v___x_371_);
v___x_374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9));
v___x_376_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_377_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_378_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14));
v___x_379_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15));
lean_inc(v___x_371_);
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_371_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
v___x_381_ = lean_obj_once(&l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1, &l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_382_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3));
v___x_383_ = l_Lean_addMacroScope(v_quotContext_367_, v___x_382_, v_currMacroScope_368_);
v___x_384_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5));
lean_inc(v___x_371_);
v___x_385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_385_, 0, v___x_371_);
lean_ctor_set(v___x_385_, 1, v___x_381_);
lean_ctor_set(v___x_385_, 2, v___x_383_);
lean_ctor_set(v___x_385_, 3, v___x_384_);
lean_inc(v___x_371_);
v___x_386_ = l_Lean_Syntax_node2(v___x_371_, v___x_379_, v___x_380_, v___x_385_);
v___x_387_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25));
lean_inc(v___x_371_);
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_371_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26));
v___x_390_ = ((lean_object*)(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc(v___x_371_);
v___x_391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_371_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_inc(v___x_371_);
v___x_392_ = l_Lean_Syntax_node1(v___x_371_, v___x_390_, v___x_391_);
lean_inc(v___x_371_);
v___x_393_ = l_Lean_Syntax_node3(v___x_371_, v___x_377_, v___x_386_, v___x_388_, v___x_392_);
lean_inc(v___x_371_);
v___x_394_ = l_Lean_Syntax_node1(v___x_371_, v___x_376_, v___x_393_);
lean_inc(v___x_371_);
v___x_395_ = l_Lean_Syntax_node1(v___x_371_, v___x_375_, v___x_394_);
v___x_396_ = l_Lean_Syntax_node2(v___x_371_, v___x_372_, v___x_374_, v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_a_362_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr(lean_object* v_x_398_, uint32_t v_x_399_){
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
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_setCurr___boxed(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint32_t v_x_15__boxed_412_; lean_object* v_res_413_; 
v_x_15__boxed_412_ = lean_unbox_uint32(v_x_411_);
lean_dec(v_x_411_);
v_res_413_ = l_String_Legacy_Iterator_setCurr(v_x_410_, v_x_15__boxed_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_find(lean_object* v_it_414_, lean_object* v_p_415_){
_start:
{
lean_object* v_s_416_; lean_object* v_i_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_s_416_ = lean_ctor_get(v_it_414_, 0);
v_i_417_ = lean_ctor_get(v_it_414_, 1);
v___x_418_ = lean_string_utf8_byte_size(v_s_416_);
v___x_419_ = lean_nat_dec_le(v___x_418_, v_i_417_);
if (v___x_419_ == 0)
{
uint32_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_420_ = lean_string_utf8_get(v_s_416_, v_i_417_);
v___x_421_ = lean_box_uint32(v___x_420_);
lean_inc_ref(v_p_415_);
v___x_422_ = lean_apply_1(v_p_415_, v___x_421_);
v___x_423_ = lean_unbox(v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
lean_inc(v_i_417_);
lean_inc_ref(v_s_416_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_it_414_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_433_ = lean_ctor_get(v_it_414_, 1);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_it_414_, 0);
lean_dec(v_unused_434_);
v___x_425_ = v_it_414_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_dec(v_it_414_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = lean_string_utf8_next(v_s_416_, v_i_417_);
lean_dec(v_i_417_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_s_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v_it_414_ = v___x_429_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_415_);
return v_it_414_;
}
}
else
{
lean_dec_ref(v_p_415_);
return v_it_414_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil___redArg(lean_object* v_it_435_, lean_object* v_init_436_, lean_object* v_f_437_){
_start:
{
lean_object* v_s_438_; lean_object* v_i_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_s_438_ = lean_ctor_get(v_it_435_, 0);
v_i_439_ = lean_ctor_get(v_it_435_, 1);
v___x_440_ = lean_string_utf8_byte_size(v_s_438_);
v___x_441_ = lean_nat_dec_le(v___x_440_, v_i_439_);
if (v___x_441_ == 0)
{
uint32_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_string_utf8_get(v_s_438_, v_i_439_);
v___x_443_ = lean_box_uint32(v___x_442_);
lean_inc_ref(v_f_437_);
lean_inc(v_init_436_);
v___x_444_ = lean_apply_2(v_f_437_, v_init_436_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 1)
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_454_; 
lean_inc(v_i_439_);
lean_inc_ref(v_s_438_);
lean_dec(v_init_436_);
v_isSharedCheck_454_ = !lean_is_exclusive(v_it_435_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_455_ = lean_ctor_get(v_it_435_, 1);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_it_435_, 0);
lean_dec(v_unused_456_);
v___x_446_ = v_it_435_;
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_it_435_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_val_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v_val_448_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_448_);
lean_dec_ref(v___x_444_);
v___x_449_ = lean_string_utf8_next(v_s_438_, v_i_439_);
lean_dec(v_i_439_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_s_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_453_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v_it_435_ = v___x_451_;
v_init_436_ = v_val_448_;
goto _start;
}
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v___x_444_);
lean_dec_ref(v_f_437_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_init_436_);
lean_ctor_set(v___x_457_, 1, v_it_435_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_f_437_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_init_436_);
lean_ctor_set(v___x_458_, 1, v_it_435_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_String_Legacy_Iterator_foldUntil(lean_object* v_00_u03b1_459_, lean_object* v_it_460_, lean_object* v_init_461_, lean_object* v_f_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_460_, v_init_461_, v_f_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(lean_object* v_x_464_, lean_object* v_h__1_465_, lean_object* v_h__2_466_){
_start:
{
if (lean_obj_tag(v_x_464_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; 
lean_dec(v_h__2_466_);
v_val_467_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_val_467_);
lean_dec_ref(v_x_464_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(lean_object* v_00_u03b1_470_, lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
if (lean_obj_tag(v_x_472_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_476_; 
lean_dec(v_h__2_474_);
v_val_475_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v_x_472_);
v___x_476_ = lean_apply_1(v_h__1_473_, v_val_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v_h__1_473_);
v___x_477_ = lean_apply_2(v_h__2_474_, v_x_472_, lean_box(0));
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator(lean_object* v_x_478_){
_start:
{
lean_object* v_str_479_; lean_object* v_startPos_480_; lean_object* v___x_481_; 
v_str_479_ = lean_ctor_get(v_x_478_, 0);
v_startPos_480_ = lean_ctor_get(v_x_478_, 1);
lean_inc(v_startPos_480_);
lean_inc_ref(v_str_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_str_479_);
lean_ctor_set(v___x_481_, 1, v_startPos_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toLegacyIterator___boxed(lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Substring_Raw_toLegacyIterator(v_x_482_);
lean_dec_ref(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_s_498_; lean_object* v_i_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_519_; 
v_s_498_ = lean_ctor_get(v_x_496_, 0);
v_i_499_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_519_ == 0)
{
v___x_501_ = v_x_496_;
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_i_499_);
lean_inc(v_s_498_);
lean_dec(v_x_496_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_503_ = ((lean_object*)(l_instReprIterator___lam__0___closed__1));
v___x_504_ = l_String_quote(v_s_498_);
v___x_505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 5);
lean_ctor_set(v___x_501_, 1, v___x_505_);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_518_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_508_ = ((lean_object*)(l_instReprIterator___lam__0___closed__3));
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = ((lean_object*)(l_instReprIterator___lam__0___closed__5));
v___x_511_ = l_Nat_reprFast(v_i_499_);
v___x_512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = ((lean_object*)(l_instReprIterator___lam__0___closed__7));
v___x_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_509_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Repr_addAppParen(v___x_516_, v_x_497_);
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprIterator___lam__0___boxed(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_instReprIterator___lam__0(v_x_520_, v_x_521_);
lean_dec(v_x_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0(lean_object* v_it_525_){
_start:
{
lean_object* v_s_526_; lean_object* v_i_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_s_526_ = lean_ctor_get(v_it_525_, 0);
v_i_527_ = lean_ctor_get(v_it_525_, 1);
v___x_528_ = lean_string_utf8_byte_size(v_s_526_);
v___x_529_ = lean_string_utf8_extract(v_s_526_, v_i_527_, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_instToStringIterator___lam__0___boxed(lean_object* v_it_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_instToStringIterator___lam__0(v_it_530_);
lean_dec_ref(v_it_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* v_s_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_s_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* v_s_537_){
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
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object* v_a_540_){
_start:
{
lean_object* v_s_541_; lean_object* v_i_542_; uint32_t v___x_543_; 
v_s_541_ = lean_ctor_get(v_a_540_, 0);
v_i_542_ = lean_ctor_get(v_a_540_, 1);
v___x_543_ = lean_string_utf8_get(v_s_541_, v_i_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* v_a_544_){
_start:
{
uint32_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_String_Iterator_curr(v_a_544_);
lean_dec_ref(v_a_544_);
v_r_546_ = lean_box_uint32(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* v_a_547_){
_start:
{
lean_object* v_s_548_; lean_object* v_i_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_s_548_ = lean_ctor_get(v_a_547_, 0);
v_i_549_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_a_547_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_i_549_);
lean_inc(v_s_548_);
lean_dec(v_a_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_string_utf8_next(v_s_548_, v_i_549_);
lean_dec(v_i_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_s_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object* v_a_558_){
_start:
{
lean_object* v_s_559_; lean_object* v_i_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_s_559_ = lean_ctor_get(v_a_558_, 0);
v_i_560_ = lean_ctor_get(v_a_558_, 1);
v___x_561_ = lean_string_utf8_byte_size(v_s_559_);
v___x_562_ = lean_nat_dec_lt(v_i_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object* v_a_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_String_Iterator_hasNext(v_a_563_);
lean_dec_ref(v_a_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object* v_a_566_){
_start:
{
lean_object* v_str_567_; lean_object* v_startPos_568_; lean_object* v___x_569_; 
v_str_567_ = lean_ctor_get(v_a_566_, 0);
v_startPos_568_ = lean_ctor_get(v_a_566_, 1);
lean_inc(v_startPos_568_);
lean_inc_ref(v_str_567_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_str_567_);
lean_ctor_set(v___x_569_, 1, v_startPos_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Substring_toIterator(v_a_570_);
lean_dec_ref(v_a_570_);
return v_res_571_;
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
