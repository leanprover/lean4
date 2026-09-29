// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Parsing
// Imports: public import Lean.Parser.Extension public import Lean.DocString.Syntax public import Lean.DocString.View public import Init.While import Init.Data.Array.Attach import Init.Data.Array.Mem
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* l_Lean_Doc_VersoText_view(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Doc_RoleView_of(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_onlyCodes___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Expected code"};
static const lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Doc_onlyCodes___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1;
static const lean_closure_object l_Lean_Doc_onlyCodes___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Doc_onlyCodes___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_onlyCodes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_onlyCodes___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_onlyCodes___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__4_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__5_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__0_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__7 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__7_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__3_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__4_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__8 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__8_value),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__10 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_onlyCode___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected precisely 1 code argument"};
static const lean_object* l_Lean_Doc_onlyCode___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_onlyCode___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_onlyCode___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_onlyCode___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Not a quoted string literal"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0_value;
static lean_once_cell_t l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__0(lean_object* v___y_1_, lean_object* v_toPure_2_, lean_object* v_____r_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4_, 0, v___y_1_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Doc_onlyCodes___redArg___lam__2___closed__0));
v___x_8_ = l_Lean_stringToMessageData(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_Doc_onlyCodes___redArg___lam__2___closed__2));
v___x_11_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__2(lean_object* v_toPure_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_toBind_15_, lean_object* v___x_16_, lean_object* v_a_17_, lean_object* v_x_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_25_; 
lean_inc(v_toPure_12_);
lean_inc_ref(v___y_19_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCodes___redArg___lam__0), 3, 2);
lean_closure_set(v___f_20_, 0, v___y_19_);
lean_closure_set(v___f_20_, 1, v_toPure_12_);
lean_inc(v_a_17_);
v___x_25_ = l_Lean_Doc_InlineView_of(v_a_17_);
if (lean_obj_tag(v___x_25_) == 1)
{
lean_object* v_val_26_; 
v_val_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v___x_25_, 1);
switch(lean_obj_tag(v_val_26_))
{
case 3:
{
lean_object* v_view_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_37_; 
lean_dec_ref(v___f_20_);
lean_dec(v_a_17_);
lean_dec(v___x_16_);
lean_dec(v_toBind_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
v_view_27_ = lean_ctor_get(v_val_26_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_val_26_);
if (v_isSharedCheck_37_ == 0)
{
v___x_29_ = v_val_26_;
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_view_27_);
lean_dec(v_val_26_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_37_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v_content_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v_content_31_ = lean_ctor_get(v_view_27_, 2);
lean_inc(v_content_31_);
lean_dec_ref(v_view_27_);
v___x_32_ = lean_array_push(v___y_19_, v_content_31_);
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 1);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_34_ = v___x_29_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_36_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; 
v___x_35_ = lean_apply_2(v_toPure_12_, lean_box(0), v___x_34_);
return v___x_35_;
}
}
}
case 0:
{
lean_object* v_view_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_56_; 
v_view_38_ = lean_ctor_get(v_val_26_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v_val_26_);
if (v_isSharedCheck_56_ == 0)
{
v___x_40_ = v_val_26_;
v_isShared_41_ = v_isSharedCheck_56_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_view_38_);
lean_dec(v_val_26_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_56_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_content_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v_decide_48_; 
v_content_42_ = lean_ctor_get(v_view_38_, 1);
lean_inc(v_content_42_);
lean_dec_ref(v_view_38_);
v___x_43_ = l_Lean_Doc_VersoText_view(v_content_42_);
lean_dec(v_content_42_);
v___x_44_ = lean_obj_once(&l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3, &l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3_once, _init_l_Lean_Doc_onlyCodes___redArg___lam__2___closed__3);
v___x_45_ = lean_string_utf8_byte_size(v___x_43_);
lean_inc(v___x_16_);
v___x_46_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_46_, 0, v___x_43_);
lean_ctor_set(v___x_46_, 1, v___x_16_);
lean_ctor_set(v___x_46_, 2, v___x_45_);
v___x_47_ = l_String_Slice_Pos_skipWhile___redArg(v___x_46_, v___x_16_, v___x_44_);
lean_dec_ref_known(v___x_46_, 3);
v_decide_48_ = lean_nat_dec_eq(v___x_47_, v___x_45_);
lean_dec(v___x_47_);
if (v_decide_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_del_object(v___x_40_);
lean_dec_ref(v___y_19_);
lean_dec(v_toPure_12_);
v___x_49_ = lean_obj_once(&l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1, &l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1_once, _init_l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1);
v___x_50_ = l_Lean_throwErrorAt___redArg(v_inst_13_, v_inst_14_, v_a_17_, v___x_49_);
v___x_51_ = lean_apply_4(v_toBind_15_, lean_box(0), lean_box(0), v___x_50_, v___f_20_);
return v___x_51_;
}
else
{
lean_object* v___x_53_; 
lean_dec_ref(v___f_20_);
lean_dec(v_a_17_);
lean_dec(v_toBind_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
if (v_isShared_41_ == 0)
{
lean_ctor_set_tag(v___x_40_, 1);
lean_ctor_set(v___x_40_, 0, v___y_19_);
v___x_53_ = v___x_40_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___y_19_);
v___x_53_ = v_reuseFailAlloc_55_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_54_; 
v___x_54_ = lean_apply_2(v_toPure_12_, lean_box(0), v___x_53_);
return v___x_54_;
}
}
}
}
default: 
{
lean_dec(v_val_26_);
lean_dec_ref(v___y_19_);
lean_dec(v___x_16_);
lean_dec(v_toPure_12_);
goto v___jp_21_;
}
}
}
else
{
lean_dec(v___x_25_);
lean_dec_ref(v___y_19_);
lean_dec(v___x_16_);
lean_dec(v_toPure_12_);
goto v___jp_21_;
}
v___jp_21_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1, &l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1_once, _init_l_Lean_Doc_onlyCodes___redArg___lam__2___closed__1);
v___x_23_ = l_Lean_throwErrorAt___redArg(v_inst_13_, v_inst_14_, v_a_17_, v___x_22_);
v___x_24_ = lean_apply_4(v_toBind_15_, lean_box(0), lean_box(0), v___x_23_, v___f_20_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg___lam__1(lean_object* v_toPure_57_, lean_object* v_____s_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_2(v_toPure_57_, lean_box(0), v_____s_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_xs_64_){
_start:
{
lean_object* v_toApplicative_65_; lean_object* v_toBind_66_; lean_object* v_toPure_67_; lean_object* v___x_68_; lean_object* v_codes_69_; lean_object* v___f_70_; lean_object* v___f_71_; size_t v_sz_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_toApplicative_65_ = lean_ctor_get(v_inst_62_, 0);
v_toBind_66_ = lean_ctor_get(v_inst_62_, 1);
lean_inc_n(v_toBind_66_, 2);
v_toPure_67_ = lean_ctor_get(v_toApplicative_65_, 1);
v___x_68_ = lean_unsigned_to_nat(0u);
v_codes_69_ = ((lean_object*)(l_Lean_Doc_onlyCodes___redArg___closed__0));
lean_inc_ref(v_inst_62_);
lean_inc_n(v_toPure_67_, 2);
v___f_70_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCodes___redArg___lam__2), 8, 5);
lean_closure_set(v___f_70_, 0, v_toPure_67_);
lean_closure_set(v___f_70_, 1, v_inst_62_);
lean_closure_set(v___f_70_, 2, v_inst_63_);
lean_closure_set(v___f_70_, 3, v_toBind_66_);
lean_closure_set(v___f_70_, 4, v___x_68_);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCodes___redArg___lam__1), 2, 1);
lean_closure_set(v___f_71_, 0, v_toPure_67_);
v_sz_72_ = lean_array_size(v_xs_64_);
v___x_73_ = ((size_t)0ULL);
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_62_, v_xs_64_, v___f_70_, v_sz_72_, v___x_73_, v_codes_69_);
v___x_75_ = lean_apply_4(v_toBind_66_, lean_box(0), lean_box(0), v___x_74_, v___f_71_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCodes(lean_object* v_m_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_xs_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Doc_onlyCodes___redArg(v_inst_77_, v_inst_78_, v_xs_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0(lean_object* v_s_81_, lean_object* v_pos_82_){
_start:
{
lean_object* v_str_83_; lean_object* v_startInclusive_84_; lean_object* v_endExclusive_85_; lean_object* v___x_86_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v_decide_97_; 
v_str_83_ = lean_ctor_get(v_s_81_, 0);
v_startInclusive_84_ = lean_ctor_get(v_s_81_, 1);
v_endExclusive_85_ = lean_ctor_get(v_s_81_, 2);
v___x_86_ = lean_nat_add(v_startInclusive_84_, v_pos_82_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_sub(v_endExclusive_85_, v___x_86_);
v_decide_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
if (v_decide_97_ == 0)
{
uint32_t v___x_98_; uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_string_utf8_get_fast(v_str_83_, v___x_86_);
v___x_99_ = 32;
v___x_100_ = lean_uint32_dec_eq(v___x_98_, v___x_99_);
if (v___x_100_ == 0)
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 9;
v___x_102_ = lean_uint32_dec_eq(v___x_98_, v___x_101_);
if (v___x_102_ == 0)
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 13;
v___x_104_ = lean_uint32_dec_eq(v___x_98_, v___x_103_);
if (v___x_104_ == 0)
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 10;
v___x_106_ = lean_uint32_dec_eq(v___x_98_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec(v___x_86_);
return v_pos_82_;
}
else
{
goto v___jp_87_;
}
}
else
{
goto v___jp_87_;
}
}
else
{
goto v___jp_87_;
}
}
else
{
goto v___jp_87_;
}
}
else
{
lean_dec(v___x_86_);
return v_pos_82_;
}
v___jp_87_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_88_ = lean_string_utf8_next_fast(v_str_83_, v___x_86_);
v___x_89_ = lean_nat_sub(v___x_88_, v___x_86_);
lean_dec(v___x_86_);
v___x_90_ = lean_nat_add(v_pos_82_, v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_pos_82_, v___x_91_);
v___x_93_ = lean_nat_dec_le(v___x_92_, v___x_90_);
lean_dec(v___x_92_);
if (v___x_93_ == 0)
{
lean_dec(v___x_90_);
return v_pos_82_;
}
else
{
lean_dec(v_pos_82_);
v_pos_82_ = v___x_90_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0___boxed(lean_object* v_s_107_, lean_object* v_pos_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0(v_s_107_, v_pos_108_);
lean_dec_ref(v_s_107_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Doc_InlineView_of(v_x_110_);
if (lean_obj_tag(v___x_111_) == 1)
{
lean_object* v_val_112_; 
v_val_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_111_, 1);
if (lean_obj_tag(v_val_112_) == 0)
{
lean_object* v_view_113_; lean_object* v_content_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v_decide_120_; 
v_view_113_ = lean_ctor_get(v_val_112_, 0);
lean_inc_ref(v_view_113_);
lean_dec_ref_known(v_val_112_, 1);
v_content_114_ = lean_ctor_get(v_view_113_, 1);
lean_inc(v_content_114_);
lean_dec_ref(v_view_113_);
v___x_115_ = l_Lean_Doc_VersoText_view(v_content_114_);
lean_dec(v_content_114_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_string_utf8_byte_size(v___x_115_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_115_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
v___x_119_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_spec__0(v___x_118_, v___x_116_);
lean_dec_ref_known(v___x_118_, 3);
v_decide_120_ = lean_nat_dec_eq(v___x_119_, v___x_117_);
lean_dec(v___x_119_);
return v_decide_120_;
}
else
{
uint8_t v___x_121_; 
lean_dec(v_val_112_);
v___x_121_ = 0;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
lean_dec(v___x_111_);
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank___boxed(lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(v_x_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0(lean_object* v_x_126_){
_start:
{
lean_inc(v_x_126_);
return v_x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0___boxed(lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0(v_x_127_);
lean_dec(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(lean_object* v_v_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(v_v_129_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 1;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1___boxed(lean_object* v_v_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(v_v_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3(lean_object* v_xs_158_, lean_object* v_toPure_159_, lean_object* v___f_160_, lean_object* v___f_161_, lean_object* v___f_162_, lean_object* v_ref_163_){
_start:
{
lean_object* v___x_182_; 
lean_inc(v_ref_163_);
v___x_182_ = l_Lean_Doc_RoleView_of(v_ref_163_);
if (lean_obj_tag(v___x_182_) == 1)
{
lean_object* v_val_183_; lean_object* v_brackets_184_; 
v_val_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v___x_182_, 1);
v_brackets_184_ = lean_ctor_get(v_val_183_, 5);
lean_inc(v_brackets_184_);
lean_dec(v_val_183_);
if (lean_obj_tag(v_brackets_184_) == 1)
{
lean_object* v_val_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_ref_163_);
lean_dec_ref(v___f_161_);
lean_dec_ref(v___f_160_);
v_val_185_ = lean_ctor_get(v_brackets_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v_brackets_184_, 1);
v_fst_186_ = lean_ctor_get(v_val_185_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v_val_185_, 1);
lean_inc(v_snd_187_);
lean_dec(v_val_185_);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_mk_empty_array_with_capacity(v___x_188_);
lean_inc_ref(v___x_189_);
v___x_190_ = lean_array_push(v___x_189_, v_fst_186_);
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v_sz_192_ = lean_array_size(v_xs_158_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_191_, v___f_162_, v_sz_192_, v___x_193_, v_xs_158_);
v___x_195_ = l_Array_append___redArg(v___x_190_, v___x_194_);
lean_dec(v___x_194_);
v___x_196_ = lean_array_push(v___x_189_, v_snd_187_);
v___x_197_ = l_Array_append___redArg(v___x_195_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11));
v___x_199_ = lean_box(2);
v___x_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 2, v___x_197_);
v___x_201_ = lean_apply_2(v_toPure_159_, lean_box(0), v___x_200_);
return v___x_201_;
}
else
{
lean_dec(v_brackets_184_);
lean_dec_ref(v___f_162_);
goto v___jp_164_;
}
}
else
{
lean_dec(v___x_182_);
lean_dec_ref(v___f_162_);
goto v___jp_164_;
}
v___jp_164_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_array_get_size(v_xs_158_);
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v___x_168_ = lean_nat_dec_lt(v___x_165_, v___x_166_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec_ref(v___f_161_);
lean_dec_ref(v___f_160_);
lean_dec_ref(v_xs_158_);
v___x_169_ = lean_apply_2(v_toPure_159_, lean_box(0), v_ref_163_);
return v___x_169_;
}
else
{
if (v___x_168_ == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v___f_161_);
lean_dec_ref(v___f_160_);
lean_dec_ref(v_xs_158_);
v___x_170_ = lean_apply_2(v_toPure_159_, lean_box(0), v_ref_163_);
return v___x_170_;
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_166_);
lean_inc_ref(v_xs_158_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_167_, v___f_160_, v_xs_158_, v___x_171_, v___x_172_);
v___x_174_ = lean_unbox(v___x_173_);
lean_dec(v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v___f_161_);
lean_dec_ref(v_xs_158_);
v___x_175_ = lean_apply_2(v_toPure_159_, lean_box(0), v_ref_163_);
return v___x_175_;
}
else
{
size_t v_sz_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_ref_163_);
v_sz_176_ = lean_array_size(v_xs_158_);
v___x_177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_167_, v___f_161_, v_sz_176_, v___x_171_, v_xs_158_);
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11));
v___x_179_ = lean_box(2);
v___x_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
v___x_181_ = lean_apply_2(v_toPure_159_, lean_box(0), v___x_180_);
return v___x_181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_xs_206_){
_start:
{
lean_object* v_toApplicative_207_; lean_object* v_toBind_208_; lean_object* v_getRef_209_; lean_object* v_toPure_210_; lean_object* v___f_211_; lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___x_214_; 
v_toApplicative_207_ = lean_ctor_get(v_inst_204_, 0);
lean_inc_ref(v_toApplicative_207_);
v_toBind_208_ = lean_ctor_get(v_inst_204_, 1);
lean_inc(v_toBind_208_);
lean_dec_ref(v_inst_204_);
v_getRef_209_ = lean_ctor_get(v_inst_205_, 0);
lean_inc(v_getRef_209_);
lean_dec_ref(v_inst_205_);
v_toPure_210_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_inc(v_toPure_210_);
lean_dec_ref(v_toApplicative_207_);
v___f_211_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__0));
v___f_212_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__1));
v___f_213_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3), 6, 5);
lean_closure_set(v___f_213_, 0, v_xs_206_);
lean_closure_set(v___f_213_, 1, v_toPure_210_);
lean_closure_set(v___f_213_, 2, v___f_212_);
lean_closure_set(v___f_213_, 3, v___f_211_);
lean_closure_set(v___f_213_, 4, v___f_211_);
v___x_214_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v_getRef_209_, v___f_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange(lean_object* v_m_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_xs_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(v_inst_216_, v_inst_217_, v_xs_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Doc_onlyCode___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Doc_onlyCode___redArg___lam__0___closed__0));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__0(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_____do__lift_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lean_Doc_onlyCode___redArg___lam__0___closed__1, &l_Lean_Doc_onlyCode___redArg___lam__0___closed__1_once, _init_l_Lean_Doc_onlyCode___redArg___lam__0___closed__1);
v___x_227_ = l_Lean_throwErrorAt___redArg(v_inst_223_, v_inst_224_, v_____do__lift_225_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1(lean_object* v_inst_228_, lean_object* v_toMonadRef_229_, lean_object* v_xs_230_, lean_object* v_toBind_231_, lean_object* v___f_232_, lean_object* v_toPure_233_, lean_object* v_codes_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_array_get_size(v_codes_234_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_toPure_233_);
v___x_238_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(v_inst_228_, v_toMonadRef_229_, v_xs_230_);
v___x_239_ = lean_apply_4(v_toBind_231_, lean_box(0), lean_box(0), v___x_238_, v___f_232_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v___f_232_);
lean_dec(v_toBind_231_);
lean_dec_ref(v_xs_230_);
lean_dec_ref(v_toMonadRef_229_);
lean_dec_ref(v_inst_228_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_array_fget_borrowed(v_codes_234_, v___x_240_);
lean_inc(v___x_241_);
v___x_242_ = lean_apply_2(v_toPure_233_, lean_box(0), v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1___boxed(lean_object* v_inst_243_, lean_object* v_toMonadRef_244_, lean_object* v_xs_245_, lean_object* v_toBind_246_, lean_object* v___f_247_, lean_object* v_toPure_248_, lean_object* v_codes_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Doc_onlyCode___redArg___lam__1(v_inst_243_, v_toMonadRef_244_, v_xs_245_, v_toBind_246_, v___f_247_, v_toPure_248_, v_codes_249_);
lean_dec_ref(v_codes_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg(lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_xs_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toBind_255_; lean_object* v_toMonadRef_256_; lean_object* v_toPure_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_251_, 0);
v_toBind_255_ = lean_ctor_get(v_inst_251_, 1);
lean_inc_n(v_toBind_255_, 2);
v_toMonadRef_256_ = lean_ctor_get(v_inst_252_, 1);
lean_inc_ref(v_toMonadRef_256_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_257_);
lean_inc_ref(v_inst_252_);
lean_inc_ref_n(v_inst_251_, 2);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCode___redArg___lam__0), 3, 2);
lean_closure_set(v___f_258_, 0, v_inst_251_);
lean_closure_set(v___f_258_, 1, v_inst_252_);
lean_inc_ref(v_xs_253_);
v___x_259_ = l_Lean_Doc_onlyCodes___redArg(v_inst_251_, v_inst_252_, v_xs_253_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCode___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_260_, 0, v_inst_251_);
lean_closure_set(v___f_260_, 1, v_toMonadRef_256_);
lean_closure_set(v___f_260_, 2, v_xs_253_);
lean_closure_set(v___f_260_, 3, v_toBind_255_);
lean_closure_set(v___f_260_, 4, v___f_258_);
lean_closure_set(v___f_260_, 5, v_toPure_257_);
v___x_261_ = lean_apply_4(v_toBind_255_, lean_box(0), lean_box(0), v___x_259_, v___f_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode(lean_object* v_m_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_xs_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Doc_onlyCode___redArg(v_inst_263_, v_inst_264_, v_xs_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2));
v___x_271_ = lean_unsigned_to_nat(14u);
v___x_272_ = lean_unsigned_to_nat(22u);
v___x_273_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1));
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0));
v___x_275_ = l_mkPanicMessageWithDecl(v___x_274_, v___x_273_, v___x_272_, v___x_271_, v___x_270_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object* v_inst_276_, lean_object* v_s_277_){
_start:
{
lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___x_292_; uint8_t v___x_293_; lean_object* v___y_295_; lean_object* v___x_300_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = 1;
v___x_300_ = l_Lean_Syntax_getPos_x3f(v_s_277_, v___x_293_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_302_ = l_panic___redArg(v___x_292_, v___x_301_);
v___y_295_ = v___x_302_;
goto v___jp_294_;
}
else
{
lean_object* v_val_303_; 
v_val_303_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_val_303_);
lean_dec_ref_known(v___x_300_, 1);
v___y_295_ = v_val_303_;
goto v___jp_294_;
}
v___jp_278_:
{
lean_object* v_toApplicative_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_290_; 
v_toApplicative_281_ = lean_ctor_get(v_inst_276_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_inst_276_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v_inst_276_, 1);
lean_dec(v_unused_291_);
v___x_283_ = v_inst_276_;
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_toApplicative_281_);
lean_dec(v_inst_276_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_toPure_285_; lean_object* v___x_287_; 
v_toPure_285_ = lean_ctor_get(v_toApplicative_281_, 1);
lean_inc(v_toPure_285_);
lean_dec_ref(v_toApplicative_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___y_280_);
lean_ctor_set(v___x_283_, 0, v___y_279_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___y_279_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___y_280_);
v___x_287_ = v_reuseFailAlloc_289_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_apply_2(v_toPure_285_, lean_box(0), v___x_287_);
return v___x_288_;
}
}
}
v___jp_294_:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Syntax_getTailPos_x3f(v_s_277_, v___x_293_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_298_ = l_panic___redArg(v___x_292_, v___x_297_);
v___y_279_ = v___y_295_;
v___y_280_ = v___x_298_;
goto v___jp_278_;
}
else
{
lean_object* v_val_299_; 
v_val_299_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_299_);
lean_dec_ref_known(v___x_296_, 1);
v___y_279_ = v___y_295_;
v___y_280_ = v_val_299_;
goto v___jp_278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object* v_inst_304_, lean_object* v_s_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_304_, v_s_305_);
lean_dec(v_s_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object* v_m_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_s_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_308_, v_s_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object* v_m_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_s_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(v_m_312_, v_inst_313_, v_inst_314_, v_s_315_);
lean_dec(v_s_315_);
lean_dec(v_inst_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object* v_env_318_, lean_object* v_contents_319_, lean_object* v_p_320_, lean_object* v_ictx_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_toPure_324_, lean_object* v_____do__lift_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_s_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_box(0);
lean_inc_ref(v_env_318_);
v___x_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_328_, 0, v_env_318_);
lean_ctor_set(v___x_328_, 1, v_____do__lift_325_);
lean_ctor_set(v___x_328_, 2, v___x_326_);
lean_ctor_set(v___x_328_, 3, v___x_327_);
v___x_329_ = l_Lean_Parser_getTokenTable(v_env_318_);
v___x_330_ = l_Lean_Parser_mkParserState(v_contents_319_);
lean_inc_ref(v_ictx_321_);
v_s_331_ = l_Lean_Parser_ParserFn_run(v_p_320_, v_ictx_321_, v___x_328_, v___x_329_, v___x_330_);
lean_inc_ref(v_s_331_);
v___x_332_ = l_Lean_Parser_ParserState_allErrors(v_s_331_);
v___x_333_ = lean_array_get_size(v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_toPure_324_);
v___x_336_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_321_, v_s_331_);
v___x_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
v___x_338_ = l_Lean_MessageData_ofFormat(v___x_337_);
v___x_339_ = l_Lean_throwError___redArg(v_inst_322_, v_inst_323_, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v_stxStack_340_; lean_object* v_pos_341_; uint8_t v___x_342_; 
v_stxStack_340_ = lean_ctor_get(v_s_331_, 0);
lean_inc_ref(v_stxStack_340_);
v_pos_341_ = lean_ctor_get(v_s_331_, 2);
lean_inc(v_pos_341_);
v___x_342_ = l_Lean_Parser_InputContext_atEnd(v_ictx_321_, v_pos_341_);
lean_dec(v_pos_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref(v_stxStack_340_);
lean_dec(v_toPure_324_);
v___x_343_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_344_ = l_Lean_Parser_ParserState_mkError(v_s_331_, v___x_343_);
v___x_345_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_321_, v___x_344_);
v___x_346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___x_347_ = l_Lean_MessageData_ofFormat(v___x_346_);
v___x_348_ = l_Lean_throwError___redArg(v_inst_322_, v_inst_323_, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_s_331_);
lean_dec_ref(v_inst_323_);
lean_dec_ref(v_inst_322_);
lean_dec_ref(v_ictx_321_);
v___x_349_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_340_);
lean_dec_ref(v_stxStack_340_);
v___x_350_ = lean_apply_2(v_toPure_324_, lean_box(0), v___x_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_351_, lean_object* v_contents_352_, lean_object* v_p_353_, lean_object* v_ictx_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_toPure_357_, lean_object* v_____do__lift_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_351_, v_contents_352_, v_p_353_, v_ictx_354_, v_inst_355_, v_inst_356_, v_toPure_357_, v_____do__lift_358_);
lean_dec_ref(v_contents_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_inst_360_, lean_object* v_contents_361_, lean_object* v_env_362_, lean_object* v_p_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_toPure_366_, lean_object* v_toBind_367_, lean_object* v_____do__lift_368_){
_start:
{
lean_object* v_getOptions_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v_ictx_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_getOptions_369_ = lean_ctor_get(v_inst_360_, 0);
lean_inc(v_getOptions_369_);
lean_dec_ref(v_inst_360_);
v___x_370_ = lean_string_utf8_byte_size(v_contents_361_);
v___x_371_ = 1;
lean_inc_ref(v_contents_361_);
v_ictx_372_ = l_Lean_Parser_mkInputContext___redArg(v_contents_361_, v_____do__lift_368_, v___x_371_, v___x_370_);
v___f_373_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_373_, 0, v_env_362_);
lean_closure_set(v___f_373_, 1, v_contents_361_);
lean_closure_set(v___f_373_, 2, v_p_363_);
lean_closure_set(v___f_373_, 3, v_ictx_372_);
lean_closure_set(v___f_373_, 4, v_inst_364_);
lean_closure_set(v___f_373_, 5, v_inst_365_);
lean_closure_set(v___f_373_, 6, v_toPure_366_);
v___x_374_ = lean_apply_4(v_toBind_367_, lean_box(0), lean_box(0), v_getOptions_369_, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_contents_377_, lean_object* v_p_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_toPure_381_, lean_object* v_toBind_382_, lean_object* v_env_383_){
_start:
{
lean_object* v_getFileName_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
v_getFileName_384_ = lean_ctor_get(v_inst_375_, 2);
lean_inc(v_getFileName_384_);
lean_dec_ref(v_inst_375_);
lean_inc(v_toBind_382_);
v___f_385_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_385_, 0, v_inst_376_);
lean_closure_set(v___f_385_, 1, v_contents_377_);
lean_closure_set(v___f_385_, 2, v_env_383_);
lean_closure_set(v___f_385_, 3, v_p_378_);
lean_closure_set(v___f_385_, 4, v_inst_379_);
lean_closure_set(v___f_385_, 5, v_inst_380_);
lean_closure_set(v___f_385_, 6, v_toPure_381_);
lean_closure_set(v___f_385_, 7, v_toBind_382_);
v___x_386_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v_getFileName_384_, v___f_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_p_392_, lean_object* v_contents_393_){
_start:
{
lean_object* v_toApplicative_394_; lean_object* v_toBind_395_; lean_object* v_getEnv_396_; lean_object* v_toPure_397_; lean_object* v___f_398_; lean_object* v___x_399_; 
v_toApplicative_394_ = lean_ctor_get(v_inst_387_, 0);
v_toBind_395_ = lean_ctor_get(v_inst_387_, 1);
lean_inc_n(v_toBind_395_, 2);
v_getEnv_396_ = lean_ctor_get(v_inst_388_, 0);
lean_inc(v_getEnv_396_);
lean_dec_ref(v_inst_388_);
v_toPure_397_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_397_);
v___f_398_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_398_, 0, v_inst_390_);
lean_closure_set(v___f_398_, 1, v_inst_391_);
lean_closure_set(v___f_398_, 2, v_contents_393_);
lean_closure_set(v___f_398_, 3, v_p_392_);
lean_closure_set(v___f_398_, 4, v_inst_387_);
lean_closure_set(v___f_398_, 5, v_inst_389_);
lean_closure_set(v___f_398_, 6, v_toPure_397_);
lean_closure_set(v___f_398_, 7, v_toBind_395_);
v___x_399_ = lean_apply_4(v_toBind_395_, lean_box(0), lean_box(0), v_getEnv_396_, v___f_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_p_406_, lean_object* v_contents_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_inst_405_, v_p_406_, v_contents_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object* v_env_409_, lean_object* v_p_410_, lean_object* v_ictx_411_, lean_object* v_s_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_toPure_415_, lean_object* v_____do__lift_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_s_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_box(0);
lean_inc_ref(v_env_409_);
v___x_419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_419_, 0, v_env_409_);
lean_ctor_set(v___x_419_, 1, v_____do__lift_416_);
lean_ctor_set(v___x_419_, 2, v___x_417_);
lean_ctor_set(v___x_419_, 3, v___x_418_);
v___x_420_ = l_Lean_Parser_getTokenTable(v_env_409_);
lean_inc_ref(v_ictx_411_);
v_s_421_ = l_Lean_Parser_ParserFn_run(v_p_410_, v_ictx_411_, v___x_419_, v___x_420_, v_s_412_);
lean_inc_ref(v_s_421_);
v___x_422_ = l_Lean_Parser_ParserState_allErrors(v_s_421_);
v___x_423_ = lean_array_get_size(v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_nat_dec_eq(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_toPure_415_);
v___x_426_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_411_, v_s_421_);
v___x_427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___x_428_ = l_Lean_MessageData_ofFormat(v___x_427_);
v___x_429_ = l_Lean_throwError___redArg(v_inst_413_, v_inst_414_, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v_stxStack_430_; lean_object* v_pos_431_; uint8_t v___x_432_; 
v_stxStack_430_ = lean_ctor_get(v_s_421_, 0);
lean_inc_ref(v_stxStack_430_);
v_pos_431_ = lean_ctor_get(v_s_421_, 2);
lean_inc(v_pos_431_);
v___x_432_ = l_Lean_Parser_InputContext_atEnd(v_ictx_411_, v_pos_431_);
lean_dec(v_pos_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v_stxStack_430_);
lean_dec(v_toPure_415_);
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_434_ = l_Lean_Parser_ParserState_mkError(v_s_421_, v___x_433_);
v___x_435_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_411_, v___x_434_);
v___x_436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = l_Lean_MessageData_ofFormat(v___x_436_);
v___x_438_ = l_Lean_throwError___redArg(v_inst_413_, v_inst_414_, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_s_421_);
lean_dec_ref(v_inst_414_);
lean_dec_ref(v_inst_413_);
lean_dec_ref(v_ictx_411_);
v___x_439_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_430_);
lean_dec_ref(v_stxStack_430_);
v___x_440_ = lean_apply_2(v_toPure_415_, lean_box(0), v___x_439_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object* v_inst_441_, lean_object* v_source_442_, uint8_t v___x_443_, lean_object* v___y_444_, lean_object* v_start_445_, lean_object* v_env_446_, lean_object* v_p_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_toPure_450_, lean_object* v_toBind_451_, lean_object* v_____do__lift_452_){
_start:
{
lean_object* v_getOptions_453_; lean_object* v_ictx_454_; lean_object* v___x_455_; lean_object* v_s_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_getOptions_453_ = lean_ctor_get(v_inst_441_, 0);
lean_inc(v_getOptions_453_);
lean_dec_ref(v_inst_441_);
lean_inc_ref(v_source_442_);
v_ictx_454_ = l_Lean_Parser_mkInputContext___redArg(v_source_442_, v_____do__lift_452_, v___x_443_, v___y_444_);
v___x_455_ = l_Lean_Parser_mkParserState(v_source_442_);
lean_dec_ref(v_source_442_);
v_s_456_ = l_Lean_Parser_ParserState_setPos(v___x_455_, v_start_445_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__0), 8, 7);
lean_closure_set(v___f_457_, 0, v_env_446_);
lean_closure_set(v___f_457_, 1, v_p_447_);
lean_closure_set(v___f_457_, 2, v_ictx_454_);
lean_closure_set(v___f_457_, 3, v_s_456_);
lean_closure_set(v___f_457_, 4, v_inst_448_);
lean_closure_set(v___f_457_, 5, v_inst_449_);
lean_closure_set(v___f_457_, 6, v_toPure_450_);
v___x_458_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v_getOptions_453_, v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object* v_inst_459_, lean_object* v_source_460_, lean_object* v___x_461_, lean_object* v___y_462_, lean_object* v_start_463_, lean_object* v_env_464_, lean_object* v_p_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_toPure_468_, lean_object* v_toBind_469_, lean_object* v_____do__lift_470_){
_start:
{
uint8_t v___x_363__boxed_471_; lean_object* v_res_472_; 
v___x_363__boxed_471_ = lean_unbox(v___x_461_);
v_res_472_ = l_Lean_Doc_parseContent___redArg___lam__1(v_inst_459_, v_source_460_, v___x_363__boxed_471_, v___y_462_, v_start_463_, v_env_464_, v_p_465_, v_inst_466_, v_inst_467_, v_toPure_468_, v_toBind_469_, v_____do__lift_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object* v_text_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, uint8_t v___x_476_, lean_object* v_env_477_, lean_object* v_p_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_toPure_481_, lean_object* v_toBind_482_, lean_object* v_____x_483_){
_start:
{
lean_object* v_start_484_; lean_object* v_stop_485_; lean_object* v_source_486_; lean_object* v___y_488_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_start_484_ = lean_ctor_get(v_____x_483_, 0);
lean_inc(v_start_484_);
v_stop_485_ = lean_ctor_get(v_____x_483_, 1);
lean_inc(v_stop_485_);
lean_dec_ref(v_____x_483_);
v_source_486_ = lean_ctor_get(v_text_473_, 0);
lean_inc_ref(v_source_486_);
lean_dec_ref(v_text_473_);
v___x_493_ = lean_string_utf8_byte_size(v_source_486_);
v___x_494_ = lean_nat_dec_le(v_stop_485_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_stop_485_);
v___y_488_ = v___x_493_;
goto v___jp_487_;
}
else
{
v___y_488_ = v_stop_485_;
goto v___jp_487_;
}
v___jp_487_:
{
lean_object* v_getFileName_489_; lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; 
v_getFileName_489_ = lean_ctor_get(v_inst_474_, 2);
lean_inc(v_getFileName_489_);
lean_dec_ref(v_inst_474_);
v___x_490_ = lean_box(v___x_476_);
lean_inc(v_toBind_482_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_491_, 0, v_inst_475_);
lean_closure_set(v___f_491_, 1, v_source_486_);
lean_closure_set(v___f_491_, 2, v___x_490_);
lean_closure_set(v___f_491_, 3, v___y_488_);
lean_closure_set(v___f_491_, 4, v_start_484_);
lean_closure_set(v___f_491_, 5, v_env_477_);
lean_closure_set(v___f_491_, 6, v_p_478_);
lean_closure_set(v___f_491_, 7, v_inst_479_);
lean_closure_set(v___f_491_, 8, v_inst_480_);
lean_closure_set(v___f_491_, 9, v_toPure_481_);
lean_closure_set(v___f_491_, 10, v_toBind_482_);
v___x_492_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v_getFileName_489_, v___f_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object* v_text_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v___x_498_, lean_object* v_env_499_, lean_object* v_p_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_toPure_503_, lean_object* v_toBind_504_, lean_object* v_____x_505_){
_start:
{
uint8_t v___x_391__boxed_506_; lean_object* v_res_507_; 
v___x_391__boxed_506_ = lean_unbox(v___x_498_);
v_res_507_ = l_Lean_Doc_parseContent___redArg___lam__2(v_text_495_, v_inst_496_, v_inst_497_, v___x_391__boxed_506_, v_env_499_, v_p_500_, v_inst_501_, v_inst_502_, v_toPure_503_, v_toBind_504_, v_____x_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object* v_text_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, uint8_t v___x_511_, lean_object* v_p_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_toPure_515_, lean_object* v_toBind_516_, lean_object* v_tok_517_, lean_object* v_env_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_box(v___x_511_);
lean_inc(v_toBind_516_);
lean_inc_ref(v_inst_513_);
v___f_520_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_520_, 0, v_text_508_);
lean_closure_set(v___f_520_, 1, v_inst_509_);
lean_closure_set(v___f_520_, 2, v_inst_510_);
lean_closure_set(v___f_520_, 3, v___x_519_);
lean_closure_set(v___f_520_, 4, v_env_518_);
lean_closure_set(v___f_520_, 5, v_p_512_);
lean_closure_set(v___f_520_, 6, v_inst_513_);
lean_closure_set(v___f_520_, 7, v_inst_514_);
lean_closure_set(v___f_520_, 8, v_toPure_515_);
lean_closure_set(v___f_520_, 9, v_toBind_516_);
v___x_521_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_513_, v_tok_517_);
v___x_522_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_521_, v___f_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object* v_text_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v___x_526_, lean_object* v_p_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_toPure_530_, lean_object* v_toBind_531_, lean_object* v_tok_532_, lean_object* v_env_533_){
_start:
{
uint8_t v___x_427__boxed_534_; lean_object* v_res_535_; 
v___x_427__boxed_534_ = lean_unbox(v___x_526_);
v_res_535_ = l_Lean_Doc_parseContent___redArg___lam__3(v_text_523_, v_inst_524_, v_inst_525_, v___x_427__boxed_534_, v_p_527_, v_inst_528_, v_inst_529_, v_toPure_530_, v_toBind_531_, v_tok_532_, v_env_533_);
lean_dec(v_tok_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, uint8_t v___x_539_, lean_object* v_p_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_toPure_543_, lean_object* v_toBind_544_, lean_object* v_tok_545_, lean_object* v_text_546_){
_start:
{
lean_object* v_getEnv_547_; lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v___x_550_; 
v_getEnv_547_ = lean_ctor_get(v_inst_536_, 0);
lean_inc(v_getEnv_547_);
lean_dec_ref(v_inst_536_);
v___x_548_ = lean_box(v___x_539_);
lean_inc(v_toBind_544_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_549_, 0, v_text_546_);
lean_closure_set(v___f_549_, 1, v_inst_537_);
lean_closure_set(v___f_549_, 2, v_inst_538_);
lean_closure_set(v___f_549_, 3, v___x_548_);
lean_closure_set(v___f_549_, 4, v_p_540_);
lean_closure_set(v___f_549_, 5, v_inst_541_);
lean_closure_set(v___f_549_, 6, v_inst_542_);
lean_closure_set(v___f_549_, 7, v_toPure_543_);
lean_closure_set(v___f_549_, 8, v_toBind_544_);
lean_closure_set(v___f_549_, 9, v_tok_545_);
v___x_550_ = lean_apply_4(v_toBind_544_, lean_box(0), lean_box(0), v_getEnv_547_, v___f_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v___x_554_, lean_object* v_p_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_toPure_558_, lean_object* v_toBind_559_, lean_object* v_tok_560_, lean_object* v_text_561_){
_start:
{
uint8_t v___x_451__boxed_562_; lean_object* v_res_563_; 
v___x_451__boxed_562_ = lean_unbox(v___x_554_);
v_res_563_ = l_Lean_Doc_parseContent___redArg___lam__4(v_inst_551_, v_inst_552_, v_inst_553_, v___x_451__boxed_562_, v_p_555_, v_inst_556_, v_inst_557_, v_toPure_558_, v_toBind_559_, v_tok_560_, v_text_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_p_570_, lean_object* v_tok_571_, lean_object* v_contents_572_){
_start:
{
uint8_t v___x_573_; uint8_t v___y_575_; lean_object* v___x_583_; 
v___x_573_ = 1;
v___x_583_ = l_Lean_Syntax_getPos_x3f(v_tok_571_, v___x_573_);
if (lean_obj_tag(v___x_583_) == 0)
{
v___y_575_ = v___x_573_;
goto v___jp_574_;
}
else
{
uint8_t v___x_584_; 
lean_dec_ref_known(v___x_583_, 1);
v___x_584_ = 0;
v___y_575_ = v___x_584_;
goto v___jp_574_;
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v_toApplicative_576_; lean_object* v_toBind_577_; lean_object* v_toPure_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; 
v_toApplicative_576_ = lean_ctor_get(v_inst_564_, 0);
lean_dec_ref(v_contents_572_);
v_toBind_577_ = lean_ctor_get(v_inst_564_, 1);
lean_inc_n(v_toBind_577_, 2);
v_toPure_578_ = lean_ctor_get(v_toApplicative_576_, 1);
lean_inc(v_toPure_578_);
v___x_579_ = lean_box(v___x_573_);
v___f_580_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_580_, 0, v_inst_566_);
lean_closure_set(v___f_580_, 1, v_inst_568_);
lean_closure_set(v___f_580_, 2, v_inst_569_);
lean_closure_set(v___f_580_, 3, v___x_579_);
lean_closure_set(v___f_580_, 4, v_p_570_);
lean_closure_set(v___f_580_, 5, v_inst_564_);
lean_closure_set(v___f_580_, 6, v_inst_567_);
lean_closure_set(v___f_580_, 7, v_toPure_578_);
lean_closure_set(v___f_580_, 8, v_toBind_577_);
lean_closure_set(v___f_580_, 9, v_tok_571_);
v___x_581_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v_inst_565_, v___f_580_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; 
lean_dec(v_tok_571_);
lean_dec(v_inst_565_);
v___x_582_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_564_, v_inst_566_, v_inst_567_, v_inst_568_, v_inst_569_, v_p_570_, v_contents_572_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object* v_m_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_p_592_, lean_object* v_tok_593_, lean_object* v_contents_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Doc_parseContent___redArg(v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_inst_590_, v_inst_591_, v_p_592_, v_tok_593_, v_contents_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_614_; 
v_fst_598_ = lean_ctor_get(v_a_597_, 0);
v_snd_599_ = lean_ctor_get(v_a_597_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_614_ == 0)
{
v___x_601_ = v_a_597_;
v_isShared_602_ = v_isSharedCheck_614_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
lean_dec(v_a_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_614_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_dec_le(v___x_603_, v_fst_598_);
if (v___x_604_ == 0)
{
lean_object* v___x_606_; 
if (v_isShared_602_ == 0)
{
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_fst_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_snd_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_string_utf8_prev(v_str_596_, v_fst_598_);
lean_dec(v_fst_598_);
v___x_609_ = lean_nat_add(v_snd_599_, v___x_603_);
lean_dec(v_snd_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v___x_609_);
lean_ctor_set(v___x_601_, 0, v___x_608_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_609_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v_a_597_ = v___x_611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_615_, v_a_616_);
lean_dec_ref(v_str_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_618_, lean_object* v_p_619_){
_start:
{
lean_object* v_n_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_snd_623_; 
v_n_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_p_619_);
lean_ctor_set(v___x_621_, 1, v_n_620_);
v___x_622_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_618_, v___x_621_);
v_snd_623_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_622_);
return v_snd_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_624_, lean_object* v_p_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_624_, v_p_625_);
lean_dec_ref(v_str_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_627_, lean_object* v_inst_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_627_, v_a_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_631_, lean_object* v_inst_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_631_, v_inst_632_, v_a_633_);
lean_dec_ref(v_str_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_635_, lean_object* v_p_636_, lean_object* v_j_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_zero_639_; uint8_t v_isZero_640_; 
v_zero_639_ = lean_unsigned_to_nat(0u);
v_isZero_640_ = lean_nat_dec_eq(v_j_637_, v_zero_639_);
if (v_isZero_640_ == 1)
{
lean_dec(v_j_637_);
return v_a_638_;
}
else
{
lean_object* v_one_641_; lean_object* v_n_642_; lean_object* v___x_643_; 
lean_dec(v_a_638_);
v_one_641_ = lean_unsigned_to_nat(1u);
v_n_642_ = lean_nat_sub(v_j_637_, v_one_641_);
lean_dec(v_j_637_);
v___x_643_ = lean_string_utf8_next(v_str_635_, v_p_636_);
v_j_637_ = v_n_642_;
v_a_638_ = v___x_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_645_, lean_object* v_p_646_, lean_object* v_j_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_645_, v_p_646_, v_j_647_, v_a_648_);
lean_dec(v_p_646_);
lean_dec_ref(v_str_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_650_, lean_object* v_n_651_, lean_object* v_p_652_){
_start:
{
lean_object* v___x_653_; 
lean_inc(v_p_652_);
v___x_653_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_650_, v_p_652_, v_n_651_, v_p_652_);
lean_dec(v_p_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_654_, lean_object* v_n_655_, lean_object* v_p_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_654_, v_n_655_, v_p_656_);
lean_dec_ref(v_str_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_658_, lean_object* v_p_659_, lean_object* v_n_660_, lean_object* v_j_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_658_, v_p_659_, v_j_661_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_665_, lean_object* v_p_666_, lean_object* v_n_667_, lean_object* v_j_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_665_, v_p_666_, v_n_667_, v_j_668_, v_a_669_, v_a_670_);
lean_dec(v_n_667_);
lean_dec(v_p_666_);
lean_dec_ref(v_str_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_672_, lean_object* v_posOfStr_673_, lean_object* v_str_674_, lean_object* v_posInStr_675_){
_start:
{
lean_object* v_source_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_source_676_ = lean_ctor_get(v_text_672_, 0);
v___x_677_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_674_, v_posInStr_675_);
lean_inc(v_posOfStr_673_);
v___x_678_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_676_, v_posOfStr_673_, v___x_677_, v_posOfStr_673_);
lean_dec(v_posOfStr_673_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_679_, lean_object* v_posOfStr_680_, lean_object* v_str_681_, lean_object* v_posInStr_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_679_, v_posOfStr_680_, v_str_681_, v_posInStr_682_);
lean_dec_ref(v_str_681_);
lean_dec_ref(v_text_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_684_, lean_object* v_posOfStr_685_, lean_object* v_str_686_, lean_object* v_a_687_){
_start:
{
switch(lean_obj_tag(v_a_687_))
{
case 0:
{
lean_object* v_pos_688_; lean_object* v_endPos_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; 
v_pos_688_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_pos_688_);
v_endPos_689_ = lean_ctor_get(v_a_687_, 3);
lean_inc(v_endPos_689_);
lean_dec_ref_known(v_a_687_, 4);
lean_inc(v_posOfStr_685_);
v___x_690_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_684_, v_posOfStr_685_, v_str_686_, v_pos_688_);
v___x_691_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_684_, v_posOfStr_685_, v_str_686_, v_endPos_689_);
v___x_692_ = 1;
v___x_693_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_693_, 0, v___x_690_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*2, v___x_692_);
return v___x_693_;
}
case 1:
{
lean_object* v_pos_694_; lean_object* v_endPos_695_; uint8_t v_canonical_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_705_; 
v_pos_694_ = lean_ctor_get(v_a_687_, 0);
v_endPos_695_ = lean_ctor_get(v_a_687_, 1);
v_canonical_696_ = lean_ctor_get_uint8(v_a_687_, sizeof(void*)*2);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_705_ == 0)
{
v___x_698_ = v_a_687_;
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_endPos_695_);
lean_inc(v_pos_694_);
lean_dec(v_a_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_posOfStr_685_);
v___x_700_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_684_, v_posOfStr_685_, v_str_686_, v_pos_694_);
v___x_701_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_684_, v_posOfStr_685_, v_str_686_, v_endPos_695_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_701_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_704_, sizeof(void*)*2, v_canonical_696_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
default: 
{
lean_dec(v_posOfStr_685_);
return v_a_687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_706_, lean_object* v_posOfStr_707_, lean_object* v_str_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_706_, v_posOfStr_707_, v_str_708_, v_a_709_);
lean_dec_ref(v_str_708_);
lean_dec_ref(v_text_706_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_711_, lean_object* v_posOfStr_712_, lean_object* v_str_713_, lean_object* v_a_714_){
_start:
{
switch(lean_obj_tag(v_a_714_))
{
case 0:
{
lean_dec(v_posOfStr_712_);
return v_a_714_;
}
case 1:
{
lean_object* v_info_715_; lean_object* v_kind_716_; lean_object* v_args_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_728_; 
v_info_715_ = lean_ctor_get(v_a_714_, 0);
v_kind_716_ = lean_ctor_get(v_a_714_, 1);
v_args_717_ = lean_ctor_get(v_a_714_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_728_ == 0)
{
v___x_719_ = v_a_714_;
v_isShared_720_ = v_isSharedCheck_728_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_args_717_);
lean_inc(v_kind_716_);
lean_inc(v_info_715_);
lean_dec(v_a_714_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_728_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; size_t v_sz_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
lean_inc(v_posOfStr_712_);
v___x_721_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_711_, v_posOfStr_712_, v_str_713_, v_info_715_);
v_sz_722_ = lean_array_size(v_args_717_);
v___x_723_ = ((size_t)0ULL);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_711_, v_posOfStr_712_, v_str_713_, v_sz_722_, v___x_723_, v_args_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 2, v___x_724_);
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_726_ = v___x_719_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_kind_716_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
case 2:
{
lean_object* v_info_729_; lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_info_729_ = lean_ctor_get(v_a_714_, 0);
v_val_730_ = lean_ctor_get(v_a_714_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_738_ == 0)
{
v___x_732_ = v_a_714_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_inc(v_info_729_);
lean_dec(v_a_714_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_711_, v_posOfStr_712_, v_str_713_, v_info_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_val_730_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
default: 
{
lean_object* v_info_739_; lean_object* v_rawVal_740_; lean_object* v_val_741_; lean_object* v_preresolved_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_info_739_ = lean_ctor_get(v_a_714_, 0);
v_rawVal_740_ = lean_ctor_get(v_a_714_, 1);
v_val_741_ = lean_ctor_get(v_a_714_, 2);
v_preresolved_742_ = lean_ctor_get(v_a_714_, 3);
v_isSharedCheck_750_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v_a_714_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_preresolved_742_);
lean_inc(v_val_741_);
lean_inc(v_rawVal_740_);
lean_inc(v_info_739_);
lean_dec(v_a_714_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_711_, v_posOfStr_712_, v_str_713_, v_info_739_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_rawVal_740_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_val_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_preresolved_742_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_751_, lean_object* v_posOfStr_752_, lean_object* v_str_753_, size_t v_sz_754_, size_t v_i_755_, lean_object* v_bs_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_lt(v_i_755_, v_sz_754_);
if (v___x_757_ == 0)
{
lean_dec(v_posOfStr_752_);
return v_bs_756_;
}
else
{
lean_object* v_v_758_; lean_object* v___x_759_; lean_object* v_bs_x27_760_; lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v_v_758_ = lean_array_uget(v_bs_756_, v_i_755_);
v___x_759_ = lean_unsigned_to_nat(0u);
v_bs_x27_760_ = lean_array_uset(v_bs_756_, v_i_755_, v___x_759_);
lean_inc(v_posOfStr_752_);
v___x_761_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_751_, v_posOfStr_752_, v_str_753_, v_v_758_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_755_, v___x_762_);
v___x_764_ = lean_array_uset(v_bs_x27_760_, v_i_755_, v___x_761_);
v_i_755_ = v___x_763_;
v_bs_756_ = v___x_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_766_, lean_object* v_posOfStr_767_, lean_object* v_str_768_, lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_bs_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_766_, v_posOfStr_767_, v_str_768_, v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
lean_dec_ref(v_str_768_);
lean_dec_ref(v_text_766_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_775_, lean_object* v_posOfStr_776_, lean_object* v_str_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_775_, v_posOfStr_776_, v_str_777_, v_a_778_);
lean_dec_ref(v_str_777_);
lean_dec_ref(v_text_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_780_, lean_object* v_h__1_781_, lean_object* v_h__2_782_, lean_object* v_h__3_783_, lean_object* v_h__4_784_){
_start:
{
switch(lean_obj_tag(v_x_780_))
{
case 0:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_h__3_783_);
lean_dec(v_h__2_782_);
lean_dec(v_h__1_781_);
v___x_785_ = lean_box(0);
v___x_786_ = lean_apply_1(v_h__4_784_, v___x_785_);
return v___x_786_;
}
case 1:
{
lean_object* v_info_787_; lean_object* v_kind_788_; lean_object* v_args_789_; lean_object* v___x_790_; 
lean_dec(v_h__4_784_);
lean_dec(v_h__3_783_);
lean_dec(v_h__2_782_);
v_info_787_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_info_787_);
v_kind_788_ = lean_ctor_get(v_x_780_, 1);
lean_inc(v_kind_788_);
v_args_789_ = lean_ctor_get(v_x_780_, 2);
lean_inc_ref(v_args_789_);
lean_dec_ref_known(v_x_780_, 3);
v___x_790_ = lean_apply_3(v_h__1_781_, v_info_787_, v_kind_788_, v_args_789_);
return v___x_790_;
}
case 2:
{
lean_object* v_info_791_; lean_object* v_val_792_; lean_object* v___x_793_; 
lean_dec(v_h__4_784_);
lean_dec(v_h__2_782_);
lean_dec(v_h__1_781_);
v_info_791_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_info_791_);
v_val_792_ = lean_ctor_get(v_x_780_, 1);
lean_inc_ref(v_val_792_);
lean_dec_ref_known(v_x_780_, 2);
v___x_793_ = lean_apply_2(v_h__3_783_, v_info_791_, v_val_792_);
return v___x_793_;
}
default: 
{
lean_object* v_info_794_; lean_object* v_rawVal_795_; lean_object* v_val_796_; lean_object* v_preresolved_797_; lean_object* v___x_798_; 
lean_dec(v_h__4_784_);
lean_dec(v_h__3_783_);
lean_dec(v_h__1_781_);
v_info_794_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_info_794_);
v_rawVal_795_ = lean_ctor_get(v_x_780_, 1);
lean_inc_ref(v_rawVal_795_);
v_val_796_ = lean_ctor_get(v_x_780_, 2);
lean_inc(v_val_796_);
v_preresolved_797_ = lean_ctor_get(v_x_780_, 3);
lean_inc(v_preresolved_797_);
lean_dec_ref_known(v_x_780_, 4);
v___x_798_ = lean_apply_4(v_h__2_782_, v_info_794_, v_rawVal_795_, v_val_796_, v_preresolved_797_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_799_, lean_object* v_x_800_, lean_object* v_h__1_801_, lean_object* v_h__2_802_, lean_object* v_h__3_803_, lean_object* v_h__4_804_){
_start:
{
switch(lean_obj_tag(v_x_800_))
{
case 0:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_h__3_803_);
lean_dec(v_h__2_802_);
lean_dec(v_h__1_801_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_apply_1(v_h__4_804_, v___x_805_);
return v___x_806_;
}
case 1:
{
lean_object* v_info_807_; lean_object* v_kind_808_; lean_object* v_args_809_; lean_object* v___x_810_; 
lean_dec(v_h__4_804_);
lean_dec(v_h__3_803_);
lean_dec(v_h__2_802_);
v_info_807_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_info_807_);
v_kind_808_ = lean_ctor_get(v_x_800_, 1);
lean_inc(v_kind_808_);
v_args_809_ = lean_ctor_get(v_x_800_, 2);
lean_inc_ref(v_args_809_);
lean_dec_ref_known(v_x_800_, 3);
v___x_810_ = lean_apply_3(v_h__1_801_, v_info_807_, v_kind_808_, v_args_809_);
return v___x_810_;
}
case 2:
{
lean_object* v_info_811_; lean_object* v_val_812_; lean_object* v___x_813_; 
lean_dec(v_h__4_804_);
lean_dec(v_h__2_802_);
lean_dec(v_h__1_801_);
v_info_811_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_info_811_);
v_val_812_ = lean_ctor_get(v_x_800_, 1);
lean_inc_ref(v_val_812_);
lean_dec_ref_known(v_x_800_, 2);
v___x_813_ = lean_apply_2(v_h__3_803_, v_info_811_, v_val_812_);
return v___x_813_;
}
default: 
{
lean_object* v_info_814_; lean_object* v_rawVal_815_; lean_object* v_val_816_; lean_object* v_preresolved_817_; lean_object* v___x_818_; 
lean_dec(v_h__4_804_);
lean_dec(v_h__3_803_);
lean_dec(v_h__1_801_);
v_info_814_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_info_814_);
v_rawVal_815_ = lean_ctor_get(v_x_800_, 1);
lean_inc_ref(v_rawVal_815_);
v_val_816_ = lean_ctor_get(v_x_800_, 2);
lean_inc(v_val_816_);
v_preresolved_817_ = lean_ctor_get(v_x_800_, 3);
lean_inc(v_preresolved_817_);
lean_dec_ref_known(v_x_800_, 4);
v___x_818_ = lean_apply_4(v_h__2_802_, v_info_814_, v_rawVal_815_, v_val_816_, v_preresolved_817_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_819_, lean_object* v_h__1_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_apply_2(v_h__1_820_, v_x_819_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_822_, lean_object* v_P_823_, lean_object* v_motive_824_, lean_object* v_x_825_, lean_object* v_h__1_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_apply_2(v_h__1_826_, v_x_825_, lean_box(0));
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_toPure_828_, lean_object* v_____do__lift_829_){
_start:
{
if (lean_obj_tag(v_____do__lift_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v_____do__lift_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_____do__lift_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v_____do__lift_829_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v_____do__lift_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 1);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_837_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_toPure_828_, lean_box(0), v___x_835_);
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_a_839_ = lean_ctor_get(v_____do__lift_829_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_____do__lift_829_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v_____do__lift_829_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v_____do__lift_829_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_apply_2(v_toPure_828_, lean_box(0), v___x_844_);
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_text_848_, lean_object* v_pos_849_, lean_object* v_str_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_fst_852_ = lean_ctor_get(v_x_851_, 0);
v_snd_853_ = lean_ctor_get(v_x_851_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v_x_851_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_inc(v_fst_852_);
lean_dec(v_x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_848_, v_pos_849_, v_str_850_, v_fst_852_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_snd_853_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_text_862_, lean_object* v_pos_863_, lean_object* v_str_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_text_862_, v_pos_863_, v_str_864_, v_x_865_);
lean_dec_ref(v_str_864_);
lean_dec_ref(v_text_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_env_867_, lean_object* v_p_868_, lean_object* v_ictx_869_, lean_object* v_s_870_, lean_object* v_text_871_, lean_object* v_pos_872_, lean_object* v_str_873_, lean_object* v___f_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_toPure_877_, lean_object* v_____do__lift_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_s_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_box(0);
lean_inc_ref(v_env_867_);
v___x_881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_881_, 0, v_env_867_);
lean_ctor_set(v___x_881_, 1, v_____do__lift_878_);
lean_ctor_set(v___x_881_, 2, v___x_879_);
lean_ctor_set(v___x_881_, 3, v___x_880_);
v___x_882_ = l_Lean_Parser_getTokenTable(v_env_867_);
lean_inc_ref(v_ictx_869_);
v_s_883_ = l_Lean_Parser_ParserFn_run(v_p_868_, v_ictx_869_, v___x_881_, v___x_882_, v_s_870_);
lean_inc_ref(v_s_883_);
v___x_884_ = l_Lean_Parser_ParserState_allErrors(v_s_883_);
v___x_885_ = lean_array_get_size(v___x_884_);
lean_dec_ref(v___x_884_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_nat_dec_eq(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v_stxStack_888_; lean_object* v_lhsPrec_889_; lean_object* v_pos_890_; lean_object* v_cache_891_; lean_object* v_errorMsg_892_; lean_object* v_recoveredErrors_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_toPure_877_);
v_stxStack_888_ = lean_ctor_get(v_s_883_, 0);
v_lhsPrec_889_ = lean_ctor_get(v_s_883_, 1);
v_pos_890_ = lean_ctor_get(v_s_883_, 2);
v_cache_891_ = lean_ctor_get(v_s_883_, 3);
v_errorMsg_892_ = lean_ctor_get(v_s_883_, 4);
v_recoveredErrors_893_ = lean_ctor_get(v_s_883_, 5);
v_isSharedCheck_930_ = !lean_is_exclusive(v_s_883_);
if (v_isSharedCheck_930_ == 0)
{
v___x_895_ = v_s_883_;
v_isShared_896_ = v_isSharedCheck_930_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_recoveredErrors_893_);
lean_inc(v_errorMsg_892_);
lean_inc(v_cache_891_);
lean_inc(v_pos_890_);
lean_inc(v_lhsPrec_889_);
lean_inc(v_stxStack_888_);
lean_dec(v_s_883_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_930_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___y_899_; 
lean_inc(v_pos_872_);
v___x_897_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_871_, v_pos_872_, v_str_873_, v_pos_890_);
if (lean_obj_tag(v_errorMsg_892_) == 0)
{
lean_dec(v_pos_872_);
v___y_899_ = v_errorMsg_892_;
goto v___jp_898_;
}
else
{
lean_object* v_val_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_929_; 
v_val_911_ = lean_ctor_get(v_errorMsg_892_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_errorMsg_892_);
if (v_isSharedCheck_929_ == 0)
{
v___x_913_ = v_errorMsg_892_;
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_val_911_);
lean_dec(v_errorMsg_892_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_unexpectedTk_915_; lean_object* v_unexpected_916_; lean_object* v_expected_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_928_; 
v_unexpectedTk_915_ = lean_ctor_get(v_val_911_, 0);
v_unexpected_916_ = lean_ctor_get(v_val_911_, 1);
v_expected_917_ = lean_ctor_get(v_val_911_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v_val_911_);
if (v_isSharedCheck_928_ == 0)
{
v___x_919_ = v_val_911_;
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_expected_917_);
lean_inc(v_unexpected_916_);
lean_inc(v_unexpectedTk_915_);
lean_dec(v_val_911_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_871_, v_pos_872_, v_str_873_, v_unexpectedTk_915_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_unexpected_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_expected_917_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_923_);
v___x_925_ = v___x_913_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v___y_899_ = v___x_925_;
goto v___jp_898_;
}
}
}
}
}
v___jp_898_:
{
lean_object* v___x_900_; size_t v_sz_901_; size_t v___x_902_; lean_object* v___x_903_; lean_object* v_s_905_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v_sz_901_ = lean_array_size(v_recoveredErrors_893_);
v___x_902_ = ((size_t)0ULL);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_900_, v___f_874_, v_sz_901_, v___x_902_, v_recoveredErrors_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 5, v___x_903_);
lean_ctor_set(v___x_895_, 4, v___y_899_);
lean_ctor_set(v___x_895_, 2, v___x_897_);
v_s_905_ = v___x_895_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_stxStack_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_lhsPrec_889_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_cache_891_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v___y_899_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v___x_903_);
v_s_905_ = v_reuseFailAlloc_910_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_869_, v_s_905_);
v___x_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = l_Lean_MessageData_ofFormat(v___x_907_);
v___x_909_ = l_Lean_throwError___redArg(v_inst_875_, v_inst_876_, v___x_908_);
return v___x_909_;
}
}
}
}
else
{
lean_object* v_stxStack_931_; lean_object* v_pos_932_; uint8_t v___x_933_; 
lean_dec_ref(v___f_874_);
v_stxStack_931_ = lean_ctor_get(v_s_883_, 0);
lean_inc_ref(v_stxStack_931_);
v_pos_932_ = lean_ctor_get(v_s_883_, 2);
lean_inc(v_pos_932_);
v___x_933_ = l_Lean_Parser_InputContext_atEnd(v_ictx_869_, v_pos_932_);
lean_dec(v_pos_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_stxStack_931_);
lean_dec(v_toPure_877_);
lean_dec(v_pos_872_);
v___x_934_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_935_ = l_Lean_Parser_ParserState_mkError(v_s_883_, v___x_934_);
v___x_936_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_869_, v___x_935_);
v___x_937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofFormat(v___x_937_);
v___x_939_ = l_Lean_throwError___redArg(v_inst_875_, v_inst_876_, v___x_938_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_s_883_);
lean_dec_ref(v_inst_876_);
lean_dec_ref(v_inst_875_);
lean_dec_ref(v_ictx_869_);
v___x_940_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_931_);
lean_dec_ref(v_stxStack_931_);
v___x_941_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_871_, v_pos_872_, v_str_873_, v___x_940_);
v___x_942_ = lean_apply_2(v_toPure_877_, lean_box(0), v___x_941_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_env_943_, lean_object* v_p_944_, lean_object* v_ictx_945_, lean_object* v_s_946_, lean_object* v_text_947_, lean_object* v_pos_948_, lean_object* v_str_949_, lean_object* v___f_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_toPure_953_, lean_object* v_____do__lift_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_env_943_, v_p_944_, v_ictx_945_, v_s_946_, v_text_947_, v_pos_948_, v_str_949_, v___f_950_, v_inst_951_, v_inst_952_, v_toPure_953_, v_____do__lift_954_);
lean_dec_ref(v_str_949_);
lean_dec_ref(v_text_947_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_956_, lean_object* v_str_957_, uint8_t v___x_958_, lean_object* v_env_959_, lean_object* v_p_960_, lean_object* v_text_961_, lean_object* v_pos_962_, lean_object* v___f_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_toPure_966_, lean_object* v_toBind_967_, lean_object* v_____do__lift_968_){
_start:
{
lean_object* v_getOptions_969_; lean_object* v___x_970_; lean_object* v_ictx_971_; lean_object* v_s_972_; lean_object* v___f_973_; lean_object* v___x_974_; 
v_getOptions_969_ = lean_ctor_get(v_inst_956_, 0);
lean_inc(v_getOptions_969_);
lean_dec_ref(v_inst_956_);
v___x_970_ = lean_string_utf8_byte_size(v_str_957_);
lean_inc_ref(v_str_957_);
v_ictx_971_ = l_Lean_Parser_mkInputContext___redArg(v_str_957_, v_____do__lift_968_, v___x_958_, v___x_970_);
v_s_972_ = l_Lean_Parser_mkParserState(v_str_957_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_973_, 0, v_env_959_);
lean_closure_set(v___f_973_, 1, v_p_960_);
lean_closure_set(v___f_973_, 2, v_ictx_971_);
lean_closure_set(v___f_973_, 3, v_s_972_);
lean_closure_set(v___f_973_, 4, v_text_961_);
lean_closure_set(v___f_973_, 5, v_pos_962_);
lean_closure_set(v___f_973_, 6, v_str_957_);
lean_closure_set(v___f_973_, 7, v___f_963_);
lean_closure_set(v___f_973_, 8, v_inst_964_);
lean_closure_set(v___f_973_, 9, v_inst_965_);
lean_closure_set(v___f_973_, 10, v_toPure_966_);
v___x_974_ = lean_apply_4(v_toBind_967_, lean_box(0), lean_box(0), v_getOptions_969_, v___f_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_975_, lean_object* v_str_976_, lean_object* v___x_977_, lean_object* v_env_978_, lean_object* v_p_979_, lean_object* v_text_980_, lean_object* v_pos_981_, lean_object* v___f_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_toPure_985_, lean_object* v_toBind_986_, lean_object* v_____do__lift_987_){
_start:
{
uint8_t v___x_1023__boxed_988_; lean_object* v_res_989_; 
v___x_1023__boxed_988_ = lean_unbox(v___x_977_);
v_res_989_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_975_, v_str_976_, v___x_1023__boxed_988_, v_env_978_, v_p_979_, v_text_980_, v_pos_981_, v___f_982_, v_inst_983_, v_inst_984_, v_toPure_985_, v_toBind_986_, v_____do__lift_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v_inst_990_, lean_object* v_strLit_991_, lean_object* v_text_992_, lean_object* v_inst_993_, uint8_t v___x_994_, lean_object* v_env_995_, lean_object* v_p_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_toPure_999_, lean_object* v_toBind_1000_, lean_object* v_pos_1001_){
_start:
{
lean_object* v_getFileName_1002_; lean_object* v_str_1003_; lean_object* v___f_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; 
v_getFileName_1002_ = lean_ctor_get(v_inst_990_, 2);
lean_inc(v_getFileName_1002_);
lean_dec_ref(v_inst_990_);
v_str_1003_ = l_Lean_TSyntax_getString(v_strLit_991_);
lean_inc_ref(v_str_1003_);
lean_inc(v_pos_1001_);
lean_inc_ref(v_text_992_);
v___f_1004_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1004_, 0, v_text_992_);
lean_closure_set(v___f_1004_, 1, v_pos_1001_);
lean_closure_set(v___f_1004_, 2, v_str_1003_);
v___x_1005_ = lean_box(v___x_994_);
lean_inc(v_toBind_1000_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_1006_, 0, v_inst_993_);
lean_closure_set(v___f_1006_, 1, v_str_1003_);
lean_closure_set(v___f_1006_, 2, v___x_1005_);
lean_closure_set(v___f_1006_, 3, v_env_995_);
lean_closure_set(v___f_1006_, 4, v_p_996_);
lean_closure_set(v___f_1006_, 5, v_text_992_);
lean_closure_set(v___f_1006_, 6, v_pos_1001_);
lean_closure_set(v___f_1006_, 7, v___f_1004_);
lean_closure_set(v___f_1006_, 8, v_inst_997_);
lean_closure_set(v___f_1006_, 9, v_inst_998_);
lean_closure_set(v___f_1006_, 10, v_toPure_999_);
lean_closure_set(v___f_1006_, 11, v_toBind_1000_);
v___x_1007_ = lean_apply_4(v_toBind_1000_, lean_box(0), lean_box(0), v_getFileName_1002_, v___f_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object* v_inst_1008_, lean_object* v_strLit_1009_, lean_object* v_text_1010_, lean_object* v_inst_1011_, lean_object* v___x_1012_, lean_object* v_env_1013_, lean_object* v_p_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_toPure_1017_, lean_object* v_toBind_1018_, lean_object* v_pos_1019_){
_start:
{
uint8_t v___x_1048__boxed_1020_; lean_object* v_res_1021_; 
v___x_1048__boxed_1020_ = lean_unbox(v___x_1012_);
v_res_1021_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_1008_, v_strLit_1009_, v_text_1010_, v_inst_1011_, v___x_1048__boxed_1020_, v_env_1013_, v_p_1014_, v_inst_1015_, v_inst_1016_, v_toPure_1017_, v_toBind_1018_, v_pos_1019_);
lean_dec(v_strLit_1009_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_1022_, lean_object* v_pos_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_apply_1(v___f_1022_, v_pos_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_text_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_strLit_1031_, lean_object* v_toBind_1032_, lean_object* v___f_1033_, lean_object* v_toPure_1034_, lean_object* v___f_1035_, lean_object* v_____r_1036_, lean_object* v_pos_1037_){
_start:
{
lean_object* v_source_1038_; uint32_t v___x_1039_; uint32_t v___x_1040_; uint8_t v___x_1041_; 
v_source_1038_ = lean_ctor_get(v_text_1028_, 0);
v___x_1039_ = lean_string_utf8_get(v_source_1038_, v_pos_1037_);
v___x_1040_ = 34;
v___x_1041_ = lean_uint32_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___f_1035_);
lean_dec(v_toPure_1034_);
v___x_1042_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1);
v___x_1043_ = l_Lean_throwErrorAt___redArg(v_inst_1029_, v_inst_1030_, v_strLit_1031_, v___x_1042_);
v___x_1044_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1043_, v___f_1033_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___f_1033_);
lean_dec(v_strLit_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
v___x_1045_ = lean_string_utf8_next(v_source_1038_, v_pos_1037_);
v___x_1046_ = lean_apply_2(v_toPure_1034_, lean_box(0), v___x_1045_);
v___x_1047_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1046_, v___f_1035_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_text_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_strLit_1051_, lean_object* v_toBind_1052_, lean_object* v___f_1053_, lean_object* v_toPure_1054_, lean_object* v___f_1055_, lean_object* v_____r_1056_, lean_object* v_pos_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_text_1048_, v_inst_1049_, v_inst_1050_, v_strLit_1051_, v_toBind_1052_, v___f_1053_, v_toPure_1054_, v___f_1055_, v_____r_1056_, v_pos_1057_);
lean_dec(v_pos_1057_);
lean_dec_ref(v_text_1048_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v___f_1059_, lean_object* v_____s_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_apply_2(v___f_1059_, v___x_1061_, v_____s_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_1063_, lean_object* v_toPure_1064_, lean_object* v_toBind_1065_, lean_object* v___f_1066_, lean_object* v_b_1067_){
_start:
{
uint32_t v___x_1068_; uint32_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_string_utf8_get(v_source_1063_, v_b_1067_);
v___x_1069_ = 35;
v___x_1070_ = lean_uint32_dec_eq(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_b_1067_);
v___x_1072_ = lean_apply_2(v_toPure_1064_, lean_box(0), v___x_1071_);
v___x_1073_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1072_, v___f_1066_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = lean_string_utf8_next(v_source_1063_, v_b_1067_);
lean_dec(v_b_1067_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
v___x_1076_ = lean_apply_2(v_toPure_1064_, lean_box(0), v___x_1075_);
v___x_1077_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1076_, v___f_1066_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_1078_, lean_object* v_toPure_1079_, lean_object* v_toBind_1080_, lean_object* v___f_1081_, lean_object* v_b_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_1078_, v_toPure_1079_, v_toBind_1080_, v___f_1081_, v_b_1082_);
lean_dec_ref(v_source_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_1084_, lean_object* v___f_1085_, lean_object* v_toPure_1086_, lean_object* v_toBind_1087_, lean_object* v___f_1088_, lean_object* v_inst_1089_, lean_object* v___f_1090_, lean_object* v_____x_1091_){
_start:
{
lean_object* v_start_1092_; lean_object* v_source_1093_; uint32_t v___x_1094_; uint32_t v___x_1095_; uint8_t v___x_1096_; 
v_start_1092_ = lean_ctor_get(v_____x_1091_, 0);
lean_inc(v_start_1092_);
lean_dec_ref(v_____x_1091_);
v_source_1093_ = lean_ctor_get(v_text_1084_, 0);
lean_inc_ref(v_source_1093_);
lean_dec_ref(v_text_1084_);
v___x_1094_ = lean_string_utf8_get(v_source_1093_, v_start_1092_);
v___x_1095_ = 114;
v___x_1096_ = lean_uint32_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_source_1093_);
lean_dec(v___f_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec(v___f_1088_);
lean_dec(v_toBind_1087_);
lean_dec(v_toPure_1086_);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_apply_2(v___f_1085_, v___x_1097_, v_start_1092_);
return v___x_1098_;
}
else
{
lean_object* v___f_1099_; lean_object* v_pos_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v___f_1085_);
lean_inc(v_toBind_1087_);
lean_inc_ref(v_source_1093_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_1099_, 0, v_source_1093_);
lean_closure_set(v___f_1099_, 1, v_toPure_1086_);
lean_closure_set(v___f_1099_, 2, v_toBind_1087_);
lean_closure_set(v___f_1099_, 3, v___f_1088_);
v_pos_1100_ = lean_string_utf8_next(v_source_1093_, v_start_1092_);
lean_dec(v_start_1092_);
lean_dec_ref(v_source_1093_);
v___x_1101_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_1089_, v___f_1099_, v_pos_1100_);
v___x_1102_ = lean_apply_4(v_toBind_1087_, lean_box(0), lean_box(0), v___x_1101_, v___f_1090_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_1103_, lean_object* v_strLit_1104_, lean_object* v_text_1105_, lean_object* v_inst_1106_, uint8_t v___x_1107_, lean_object* v_p_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_toPure_1111_, lean_object* v_toBind_1112_, lean_object* v___f_1113_, lean_object* v_env_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1115_ = lean_box(v___x_1107_);
lean_inc_n(v_toBind_1112_, 3);
lean_inc_n(v_toPure_1111_, 2);
lean_inc_ref(v_inst_1110_);
lean_inc_ref_n(v_inst_1109_, 3);
lean_inc_ref_n(v_text_1105_, 2);
lean_inc_n(v_strLit_1104_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1116_, 0, v_inst_1103_);
lean_closure_set(v___f_1116_, 1, v_strLit_1104_);
lean_closure_set(v___f_1116_, 2, v_text_1105_);
lean_closure_set(v___f_1116_, 3, v_inst_1106_);
lean_closure_set(v___f_1116_, 4, v___x_1115_);
lean_closure_set(v___f_1116_, 5, v_env_1114_);
lean_closure_set(v___f_1116_, 6, v_p_1108_);
lean_closure_set(v___f_1116_, 7, v_inst_1109_);
lean_closure_set(v___f_1116_, 8, v_inst_1110_);
lean_closure_set(v___f_1116_, 9, v_toPure_1111_);
lean_closure_set(v___f_1116_, 10, v_toBind_1112_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1117_, 0, v___f_1116_);
lean_inc_ref(v___f_1117_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_1118_, 0, v_text_1105_);
lean_closure_set(v___f_1118_, 1, v_inst_1109_);
lean_closure_set(v___f_1118_, 2, v_inst_1110_);
lean_closure_set(v___f_1118_, 3, v_strLit_1104_);
lean_closure_set(v___f_1118_, 4, v_toBind_1112_);
lean_closure_set(v___f_1118_, 5, v___f_1117_);
lean_closure_set(v___f_1118_, 6, v_toPure_1111_);
lean_closure_set(v___f_1118_, 7, v___f_1117_);
lean_inc_ref(v___f_1118_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1119_, 0, v___f_1118_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 8, 7);
lean_closure_set(v___f_1120_, 0, v_text_1105_);
lean_closure_set(v___f_1120_, 1, v___f_1118_);
lean_closure_set(v___f_1120_, 2, v_toPure_1111_);
lean_closure_set(v___f_1120_, 3, v_toBind_1112_);
lean_closure_set(v___f_1120_, 4, v___f_1113_);
lean_closure_set(v___f_1120_, 5, v_inst_1109_);
lean_closure_set(v___f_1120_, 6, v___f_1119_);
v___x_1121_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_1109_, v_strLit_1104_);
lean_dec(v_strLit_1104_);
v___x_1122_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v___x_1121_, v___f_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_1123_, lean_object* v_strLit_1124_, lean_object* v_text_1125_, lean_object* v_inst_1126_, lean_object* v___x_1127_, lean_object* v_p_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_toPure_1131_, lean_object* v_toBind_1132_, lean_object* v___f_1133_, lean_object* v_env_1134_){
_start:
{
uint8_t v___x_1176__boxed_1135_; lean_object* v_res_1136_; 
v___x_1176__boxed_1135_ = lean_unbox(v___x_1127_);
v_res_1136_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_1123_, v_strLit_1124_, v_text_1125_, v_inst_1126_, v___x_1176__boxed_1135_, v_p_1128_, v_inst_1129_, v_inst_1130_, v_toPure_1131_, v_toBind_1132_, v___f_1133_, v_env_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_strLit_1139_, lean_object* v_inst_1140_, uint8_t v___x_1141_, lean_object* v_p_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_toPure_1145_, lean_object* v_toBind_1146_, lean_object* v___f_1147_, lean_object* v_text_1148_){
_start:
{
lean_object* v_getEnv_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; 
v_getEnv_1149_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc(v_getEnv_1149_);
lean_dec_ref(v_inst_1137_);
v___x_1150_ = lean_box(v___x_1141_);
lean_inc(v_toBind_1146_);
v___f_1151_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_1151_, 0, v_inst_1138_);
lean_closure_set(v___f_1151_, 1, v_strLit_1139_);
lean_closure_set(v___f_1151_, 2, v_text_1148_);
lean_closure_set(v___f_1151_, 3, v_inst_1140_);
lean_closure_set(v___f_1151_, 4, v___x_1150_);
lean_closure_set(v___f_1151_, 5, v_p_1142_);
lean_closure_set(v___f_1151_, 6, v_inst_1143_);
lean_closure_set(v___f_1151_, 7, v_inst_1144_);
lean_closure_set(v___f_1151_, 8, v_toPure_1145_);
lean_closure_set(v___f_1151_, 9, v_toBind_1146_);
lean_closure_set(v___f_1151_, 10, v___f_1147_);
v___x_1152_ = lean_apply_4(v_toBind_1146_, lean_box(0), lean_box(0), v_getEnv_1149_, v___f_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_strLit_1155_, lean_object* v_inst_1156_, lean_object* v___x_1157_, lean_object* v_p_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_toPure_1161_, lean_object* v_toBind_1162_, lean_object* v___f_1163_, lean_object* v_text_1164_){
_start:
{
uint8_t v___x_1211__boxed_1165_; lean_object* v_res_1166_; 
v___x_1211__boxed_1165_ = lean_unbox(v___x_1157_);
v_res_1166_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_1153_, v_inst_1154_, v_strLit_1155_, v_inst_1156_, v___x_1211__boxed_1165_, v_p_1158_, v_inst_1159_, v_inst_1160_, v_toPure_1161_, v_toBind_1162_, v___f_1163_, v_text_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_p_1173_, lean_object* v_strLit_1174_){
_start:
{
uint8_t v___x_1175_; uint8_t v___y_1177_; lean_object* v___x_1187_; 
v___x_1175_ = 1;
v___x_1187_ = l_Lean_Syntax_getPos_x3f(v_strLit_1174_, v___x_1175_);
if (lean_obj_tag(v___x_1187_) == 0)
{
v___y_1177_ = v___x_1175_;
goto v___jp_1176_;
}
else
{
uint8_t v___x_1188_; 
lean_dec_ref_known(v___x_1187_, 1);
v___x_1188_ = 0;
v___y_1177_ = v___x_1188_;
goto v___jp_1176_;
}
v___jp_1176_:
{
if (v___y_1177_ == 0)
{
lean_object* v_toApplicative_1178_; lean_object* v_toBind_1179_; lean_object* v_toPure_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v_toApplicative_1178_ = lean_ctor_get(v_inst_1167_, 0);
v_toBind_1179_ = lean_ctor_get(v_inst_1167_, 1);
lean_inc_n(v_toBind_1179_, 2);
v_toPure_1180_ = lean_ctor_get(v_toApplicative_1178_, 1);
lean_inc_n(v_toPure_1180_, 2);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1181_, 0, v_toPure_1180_);
v___x_1182_ = lean_box(v___x_1175_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 12, 11);
lean_closure_set(v___f_1183_, 0, v_inst_1169_);
lean_closure_set(v___f_1183_, 1, v_inst_1171_);
lean_closure_set(v___f_1183_, 2, v_strLit_1174_);
lean_closure_set(v___f_1183_, 3, v_inst_1172_);
lean_closure_set(v___f_1183_, 4, v___x_1182_);
lean_closure_set(v___f_1183_, 5, v_p_1173_);
lean_closure_set(v___f_1183_, 6, v_inst_1167_);
lean_closure_set(v___f_1183_, 7, v_inst_1170_);
lean_closure_set(v___f_1183_, 8, v_toPure_1180_);
lean_closure_set(v___f_1183_, 9, v_toBind_1179_);
lean_closure_set(v___f_1183_, 10, v___f_1181_);
v___x_1184_ = lean_apply_4(v_toBind_1179_, lean_box(0), lean_box(0), v_inst_1168_, v___f_1183_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_inst_1168_);
v___x_1185_ = l_Lean_TSyntax_getString(v_strLit_1174_);
lean_dec(v_strLit_1174_);
v___x_1186_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_1167_, v_inst_1169_, v_inst_1170_, v_inst_1171_, v_inst_1172_, v_p_1173_, v___x_1185_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_p_1196_, lean_object* v_strLit_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_inst_1195_, v_p_1196_, v_strLit_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object* v_s_1199_, lean_object* v_toPure_1200_, uint8_t v_err_1201_){
_start:
{
lean_object* v_stxStack_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_stxStack_1202_ = lean_ctor_get(v_s_1199_, 0);
v___x_1203_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1202_);
v___x_1204_ = lean_box(v_err_1201_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_apply_2(v_toPure_1200_, lean_box(0), v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object* v_s_1207_, lean_object* v_toPure_1208_, lean_object* v_err_1209_){
_start:
{
uint8_t v_err_boxed_1210_; lean_object* v_res_1211_; 
v_err_boxed_1210_ = lean_unbox(v_err_1209_);
v_res_1211_ = l_Lean_Doc_parseContent_x27___redArg___lam__0(v_s_1207_, v_toPure_1208_, v_err_boxed_1210_);
lean_dec_ref(v_s_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object* v___f_1212_, uint8_t v_err_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_box(v_err_1213_);
v___x_1215_ = lean_apply_1(v___f_1212_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object* v___f_1216_, lean_object* v_err_1217_){
_start:
{
uint8_t v_err_boxed_1218_; lean_object* v_res_1219_; 
v_err_boxed_1218_ = lean_unbox(v_err_1217_);
v_res_1219_ = l_Lean_Doc_parseContent_x27___redArg___lam__1(v___f_1216_, v_err_boxed_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object* v_toPure_1220_, uint8_t v___x_1221_, lean_object* v_toBind_1222_, lean_object* v___f_1223_, lean_object* v_____r_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box(v___x_1221_);
v___x_1226_ = lean_apply_2(v_toPure_1220_, lean_box(0), v___x_1225_);
v___x_1227_ = lean_apply_4(v_toBind_1222_, lean_box(0), lean_box(0), v___x_1226_, v___f_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object* v_toPure_1228_, lean_object* v___x_1229_, lean_object* v_toBind_1230_, lean_object* v___f_1231_, lean_object* v_____r_1232_){
_start:
{
uint8_t v___x_798__boxed_1233_; lean_object* v_res_1234_; 
v___x_798__boxed_1233_ = lean_unbox(v___x_1229_);
v_res_1234_ = l_Lean_Doc_parseContent_x27___redArg___lam__2(v_toPure_1228_, v___x_798__boxed_1233_, v_toBind_1230_, v___f_1231_, v_____r_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object* v_env_1235_, lean_object* v_p_1236_, lean_object* v_ictx_1237_, lean_object* v_s_1238_, lean_object* v_toPure_1239_, uint8_t v___x_1240_, lean_object* v_toBind_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, uint8_t v___y_1246_, lean_object* v_____do__lift_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_s_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_box(0);
lean_inc_ref(v_env_1235_);
v___x_1250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1250_, 0, v_env_1235_);
lean_ctor_set(v___x_1250_, 1, v_____do__lift_1247_);
lean_ctor_set(v___x_1250_, 2, v___x_1248_);
lean_ctor_set(v___x_1250_, 3, v___x_1249_);
v___x_1251_ = l_Lean_Parser_getTokenTable(v_env_1235_);
lean_inc_ref(v_ictx_1237_);
v_s_1252_ = l_Lean_Parser_ParserFn_run(v_p_1236_, v_ictx_1237_, v___x_1250_, v___x_1251_, v_s_1238_);
lean_inc(v_toPure_1239_);
lean_inc_ref_n(v_s_1252_, 2);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1253_, 0, v_s_1252_);
lean_closure_set(v___f_1253_, 1, v_toPure_1239_);
v___x_1254_ = l_Lean_Parser_ParserState_allErrors(v_s_1252_);
v___x_1255_ = lean_array_get_size(v___x_1254_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_nat_dec_eq(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1258_, 0, v___f_1253_);
v___x_1259_ = lean_box(v___x_1240_);
lean_inc(v_toBind_1241_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1260_, 0, v_toPure_1239_);
lean_closure_set(v___f_1260_, 1, v___x_1259_);
lean_closure_set(v___f_1260_, 2, v_toBind_1241_);
lean_closure_set(v___f_1260_, 3, v___f_1258_);
v___x_1261_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1237_, v_s_1252_);
v___x_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
v___x_1263_ = l_Lean_MessageData_ofFormat(v___x_1262_);
v___x_1264_ = l_Lean_logError___redArg(v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v___x_1263_);
v___x_1265_ = lean_apply_4(v_toBind_1241_, lean_box(0), lean_box(0), v___x_1264_, v___f_1260_);
return v___x_1265_;
}
else
{
lean_object* v_pos_1266_; uint8_t v___x_1267_; 
v_pos_1266_ = lean_ctor_get(v_s_1252_, 2);
lean_inc(v_pos_1266_);
v___x_1267_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1237_, v_pos_1266_);
lean_dec(v_pos_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___f_1268_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1268_, 0, v___f_1253_);
v___x_1269_ = lean_box(v___x_1240_);
lean_inc(v_toBind_1241_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1270_, 0, v_toPure_1239_);
lean_closure_set(v___f_1270_, 1, v___x_1269_);
lean_closure_set(v___f_1270_, 2, v_toBind_1241_);
lean_closure_set(v___f_1270_, 3, v___f_1268_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1272_ = l_Lean_Parser_ParserState_mkError(v_s_1252_, v___x_1271_);
v___x_1273_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1237_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___x_1275_ = l_Lean_MessageData_ofFormat(v___x_1274_);
v___x_1276_ = l_Lean_logError___redArg(v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v___x_1275_);
v___x_1277_ = lean_apply_4(v_toBind_1241_, lean_box(0), lean_box(0), v___x_1276_, v___f_1270_);
return v___x_1277_;
}
else
{
lean_object* v___f_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref(v_s_1252_);
lean_dec_ref(v_inst_1245_);
lean_dec(v_inst_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_ictx_1237_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1278_, 0, v___f_1253_);
v___x_1279_ = lean_box(v___y_1246_);
v___x_1280_ = lean_apply_2(v_toPure_1239_, lean_box(0), v___x_1279_);
v___x_1281_ = lean_apply_4(v_toBind_1241_, lean_box(0), lean_box(0), v___x_1280_, v___f_1278_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object* v_env_1282_, lean_object* v_p_1283_, lean_object* v_ictx_1284_, lean_object* v_s_1285_, lean_object* v_toPure_1286_, lean_object* v___x_1287_, lean_object* v_toBind_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v___y_1293_, lean_object* v_____do__lift_1294_){
_start:
{
uint8_t v___x_814__boxed_1295_; uint8_t v___y_819__boxed_1296_; lean_object* v_res_1297_; 
v___x_814__boxed_1295_ = lean_unbox(v___x_1287_);
v___y_819__boxed_1296_ = lean_unbox(v___y_1293_);
v_res_1297_ = l_Lean_Doc_parseContent_x27___redArg___lam__6(v_env_1282_, v_p_1283_, v_ictx_1284_, v_s_1285_, v_toPure_1286_, v___x_814__boxed_1295_, v_toBind_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v___y_819__boxed_1296_, v_____do__lift_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object* v_source_1298_, uint8_t v___x_1299_, lean_object* v___y_1300_, lean_object* v_inst_1301_, lean_object* v_env_1302_, lean_object* v_p_1303_, lean_object* v_toPure_1304_, lean_object* v_toBind_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, uint8_t v___y_1309_, lean_object* v_tok_1310_, lean_object* v___x_1311_, lean_object* v_____do__lift_1312_){
_start:
{
lean_object* v_ictx_1313_; lean_object* v___x_1314_; lean_object* v___y_1316_; lean_object* v___x_1323_; 
lean_inc_ref(v_source_1298_);
v_ictx_1313_ = l_Lean_Parser_mkInputContext___redArg(v_source_1298_, v_____do__lift_1312_, v___x_1299_, v___y_1300_);
v___x_1314_ = l_Lean_Parser_mkParserState(v_source_1298_);
lean_dec_ref(v_source_1298_);
v___x_1323_ = l_Lean_Syntax_getPos_x3f(v_tok_1310_, v___x_1299_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1325_ = l_panic___redArg(v___x_1311_, v___x_1324_);
v___y_1316_ = v___x_1325_;
goto v___jp_1315_;
}
else
{
lean_object* v_val_1326_; 
v_val_1326_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v___x_1323_, 1);
v___y_1316_ = v_val_1326_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v_getOptions_1317_; lean_object* v_s_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; 
v_getOptions_1317_ = lean_ctor_get(v_inst_1301_, 0);
lean_inc(v_getOptions_1317_);
v_s_1318_ = l_Lean_Parser_ParserState_setPos(v___x_1314_, v___y_1316_);
v___x_1319_ = lean_box(v___x_1299_);
v___x_1320_ = lean_box(v___y_1309_);
lean_inc(v_toBind_1305_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1321_, 0, v_env_1302_);
lean_closure_set(v___f_1321_, 1, v_p_1303_);
lean_closure_set(v___f_1321_, 2, v_ictx_1313_);
lean_closure_set(v___f_1321_, 3, v_s_1318_);
lean_closure_set(v___f_1321_, 4, v_toPure_1304_);
lean_closure_set(v___f_1321_, 5, v___x_1319_);
lean_closure_set(v___f_1321_, 6, v_toBind_1305_);
lean_closure_set(v___f_1321_, 7, v_inst_1306_);
lean_closure_set(v___f_1321_, 8, v_inst_1307_);
lean_closure_set(v___f_1321_, 9, v_inst_1308_);
lean_closure_set(v___f_1321_, 10, v_inst_1301_);
lean_closure_set(v___f_1321_, 11, v___x_1320_);
v___x_1322_ = lean_apply_4(v_toBind_1305_, lean_box(0), lean_box(0), v_getOptions_1317_, v___f_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object* v_source_1327_, lean_object* v___x_1328_, lean_object* v___y_1329_, lean_object* v_inst_1330_, lean_object* v_env_1331_, lean_object* v_p_1332_, lean_object* v_toPure_1333_, lean_object* v_toBind_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v___y_1338_, lean_object* v_tok_1339_, lean_object* v___x_1340_, lean_object* v_____do__lift_1341_){
_start:
{
uint8_t v___x_908__boxed_1342_; uint8_t v___y_914__boxed_1343_; lean_object* v_res_1344_; 
v___x_908__boxed_1342_ = lean_unbox(v___x_1328_);
v___y_914__boxed_1343_ = lean_unbox(v___y_1338_);
v_res_1344_ = l_Lean_Doc_parseContent_x27___redArg___lam__3(v_source_1327_, v___x_908__boxed_1342_, v___y_1329_, v_inst_1330_, v_env_1331_, v_p_1332_, v_toPure_1333_, v_toBind_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v___y_914__boxed_1343_, v_tok_1339_, v___x_1340_, v_____do__lift_1341_);
lean_dec(v___x_1340_);
lean_dec(v_tok_1339_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object* v_text_1345_, lean_object* v_inst_1346_, uint8_t v___x_1347_, lean_object* v_inst_1348_, lean_object* v_p_1349_, lean_object* v_toPure_1350_, lean_object* v_toBind_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, uint8_t v___y_1354_, lean_object* v_tok_1355_, lean_object* v___x_1356_, lean_object* v_env_1357_){
_start:
{
lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1367_; lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Syntax_getTailPos_x3f(v_tok_1355_, v___x_1347_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1373_ = l_panic___redArg(v___x_1356_, v___x_1372_);
v___y_1367_ = v___x_1373_;
goto v___jp_1366_;
}
else
{
lean_object* v_val_1374_; 
v_val_1374_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1371_, 1);
v___y_1367_ = v_val_1374_;
goto v___jp_1366_;
}
v___jp_1358_:
{
lean_object* v_getFileName_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; 
v_getFileName_1361_ = lean_ctor_get(v_inst_1346_, 2);
lean_inc(v_getFileName_1361_);
v___x_1362_ = lean_box(v___x_1347_);
v___x_1363_ = lean_box(v___y_1354_);
lean_inc(v_toBind_1351_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1364_, 0, v___y_1359_);
lean_closure_set(v___f_1364_, 1, v___x_1362_);
lean_closure_set(v___f_1364_, 2, v___y_1360_);
lean_closure_set(v___f_1364_, 3, v_inst_1348_);
lean_closure_set(v___f_1364_, 4, v_env_1357_);
lean_closure_set(v___f_1364_, 5, v_p_1349_);
lean_closure_set(v___f_1364_, 6, v_toPure_1350_);
lean_closure_set(v___f_1364_, 7, v_toBind_1351_);
lean_closure_set(v___f_1364_, 8, v_inst_1352_);
lean_closure_set(v___f_1364_, 9, v_inst_1346_);
lean_closure_set(v___f_1364_, 10, v_inst_1353_);
lean_closure_set(v___f_1364_, 11, v___x_1363_);
lean_closure_set(v___f_1364_, 12, v_tok_1355_);
lean_closure_set(v___f_1364_, 13, v___x_1356_);
v___x_1365_ = lean_apply_4(v_toBind_1351_, lean_box(0), lean_box(0), v_getFileName_1361_, v___f_1364_);
return v___x_1365_;
}
v___jp_1366_:
{
lean_object* v_source_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_source_1368_ = lean_ctor_get(v_text_1345_, 0);
lean_inc_ref(v_source_1368_);
lean_dec_ref(v_text_1345_);
v___x_1369_ = lean_string_utf8_byte_size(v_source_1368_);
v___x_1370_ = lean_nat_dec_le(v___y_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v___y_1367_);
v___y_1359_ = v_source_1368_;
v___y_1360_ = v___x_1369_;
goto v___jp_1358_;
}
else
{
v___y_1359_ = v_source_1368_;
v___y_1360_ = v___y_1367_;
goto v___jp_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object* v_text_1375_, lean_object* v_inst_1376_, lean_object* v___x_1377_, lean_object* v_inst_1378_, lean_object* v_p_1379_, lean_object* v_toPure_1380_, lean_object* v_toBind_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v___y_1384_, lean_object* v_tok_1385_, lean_object* v___x_1386_, lean_object* v_env_1387_){
_start:
{
uint8_t v___x_973__boxed_1388_; uint8_t v___y_977__boxed_1389_; lean_object* v_res_1390_; 
v___x_973__boxed_1388_ = lean_unbox(v___x_1377_);
v___y_977__boxed_1389_ = lean_unbox(v___y_1384_);
v_res_1390_ = l_Lean_Doc_parseContent_x27___redArg___lam__4(v_text_1375_, v_inst_1376_, v___x_973__boxed_1388_, v_inst_1378_, v_p_1379_, v_toPure_1380_, v_toBind_1381_, v_inst_1382_, v_inst_1383_, v___y_977__boxed_1389_, v_tok_1385_, v___x_1386_, v_env_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object* v_inst_1391_, lean_object* v_inst_1392_, uint8_t v___x_1393_, lean_object* v_inst_1394_, lean_object* v_p_1395_, lean_object* v_toPure_1396_, lean_object* v_toBind_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, uint8_t v___y_1400_, lean_object* v_tok_1401_, lean_object* v___x_1402_, lean_object* v_text_1403_){
_start:
{
lean_object* v_getEnv_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; 
v_getEnv_1404_ = lean_ctor_get(v_inst_1391_, 0);
lean_inc(v_getEnv_1404_);
lean_dec_ref(v_inst_1391_);
v___x_1405_ = lean_box(v___x_1393_);
v___x_1406_ = lean_box(v___y_1400_);
lean_inc(v_toBind_1397_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed), 13, 12);
lean_closure_set(v___f_1407_, 0, v_text_1403_);
lean_closure_set(v___f_1407_, 1, v_inst_1392_);
lean_closure_set(v___f_1407_, 2, v___x_1405_);
lean_closure_set(v___f_1407_, 3, v_inst_1394_);
lean_closure_set(v___f_1407_, 4, v_p_1395_);
lean_closure_set(v___f_1407_, 5, v_toPure_1396_);
lean_closure_set(v___f_1407_, 6, v_toBind_1397_);
lean_closure_set(v___f_1407_, 7, v_inst_1398_);
lean_closure_set(v___f_1407_, 8, v_inst_1399_);
lean_closure_set(v___f_1407_, 9, v___x_1406_);
lean_closure_set(v___f_1407_, 10, v_tok_1401_);
lean_closure_set(v___f_1407_, 11, v___x_1402_);
v___x_1408_ = lean_apply_4(v_toBind_1397_, lean_box(0), lean_box(0), v_getEnv_1404_, v___f_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v___x_1411_, lean_object* v_inst_1412_, lean_object* v_p_1413_, lean_object* v_toPure_1414_, lean_object* v_toBind_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v___y_1418_, lean_object* v_tok_1419_, lean_object* v___x_1420_, lean_object* v_text_1421_){
_start:
{
uint8_t v___x_1030__boxed_1422_; uint8_t v___y_1034__boxed_1423_; lean_object* v_res_1424_; 
v___x_1030__boxed_1422_ = lean_unbox(v___x_1411_);
v___y_1034__boxed_1423_ = lean_unbox(v___y_1418_);
v_res_1424_ = l_Lean_Doc_parseContent_x27___redArg___lam__5(v_inst_1409_, v_inst_1410_, v___x_1030__boxed_1422_, v_inst_1412_, v_p_1413_, v_toPure_1414_, v_toBind_1415_, v_inst_1416_, v_inst_1417_, v___y_1034__boxed_1423_, v_tok_1419_, v___x_1420_, v_text_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object* v_st_1425_, lean_object* v_toPure_1426_, uint8_t v_err_1427_){
_start:
{
lean_object* v_stxStack_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_stxStack_1428_ = lean_ctor_get(v_st_1425_, 0);
v___x_1429_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1428_);
v___x_1430_ = lean_box(v_err_1427_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_apply_2(v_toPure_1426_, lean_box(0), v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object* v_st_1433_, lean_object* v_toPure_1434_, lean_object* v_err_1435_){
_start:
{
uint8_t v_err_boxed_1436_; lean_object* v_res_1437_; 
v_err_boxed_1436_ = lean_unbox(v_err_1435_);
v_res_1437_ = l_Lean_Doc_parseContent_x27___redArg___lam__7(v_st_1433_, v_toPure_1434_, v_err_boxed_1436_);
lean_dec_ref(v_st_1433_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object* v_env_1438_, lean_object* v_contents_1439_, lean_object* v_p_1440_, lean_object* v_ictx_1441_, lean_object* v_toPure_1442_, uint8_t v___x_1443_, lean_object* v_toBind_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_____do__lift_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_st_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_box(0);
lean_inc_ref(v_env_1438_);
v___x_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1452_, 0, v_env_1438_);
lean_ctor_set(v___x_1452_, 1, v_____do__lift_1449_);
lean_ctor_set(v___x_1452_, 2, v___x_1450_);
lean_ctor_set(v___x_1452_, 3, v___x_1451_);
v___x_1453_ = l_Lean_Parser_getTokenTable(v_env_1438_);
v___x_1454_ = l_Lean_Parser_mkParserState(v_contents_1439_);
lean_inc_ref(v_ictx_1441_);
v_st_1455_ = l_Lean_Parser_ParserFn_run(v_p_1440_, v_ictx_1441_, v___x_1452_, v___x_1453_, v___x_1454_);
lean_inc(v_toPure_1442_);
lean_inc_ref_n(v_st_1455_, 2);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1456_, 0, v_st_1455_);
lean_closure_set(v___f_1456_, 1, v_toPure_1442_);
v___x_1457_ = l_Lean_Parser_ParserState_allErrors(v_st_1455_);
v___x_1458_ = lean_array_get_size(v___x_1457_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_nat_dec_eq(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1461_, 0, v___f_1456_);
v___x_1462_ = lean_box(v___x_1443_);
lean_inc(v_toBind_1444_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1463_, 0, v_toPure_1442_);
lean_closure_set(v___f_1463_, 1, v___x_1462_);
lean_closure_set(v___f_1463_, 2, v_toBind_1444_);
lean_closure_set(v___f_1463_, 3, v___f_1461_);
v___x_1464_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1441_, v_st_1455_);
v___x_1465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
v___x_1466_ = l_Lean_MessageData_ofFormat(v___x_1465_);
v___x_1467_ = l_Lean_logError___redArg(v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_, v___x_1466_);
v___x_1468_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v___x_1467_, v___f_1463_);
return v___x_1468_;
}
else
{
lean_object* v_pos_1469_; uint8_t v___x_1470_; 
v_pos_1469_ = lean_ctor_get(v_st_1455_, 2);
lean_inc(v_pos_1469_);
v___x_1470_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1441_, v_pos_1469_);
lean_dec(v_pos_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1471_, 0, v___f_1456_);
v___x_1472_ = lean_box(v___x_1443_);
lean_inc(v_toBind_1444_);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1473_, 0, v_toPure_1442_);
lean_closure_set(v___f_1473_, 1, v___x_1472_);
lean_closure_set(v___f_1473_, 2, v_toBind_1444_);
lean_closure_set(v___f_1473_, 3, v___f_1471_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1475_ = l_Lean_Parser_ParserState_mkError(v_st_1455_, v___x_1474_);
v___x_1476_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1441_, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
v___x_1478_ = l_Lean_MessageData_ofFormat(v___x_1477_);
v___x_1479_ = l_Lean_logError___redArg(v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_, v___x_1478_);
v___x_1480_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v___x_1479_, v___f_1473_);
return v___x_1480_;
}
else
{
lean_object* v___f_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_st_1455_);
lean_dec_ref(v_inst_1448_);
lean_dec(v_inst_1447_);
lean_dec_ref(v_inst_1446_);
lean_dec_ref(v_inst_1445_);
lean_dec_ref(v_ictx_1441_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1481_, 0, v___f_1456_);
v___x_1482_ = 0;
v___x_1483_ = lean_box(v___x_1482_);
v___x_1484_ = lean_apply_2(v_toPure_1442_, lean_box(0), v___x_1483_);
v___x_1485_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v___x_1484_, v___f_1481_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object* v_env_1486_, lean_object* v_contents_1487_, lean_object* v_p_1488_, lean_object* v_ictx_1489_, lean_object* v_toPure_1490_, lean_object* v___x_1491_, lean_object* v_toBind_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_____do__lift_1497_){
_start:
{
uint8_t v___x_1069__boxed_1498_; lean_object* v_res_1499_; 
v___x_1069__boxed_1498_ = lean_unbox(v___x_1491_);
v_res_1499_ = l_Lean_Doc_parseContent_x27___redArg___lam__13(v_env_1486_, v_contents_1487_, v_p_1488_, v_ictx_1489_, v_toPure_1490_, v___x_1069__boxed_1498_, v_toBind_1492_, v_inst_1493_, v_inst_1494_, v_inst_1495_, v_inst_1496_, v_____do__lift_1497_);
lean_dec_ref(v_contents_1487_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object* v_inst_1500_, lean_object* v_contents_1501_, uint8_t v___x_1502_, lean_object* v_env_1503_, lean_object* v_p_1504_, lean_object* v_toPure_1505_, lean_object* v_toBind_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_____do__lift_1510_){
_start:
{
lean_object* v_getOptions_1511_; lean_object* v___x_1512_; lean_object* v_ictx_1513_; lean_object* v___x_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; 
v_getOptions_1511_ = lean_ctor_get(v_inst_1500_, 0);
lean_inc(v_getOptions_1511_);
v___x_1512_ = lean_string_utf8_byte_size(v_contents_1501_);
lean_inc_ref(v_contents_1501_);
v_ictx_1513_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1501_, v_____do__lift_1510_, v___x_1502_, v___x_1512_);
v___x_1514_ = lean_box(v___x_1502_);
lean_inc(v_toBind_1506_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_1515_, 0, v_env_1503_);
lean_closure_set(v___f_1515_, 1, v_contents_1501_);
lean_closure_set(v___f_1515_, 2, v_p_1504_);
lean_closure_set(v___f_1515_, 3, v_ictx_1513_);
lean_closure_set(v___f_1515_, 4, v_toPure_1505_);
lean_closure_set(v___f_1515_, 5, v___x_1514_);
lean_closure_set(v___f_1515_, 6, v_toBind_1506_);
lean_closure_set(v___f_1515_, 7, v_inst_1507_);
lean_closure_set(v___f_1515_, 8, v_inst_1508_);
lean_closure_set(v___f_1515_, 9, v_inst_1509_);
lean_closure_set(v___f_1515_, 10, v_inst_1500_);
v___x_1516_ = lean_apply_4(v_toBind_1506_, lean_box(0), lean_box(0), v_getOptions_1511_, v___f_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object* v_inst_1517_, lean_object* v_contents_1518_, lean_object* v___x_1519_, lean_object* v_env_1520_, lean_object* v_p_1521_, lean_object* v_toPure_1522_, lean_object* v_toBind_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_____do__lift_1527_){
_start:
{
uint8_t v___x_1156__boxed_1528_; lean_object* v_res_1529_; 
v___x_1156__boxed_1528_ = lean_unbox(v___x_1519_);
v_res_1529_ = l_Lean_Doc_parseContent_x27___redArg___lam__8(v_inst_1517_, v_contents_1518_, v___x_1156__boxed_1528_, v_env_1520_, v_p_1521_, v_toPure_1522_, v_toBind_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_____do__lift_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_contents_1532_, uint8_t v___x_1533_, lean_object* v_p_1534_, lean_object* v_toPure_1535_, lean_object* v_toBind_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_env_1539_){
_start:
{
lean_object* v_getFileName_1540_; lean_object* v___x_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; 
v_getFileName_1540_ = lean_ctor_get(v_inst_1530_, 2);
lean_inc(v_getFileName_1540_);
v___x_1541_ = lean_box(v___x_1533_);
lean_inc(v_toBind_1536_);
v___f_1542_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_1542_, 0, v_inst_1531_);
lean_closure_set(v___f_1542_, 1, v_contents_1532_);
lean_closure_set(v___f_1542_, 2, v___x_1541_);
lean_closure_set(v___f_1542_, 3, v_env_1539_);
lean_closure_set(v___f_1542_, 4, v_p_1534_);
lean_closure_set(v___f_1542_, 5, v_toPure_1535_);
lean_closure_set(v___f_1542_, 6, v_toBind_1536_);
lean_closure_set(v___f_1542_, 7, v_inst_1537_);
lean_closure_set(v___f_1542_, 8, v_inst_1530_);
lean_closure_set(v___f_1542_, 9, v_inst_1538_);
v___x_1543_ = lean_apply_4(v_toBind_1536_, lean_box(0), lean_box(0), v_getFileName_1540_, v___f_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_contents_1546_, lean_object* v___x_1547_, lean_object* v_p_1548_, lean_object* v_toPure_1549_, lean_object* v_toBind_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_env_1553_){
_start:
{
uint8_t v___x_1183__boxed_1554_; lean_object* v_res_1555_; 
v___x_1183__boxed_1554_ = lean_unbox(v___x_1547_);
v_res_1555_ = l_Lean_Doc_parseContent_x27___redArg___lam__9(v_inst_1544_, v_inst_1545_, v_contents_1546_, v___x_1183__boxed_1554_, v_p_1548_, v_toPure_1549_, v_toBind_1550_, v_inst_1551_, v_inst_1552_, v_env_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_p_1562_, lean_object* v_tok_1563_, lean_object* v_contents_1564_){
_start:
{
lean_object* v___x_1565_; uint8_t v___x_1566_; uint8_t v___y_1568_; lean_object* v___x_1583_; 
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = 1;
v___x_1583_ = l_Lean_Syntax_getPos_x3f(v_tok_1563_, v___x_1566_);
if (lean_obj_tag(v___x_1583_) == 0)
{
v___y_1568_ = v___x_1566_;
goto v___jp_1567_;
}
else
{
uint8_t v___x_1584_; 
lean_dec_ref_known(v___x_1583_, 1);
v___x_1584_ = 0;
v___y_1568_ = v___x_1584_;
goto v___jp_1567_;
}
v___jp_1567_:
{
if (v___y_1568_ == 0)
{
lean_object* v_toApplicative_1569_; lean_object* v_toBind_1570_; lean_object* v_toPure_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; 
v_toApplicative_1569_ = lean_ctor_get(v_inst_1556_, 0);
lean_dec_ref(v_contents_1564_);
v_toBind_1570_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc_n(v_toBind_1570_, 2);
v_toPure_1571_ = lean_ctor_get(v_toApplicative_1569_, 1);
lean_inc(v_toPure_1571_);
v___x_1572_ = lean_box(v___x_1566_);
v___x_1573_ = lean_box(v___y_1568_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1574_, 0, v_inst_1558_);
lean_closure_set(v___f_1574_, 1, v_inst_1560_);
lean_closure_set(v___f_1574_, 2, v___x_1572_);
lean_closure_set(v___f_1574_, 3, v_inst_1561_);
lean_closure_set(v___f_1574_, 4, v_p_1562_);
lean_closure_set(v___f_1574_, 5, v_toPure_1571_);
lean_closure_set(v___f_1574_, 6, v_toBind_1570_);
lean_closure_set(v___f_1574_, 7, v_inst_1556_);
lean_closure_set(v___f_1574_, 8, v_inst_1559_);
lean_closure_set(v___f_1574_, 9, v___x_1573_);
lean_closure_set(v___f_1574_, 10, v_tok_1563_);
lean_closure_set(v___f_1574_, 11, v___x_1565_);
v___x_1575_ = lean_apply_4(v_toBind_1570_, lean_box(0), lean_box(0), v_inst_1557_, v___f_1574_);
return v___x_1575_;
}
else
{
lean_object* v_toApplicative_1576_; lean_object* v_toBind_1577_; lean_object* v_toPure_1578_; lean_object* v_getEnv_1579_; lean_object* v___x_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; 
v_toApplicative_1576_ = lean_ctor_get(v_inst_1556_, 0);
lean_dec(v_tok_1563_);
lean_dec(v_inst_1557_);
v_toBind_1577_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc_n(v_toBind_1577_, 2);
v_toPure_1578_ = lean_ctor_get(v_toApplicative_1576_, 1);
lean_inc(v_toPure_1578_);
v_getEnv_1579_ = lean_ctor_get(v_inst_1558_, 0);
lean_inc(v_getEnv_1579_);
lean_dec_ref(v_inst_1558_);
v___x_1580_ = lean_box(v___x_1566_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1581_, 0, v_inst_1560_);
lean_closure_set(v___f_1581_, 1, v_inst_1561_);
lean_closure_set(v___f_1581_, 2, v_contents_1564_);
lean_closure_set(v___f_1581_, 3, v___x_1580_);
lean_closure_set(v___f_1581_, 4, v_p_1562_);
lean_closure_set(v___f_1581_, 5, v_toPure_1578_);
lean_closure_set(v___f_1581_, 6, v_toBind_1577_);
lean_closure_set(v___f_1581_, 7, v_inst_1556_);
lean_closure_set(v___f_1581_, 8, v_inst_1559_);
v___x_1582_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v_getEnv_1579_, v___f_1581_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object* v_m_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_p_1592_, lean_object* v_tok_1593_, lean_object* v_contents_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1586_, v_inst_1587_, v_inst_1588_, v_inst_1589_, v_inst_1590_, v_inst_1591_, v_p_1592_, v_tok_1593_, v_contents_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_p_1602_, lean_object* v_c_1603_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = l_Lean_TSyntax_getVersoCode(v_c_1603_);
v___x_1605_ = l_Lean_Doc_parseContent___redArg(v_inst_1596_, v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_p_1602_, v_c_1603_, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object* v_m_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_p_1613_, lean_object* v_c_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Doc_parseVersoCode___redArg(v_inst_1607_, v_inst_1608_, v_inst_1609_, v_inst_1610_, v_inst_1611_, v_inst_1612_, v_p_1613_, v_c_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_p_1622_, lean_object* v_c_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Lean_TSyntax_getVersoCodeBlock(v_c_1623_);
v___x_1625_ = l_Lean_Doc_parseContent___redArg(v_inst_1616_, v_inst_1617_, v_inst_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v_p_1622_, v_c_1623_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_p_1633_, lean_object* v_c_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Doc_parseVersoCodeBlock___redArg(v_inst_1627_, v_inst_1628_, v_inst_1629_, v_inst_1630_, v_inst_1631_, v_inst_1632_, v_p_1633_, v_c_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_p_1642_, lean_object* v_c_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = l_Lean_TSyntax_getVersoCode(v_c_1643_);
v___x_1645_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1636_, v_inst_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_p_1642_, v_c_1643_, v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object* v_m_1646_, lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_p_1653_, lean_object* v_c_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Doc_parseVersoCode_x27___redArg(v_inst_1647_, v_inst_1648_, v_inst_1649_, v_inst_1650_, v_inst_1651_, v_inst_1652_, v_p_1653_, v_c_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_p_1662_, lean_object* v_s_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = l_Lean_TSyntax_getString(v_s_1663_);
v___x_1665_ = l_Lean_Doc_parseContent___redArg(v_inst_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_, v_inst_1661_, v_p_1662_, v_s_1663_, v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_p_1673_, lean_object* v_s_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Doc_parseStrLit___redArg(v_inst_1667_, v_inst_1668_, v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_p_1673_, v_s_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_p_1682_, lean_object* v_s_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = l_Lean_TSyntax_getString(v_s_1683_);
v___x_1685_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1676_, v_inst_1677_, v_inst_1678_, v_inst_1679_, v_inst_1680_, v_inst_1681_, v_p_1682_, v_s_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_p_1693_, lean_object* v_s_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1687_, v_inst_1688_, v_inst_1689_, v_inst_1690_, v_inst_1691_, v_inst_1692_, v_p_1693_, v_s_1694_);
return v___x_1695_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Lean_DocString_View(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
}
#ifdef __cplusplus
}
#endif
