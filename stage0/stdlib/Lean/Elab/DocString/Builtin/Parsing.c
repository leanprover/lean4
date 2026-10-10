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
uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(lean_object* v_x_110_){
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
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_110_ = stack[0].m_obj;
uint8_t v_res_123_;
v_res_123_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(v_x_110_);
stack->m_num = v_res_123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank___boxed(lean_object* v_x_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(v_x_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0(lean_object* v_x_127_){
_start:
{
lean_inc(v_x_127_);
return v_x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0___boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__0(v_x_128_);
lean_dec(v_x_128_);
return v_res_129_;
}
}
uint8_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(lean_object* v_v_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange_isBlank(v_v_130_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_130_ = stack[0].m_obj;
uint8_t v_res_134_;
v_res_134_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(v_v_130_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1___boxed(lean_object* v_v_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__1(v_v_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3(lean_object* v_xs_160_, lean_object* v_toPure_161_, lean_object* v___f_162_, lean_object* v___f_163_, lean_object* v___f_164_, lean_object* v_ref_165_){
_start:
{
lean_object* v___x_184_; 
lean_inc(v_ref_165_);
v___x_184_ = l_Lean_Doc_RoleView_of(v_ref_165_);
if (lean_obj_tag(v___x_184_) == 1)
{
lean_object* v_val_185_; lean_object* v_brackets_186_; 
v_val_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v___x_184_, 1);
v_brackets_186_ = lean_ctor_get(v_val_185_, 5);
lean_inc(v_brackets_186_);
lean_dec(v_val_185_);
if (lean_obj_tag(v_brackets_186_) == 1)
{
lean_object* v_val_187_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; size_t v_sz_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_ref_165_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
v_val_187_ = lean_ctor_get(v_brackets_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v_brackets_186_, 1);
v_fst_188_ = lean_ctor_get(v_val_187_, 0);
lean_inc(v_fst_188_);
v_snd_189_ = lean_ctor_get(v_val_187_, 1);
lean_inc(v_snd_189_);
lean_dec(v_val_187_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
lean_inc_ref(v___x_191_);
v___x_192_ = lean_array_push(v___x_191_, v_fst_188_);
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v_sz_194_ = lean_array_size(v_xs_160_);
v___x_195_ = ((size_t)0ULL);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_193_, v___f_164_, v_sz_194_, v___x_195_, v_xs_160_);
v___x_197_ = l_Array_append___redArg(v___x_192_, v___x_196_);
lean_dec(v___x_196_);
v___x_198_ = lean_array_push(v___x_191_, v_snd_189_);
v___x_199_ = l_Array_append___redArg(v___x_197_, v___x_198_);
lean_dec_ref(v___x_198_);
v___x_200_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11));
v___x_201_ = lean_box(2);
v___x_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
v___x_203_ = lean_apply_2(v_toPure_161_, lean_box(0), v___x_202_);
return v___x_203_;
}
else
{
lean_dec(v_brackets_186_);
lean_dec_ref(v___f_164_);
goto v___jp_166_;
}
}
else
{
lean_dec(v___x_184_);
lean_dec_ref(v___f_164_);
goto v___jp_166_;
}
v___jp_166_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_array_get_size(v_xs_160_);
v___x_169_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v___x_170_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v_xs_160_);
v___x_171_ = lean_apply_2(v_toPure_161_, lean_box(0), v_ref_165_);
return v___x_171_;
}
else
{
if (v___x_170_ == 0)
{
lean_object* v___x_172_; 
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v_xs_160_);
v___x_172_ = lean_apply_2(v_toPure_161_, lean_box(0), v_ref_165_);
return v___x_172_;
}
else
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_168_);
lean_inc_ref(v_xs_160_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_169_, v___f_162_, v_xs_160_, v___x_173_, v___x_174_);
v___x_176_ = lean_unbox(v___x_175_);
lean_dec(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec_ref(v___f_163_);
lean_dec_ref(v_xs_160_);
v___x_177_ = lean_apply_2(v_toPure_161_, lean_box(0), v_ref_165_);
return v___x_177_;
}
else
{
size_t v_sz_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_ref_165_);
v_sz_178_ = lean_array_size(v_xs_160_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_169_, v___f_163_, v_sz_178_, v___x_173_, v_xs_160_);
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__11));
v___x_181_ = lean_box(2);
v___x_182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_179_);
v___x_183_ = lean_apply_2(v_toPure_161_, lean_box(0), v___x_182_);
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_xs_208_){
_start:
{
lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v_getRef_211_; lean_object* v_toPure_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; 
v_toApplicative_209_ = lean_ctor_get(v_inst_206_, 0);
lean_inc_ref(v_toApplicative_209_);
v_toBind_210_ = lean_ctor_get(v_inst_206_, 1);
lean_inc(v_toBind_210_);
lean_dec_ref(v_inst_206_);
v_getRef_211_ = lean_ctor_get(v_inst_207_, 0);
lean_inc(v_getRef_211_);
lean_dec_ref(v_inst_207_);
v_toPure_212_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_inc(v_toPure_212_);
lean_dec_ref(v_toApplicative_209_);
v___f_213_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__0));
v___f_214_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___closed__1));
v___f_215_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3), 6, 5);
lean_closure_set(v___f_215_, 0, v_xs_208_);
lean_closure_set(v___f_215_, 1, v_toPure_212_);
lean_closure_set(v___f_215_, 2, v___f_214_);
lean_closure_set(v___f_215_, 3, v___f_213_);
lean_closure_set(v___f_215_, 4, v___f_213_);
v___x_216_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v_getRef_211_, v___f_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange(lean_object* v_m_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_xs_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(v_inst_218_, v_inst_219_, v_xs_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Doc_onlyCode___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Doc_onlyCode___redArg___lam__0___closed__0));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__0(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_____do__lift_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_Doc_onlyCode___redArg___lam__0___closed__1, &l_Lean_Doc_onlyCode___redArg___lam__0___closed__1_once, _init_l_Lean_Doc_onlyCode___redArg___lam__0___closed__1);
v___x_229_ = l_Lean_throwErrorAt___redArg(v_inst_225_, v_inst_226_, v_____do__lift_227_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1(lean_object* v_inst_230_, lean_object* v_toMonadRef_231_, lean_object* v_xs_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_toPure_235_, lean_object* v_codes_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_array_get_size(v_codes_236_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_toPure_235_);
v___x_240_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg(v_inst_230_, v_toMonadRef_231_, v_xs_232_);
v___x_241_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_240_, v___f_234_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___f_234_);
lean_dec(v_toBind_233_);
lean_dec_ref(v_xs_232_);
lean_dec_ref(v_toMonadRef_231_);
lean_dec_ref(v_inst_230_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_fget_borrowed(v_codes_236_, v___x_242_);
lean_inc(v___x_243_);
v___x_244_ = lean_apply_2(v_toPure_235_, lean_box(0), v___x_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg___lam__1___boxed(lean_object* v_inst_245_, lean_object* v_toMonadRef_246_, lean_object* v_xs_247_, lean_object* v_toBind_248_, lean_object* v___f_249_, lean_object* v_toPure_250_, lean_object* v_codes_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Doc_onlyCode___redArg___lam__1(v_inst_245_, v_toMonadRef_246_, v_xs_247_, v_toBind_248_, v___f_249_, v_toPure_250_, v_codes_251_);
lean_dec_ref(v_codes_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_xs_255_){
_start:
{
lean_object* v_toApplicative_256_; lean_object* v_toBind_257_; lean_object* v_toMonadRef_258_; lean_object* v_toPure_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_toApplicative_256_ = lean_ctor_get(v_inst_253_, 0);
v_toBind_257_ = lean_ctor_get(v_inst_253_, 1);
lean_inc_n(v_toBind_257_, 2);
v_toMonadRef_258_ = lean_ctor_get(v_inst_254_, 1);
lean_inc_ref(v_toMonadRef_258_);
v_toPure_259_ = lean_ctor_get(v_toApplicative_256_, 1);
lean_inc(v_toPure_259_);
lean_inc_ref(v_inst_254_);
lean_inc_ref_n(v_inst_253_, 2);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCode___redArg___lam__0), 3, 2);
lean_closure_set(v___f_260_, 0, v_inst_253_);
lean_closure_set(v___f_260_, 1, v_inst_254_);
lean_inc_ref(v_xs_255_);
v___x_261_ = l_Lean_Doc_onlyCodes___redArg(v_inst_253_, v_inst_254_, v_xs_255_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Doc_onlyCode___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_262_, 0, v_inst_253_);
lean_closure_set(v___f_262_, 1, v_toMonadRef_258_);
lean_closure_set(v___f_262_, 2, v_xs_255_);
lean_closure_set(v___f_262_, 3, v_toBind_257_);
lean_closure_set(v___f_262_, 4, v___f_260_);
lean_closure_set(v___f_262_, 5, v_toPure_259_);
v___x_263_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v___x_261_, v___f_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_onlyCode(lean_object* v_m_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_xs_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Doc_onlyCode___redArg(v_inst_265_, v_inst_266_, v_xs_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2));
v___x_273_ = lean_unsigned_to_nat(14u);
v___x_274_ = lean_unsigned_to_nat(22u);
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1));
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0));
v___x_277_ = l_mkPanicMessageWithDecl(v___x_276_, v___x_275_, v___x_274_, v___x_273_, v___x_272_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object* v_inst_278_, lean_object* v_s_279_){
_start:
{
lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___y_297_; lean_object* v___x_302_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = 1;
v___x_302_ = l_Lean_Syntax_getPos_x3f(v_s_279_, v___x_295_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_304_ = l_panic___redArg(v___x_294_, v___x_303_);
v___y_297_ = v___x_304_;
goto v___jp_296_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_302_, 1);
v___y_297_ = v_val_305_;
goto v___jp_296_;
}
v___jp_280_:
{
lean_object* v_toApplicative_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_292_; 
v_toApplicative_283_ = lean_ctor_get(v_inst_278_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_inst_278_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_inst_278_, 1);
lean_dec(v_unused_293_);
v___x_285_ = v_inst_278_;
v_isShared_286_ = v_isSharedCheck_292_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_toApplicative_283_);
lean_dec(v_inst_278_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_292_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_toPure_287_; lean_object* v___x_289_; 
v_toPure_287_ = lean_ctor_get(v_toApplicative_283_, 1);
lean_inc(v_toPure_287_);
lean_dec_ref(v_toApplicative_283_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___y_282_);
lean_ctor_set(v___x_285_, 0, v___y_281_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___y_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___y_282_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_apply_2(v_toPure_287_, lean_box(0), v___x_289_);
return v___x_290_;
}
}
}
v___jp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Syntax_getTailPos_x3f(v_s_279_, v___x_295_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_300_ = l_panic___redArg(v___x_294_, v___x_299_);
v___y_281_ = v___y_297_;
v___y_282_ = v___x_300_;
goto v___jp_280_;
}
else
{
lean_object* v_val_301_; 
v_val_301_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_298_, 1);
v___y_281_ = v___y_297_;
v___y_282_ = v_val_301_;
goto v___jp_280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object* v_inst_306_, lean_object* v_s_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_306_, v_s_307_);
lean_dec(v_s_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_s_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_310_, v_s_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object* v_m_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_s_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(v_m_314_, v_inst_315_, v_inst_316_, v_s_317_);
lean_dec(v_s_317_);
lean_dec(v_inst_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object* v_env_320_, lean_object* v_contents_321_, lean_object* v_p_322_, lean_object* v_ictx_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_toPure_326_, lean_object* v_____do__lift_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_s_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_box(0);
lean_inc_ref(v_env_320_);
v___x_330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_330_, 0, v_env_320_);
lean_ctor_set(v___x_330_, 1, v_____do__lift_327_);
lean_ctor_set(v___x_330_, 2, v___x_328_);
lean_ctor_set(v___x_330_, 3, v___x_329_);
v___x_331_ = l_Lean_Parser_getTokenTable(v_env_320_);
v___x_332_ = l_Lean_Parser_mkParserState(v_contents_321_);
lean_inc_ref(v_ictx_323_);
v_s_333_ = l_Lean_Parser_ParserFn_run(v_p_322_, v_ictx_323_, v___x_330_, v___x_331_, v___x_332_);
lean_inc_ref(v_s_333_);
v___x_334_ = l_Lean_Parser_ParserState_allErrors(v_s_333_);
v___x_335_ = lean_array_get_size(v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_nat_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_toPure_326_);
v___x_338_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_323_, v_s_333_);
v___x_339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = l_Lean_MessageData_ofFormat(v___x_339_);
v___x_341_ = l_Lean_throwError___redArg(v_inst_324_, v_inst_325_, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v_stxStack_342_; lean_object* v_pos_343_; uint8_t v___x_344_; 
v_stxStack_342_ = lean_ctor_get(v_s_333_, 0);
v_pos_343_ = lean_ctor_get(v_s_333_, 2);
v___x_344_ = l_Lean_Parser_InputContext_atEnd(v_ictx_323_, v_pos_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_toPure_326_);
v___x_345_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_346_ = l_Lean_Parser_ParserState_mkError(v_s_333_, v___x_345_);
v___x_347_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_323_, v___x_346_);
v___x_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
v___x_349_ = l_Lean_MessageData_ofFormat(v___x_348_);
v___x_350_ = l_Lean_throwError___redArg(v_inst_324_, v_inst_325_, v___x_349_);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc_ref(v_stxStack_342_);
lean_dec_ref(v_s_333_);
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_inst_324_);
lean_dec_ref(v_ictx_323_);
v___x_351_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_342_);
lean_dec_ref(v_stxStack_342_);
v___x_352_ = lean_apply_2(v_toPure_326_, lean_box(0), v___x_351_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_353_, lean_object* v_contents_354_, lean_object* v_p_355_, lean_object* v_ictx_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_toPure_359_, lean_object* v_____do__lift_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_353_, v_contents_354_, v_p_355_, v_ictx_356_, v_inst_357_, v_inst_358_, v_toPure_359_, v_____do__lift_360_);
lean_dec_ref(v_contents_354_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_inst_362_, lean_object* v_contents_363_, lean_object* v_env_364_, lean_object* v_p_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_toPure_368_, lean_object* v_toBind_369_, lean_object* v_____do__lift_370_){
_start:
{
lean_object* v_getOptions_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v_ictx_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_getOptions_371_ = lean_ctor_get(v_inst_362_, 0);
lean_inc(v_getOptions_371_);
lean_dec_ref(v_inst_362_);
v___x_372_ = lean_string_utf8_byte_size(v_contents_363_);
v___x_373_ = 1;
lean_inc_ref(v_contents_363_);
v_ictx_374_ = l_Lean_Parser_mkInputContext___redArg(v_contents_363_, v_____do__lift_370_, v___x_373_, v___x_372_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_375_, 0, v_env_364_);
lean_closure_set(v___f_375_, 1, v_contents_363_);
lean_closure_set(v___f_375_, 2, v_p_365_);
lean_closure_set(v___f_375_, 3, v_ictx_374_);
lean_closure_set(v___f_375_, 4, v_inst_366_);
lean_closure_set(v___f_375_, 5, v_inst_367_);
lean_closure_set(v___f_375_, 6, v_toPure_368_);
v___x_376_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v_getOptions_371_, v___f_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_contents_379_, lean_object* v_p_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_toPure_383_, lean_object* v_toBind_384_, lean_object* v_env_385_){
_start:
{
lean_object* v_getFileName_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_getFileName_386_ = lean_ctor_get(v_inst_377_, 2);
lean_inc(v_getFileName_386_);
lean_dec_ref(v_inst_377_);
lean_inc(v_toBind_384_);
v___f_387_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_387_, 0, v_inst_378_);
lean_closure_set(v___f_387_, 1, v_contents_379_);
lean_closure_set(v___f_387_, 2, v_env_385_);
lean_closure_set(v___f_387_, 3, v_p_380_);
lean_closure_set(v___f_387_, 4, v_inst_381_);
lean_closure_set(v___f_387_, 5, v_inst_382_);
lean_closure_set(v___f_387_, 6, v_toPure_383_);
lean_closure_set(v___f_387_, 7, v_toBind_384_);
v___x_388_ = lean_apply_4(v_toBind_384_, lean_box(0), lean_box(0), v_getFileName_386_, v___f_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_p_394_, lean_object* v_contents_395_){
_start:
{
lean_object* v_toApplicative_396_; lean_object* v_toBind_397_; lean_object* v_getEnv_398_; lean_object* v_toPure_399_; lean_object* v___f_400_; lean_object* v___x_401_; 
v_toApplicative_396_ = lean_ctor_get(v_inst_389_, 0);
v_toBind_397_ = lean_ctor_get(v_inst_389_, 1);
lean_inc_n(v_toBind_397_, 2);
v_getEnv_398_ = lean_ctor_get(v_inst_390_, 0);
lean_inc(v_getEnv_398_);
lean_dec_ref(v_inst_390_);
v_toPure_399_ = lean_ctor_get(v_toApplicative_396_, 1);
lean_inc(v_toPure_399_);
v___f_400_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_400_, 0, v_inst_392_);
lean_closure_set(v___f_400_, 1, v_inst_393_);
lean_closure_set(v___f_400_, 2, v_contents_395_);
lean_closure_set(v___f_400_, 3, v_p_394_);
lean_closure_set(v___f_400_, 4, v_inst_389_);
lean_closure_set(v___f_400_, 5, v_inst_391_);
lean_closure_set(v___f_400_, 6, v_toPure_399_);
lean_closure_set(v___f_400_, 7, v_toBind_397_);
v___x_401_ = lean_apply_4(v_toBind_397_, lean_box(0), lean_box(0), v_getEnv_398_, v___f_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_p_408_, lean_object* v_contents_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_403_, v_inst_404_, v_inst_405_, v_inst_406_, v_inst_407_, v_p_408_, v_contents_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object* v_env_411_, lean_object* v_p_412_, lean_object* v_ictx_413_, lean_object* v_s_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_toPure_417_, lean_object* v_____do__lift_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_s_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_box(0);
lean_inc_ref(v_env_411_);
v___x_421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_421_, 0, v_env_411_);
lean_ctor_set(v___x_421_, 1, v_____do__lift_418_);
lean_ctor_set(v___x_421_, 2, v___x_419_);
lean_ctor_set(v___x_421_, 3, v___x_420_);
v___x_422_ = l_Lean_Parser_getTokenTable(v_env_411_);
lean_inc_ref(v_ictx_413_);
v_s_423_ = l_Lean_Parser_ParserFn_run(v_p_412_, v_ictx_413_, v___x_421_, v___x_422_, v_s_414_);
lean_inc_ref(v_s_423_);
v___x_424_ = l_Lean_Parser_ParserState_allErrors(v_s_423_);
v___x_425_ = lean_array_get_size(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_nat_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_toPure_417_);
v___x_428_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_413_, v_s_423_);
v___x_429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___x_430_ = l_Lean_MessageData_ofFormat(v___x_429_);
v___x_431_ = l_Lean_throwError___redArg(v_inst_415_, v_inst_416_, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_stxStack_432_; lean_object* v_pos_433_; uint8_t v___x_434_; 
v_stxStack_432_ = lean_ctor_get(v_s_423_, 0);
v_pos_433_ = lean_ctor_get(v_s_423_, 2);
v___x_434_ = l_Lean_Parser_InputContext_atEnd(v_ictx_413_, v_pos_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_toPure_417_);
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_436_ = l_Lean_Parser_ParserState_mkError(v_s_423_, v___x_435_);
v___x_437_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_413_, v___x_436_);
v___x_438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
v___x_439_ = l_Lean_MessageData_ofFormat(v___x_438_);
v___x_440_ = l_Lean_throwError___redArg(v_inst_415_, v_inst_416_, v___x_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc_ref(v_stxStack_432_);
lean_dec_ref(v_s_423_);
lean_dec_ref(v_inst_416_);
lean_dec_ref(v_inst_415_);
lean_dec_ref(v_ictx_413_);
v___x_441_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_432_);
lean_dec_ref(v_stxStack_432_);
v___x_442_ = lean_apply_2(v_toPure_417_, lean_box(0), v___x_441_);
return v___x_442_;
}
}
}
}
lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object* v_inst_443_, lean_object* v_source_444_, uint8_t v___x_445_, lean_object* v___y_446_, lean_object* v_start_447_, lean_object* v_env_448_, lean_object* v_p_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_toPure_452_, lean_object* v_toBind_453_, lean_object* v_____do__lift_454_){
_start:
{
lean_object* v_getOptions_455_; lean_object* v_ictx_456_; lean_object* v___x_457_; lean_object* v_s_458_; lean_object* v___f_459_; lean_object* v___x_460_; 
v_getOptions_455_ = lean_ctor_get(v_inst_443_, 0);
lean_inc(v_getOptions_455_);
lean_dec_ref(v_inst_443_);
lean_inc_ref(v_source_444_);
v_ictx_456_ = l_Lean_Parser_mkInputContext___redArg(v_source_444_, v_____do__lift_454_, v___x_445_, v___y_446_);
v___x_457_ = l_Lean_Parser_mkParserState(v_source_444_);
lean_dec_ref(v_source_444_);
v_s_458_ = l_Lean_Parser_ParserState_setPos(v___x_457_, v_start_447_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__0), 8, 7);
lean_closure_set(v___f_459_, 0, v_env_448_);
lean_closure_set(v___f_459_, 1, v_p_449_);
lean_closure_set(v___f_459_, 2, v_ictx_456_);
lean_closure_set(v___f_459_, 3, v_s_458_);
lean_closure_set(v___f_459_, 4, v_inst_450_);
lean_closure_set(v___f_459_, 5, v_inst_451_);
lean_closure_set(v___f_459_, 6, v_toPure_452_);
v___x_460_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v_getOptions_455_, v___f_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_443_ = stack[0].m_obj;
lean_object* v_source_444_ = stack[1].m_obj;
uint8_t v___x_445_ = stack[2].m_num;
lean_object* v___y_446_ = stack[3].m_obj;
lean_object* v_start_447_ = stack[4].m_obj;
lean_object* v_env_448_ = stack[5].m_obj;
lean_object* v_p_449_ = stack[6].m_obj;
lean_object* v_inst_450_ = stack[7].m_obj;
lean_object* v_inst_451_ = stack[8].m_obj;
lean_object* v_toPure_452_ = stack[9].m_obj;
lean_object* v_toBind_453_ = stack[10].m_obj;
lean_object* v_____do__lift_454_ = stack[11].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_Doc_parseContent___redArg___lam__1(v_inst_443_, v_source_444_, v___x_445_, v___y_446_, v_start_447_, v_env_448_, v_p_449_, v_inst_450_, v_inst_451_, v_toPure_452_, v_toBind_453_, v_____do__lift_454_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object* v_inst_462_, lean_object* v_source_463_, lean_object* v___x_464_, lean_object* v___y_465_, lean_object* v_start_466_, lean_object* v_env_467_, lean_object* v_p_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_toPure_471_, lean_object* v_toBind_472_, lean_object* v_____do__lift_473_){
_start:
{
uint8_t v___x_387__boxed_474_; lean_object* v_res_475_; 
v___x_387__boxed_474_ = lean_unbox(v___x_464_);
v_res_475_ = l_Lean_Doc_parseContent___redArg___lam__1(v_inst_462_, v_source_463_, v___x_387__boxed_474_, v___y_465_, v_start_466_, v_env_467_, v_p_468_, v_inst_469_, v_inst_470_, v_toPure_471_, v_toBind_472_, v_____do__lift_473_);
return v_res_475_;
}
}
lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object* v_text_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, uint8_t v___x_479_, lean_object* v_env_480_, lean_object* v_p_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_toPure_484_, lean_object* v_toBind_485_, lean_object* v_____x_486_){
_start:
{
lean_object* v_start_487_; lean_object* v_stop_488_; lean_object* v_source_489_; lean_object* v___y_491_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_start_487_ = lean_ctor_get(v_____x_486_, 0);
lean_inc(v_start_487_);
v_stop_488_ = lean_ctor_get(v_____x_486_, 1);
lean_inc(v_stop_488_);
lean_dec_ref(v_____x_486_);
v_source_489_ = lean_ctor_get(v_text_476_, 0);
lean_inc_ref(v_source_489_);
lean_dec_ref(v_text_476_);
v___x_496_ = lean_string_utf8_byte_size(v_source_489_);
v___x_497_ = lean_nat_dec_le(v_stop_488_, v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v_stop_488_);
v___y_491_ = v___x_496_;
goto v___jp_490_;
}
else
{
v___y_491_ = v_stop_488_;
goto v___jp_490_;
}
v___jp_490_:
{
lean_object* v_getFileName_492_; lean_object* v___x_493_; lean_object* v___f_494_; lean_object* v___x_495_; 
v_getFileName_492_ = lean_ctor_get(v_inst_477_, 2);
lean_inc(v_getFileName_492_);
lean_dec_ref(v_inst_477_);
v___x_493_ = lean_box(v___x_479_);
lean_inc(v_toBind_485_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_494_, 0, v_inst_478_);
lean_closure_set(v___f_494_, 1, v_source_489_);
lean_closure_set(v___f_494_, 2, v___x_493_);
lean_closure_set(v___f_494_, 3, v___y_491_);
lean_closure_set(v___f_494_, 4, v_start_487_);
lean_closure_set(v___f_494_, 5, v_env_480_);
lean_closure_set(v___f_494_, 6, v_p_481_);
lean_closure_set(v___f_494_, 7, v_inst_482_);
lean_closure_set(v___f_494_, 8, v_inst_483_);
lean_closure_set(v___f_494_, 9, v_toPure_484_);
lean_closure_set(v___f_494_, 10, v_toBind_485_);
v___x_495_ = lean_apply_4(v_toBind_485_, lean_box(0), lean_box(0), v_getFileName_492_, v___f_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_476_ = stack[0].m_obj;
lean_object* v_inst_477_ = stack[1].m_obj;
lean_object* v_inst_478_ = stack[2].m_obj;
uint8_t v___x_479_ = stack[3].m_num;
lean_object* v_env_480_ = stack[4].m_obj;
lean_object* v_p_481_ = stack[5].m_obj;
lean_object* v_inst_482_ = stack[6].m_obj;
lean_object* v_inst_483_ = stack[7].m_obj;
lean_object* v_toPure_484_ = stack[8].m_obj;
lean_object* v_toBind_485_ = stack[9].m_obj;
lean_object* v_____x_486_ = stack[10].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Doc_parseContent___redArg___lam__2(v_text_476_, v_inst_477_, v_inst_478_, v___x_479_, v_env_480_, v_p_481_, v_inst_482_, v_inst_483_, v_toPure_484_, v_toBind_485_, v_____x_486_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object* v_text_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v___x_502_, lean_object* v_env_503_, lean_object* v_p_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_toPure_507_, lean_object* v_toBind_508_, lean_object* v_____x_509_){
_start:
{
uint8_t v___x_432__boxed_510_; lean_object* v_res_511_; 
v___x_432__boxed_510_ = lean_unbox(v___x_502_);
v_res_511_ = l_Lean_Doc_parseContent___redArg___lam__2(v_text_499_, v_inst_500_, v_inst_501_, v___x_432__boxed_510_, v_env_503_, v_p_504_, v_inst_505_, v_inst_506_, v_toPure_507_, v_toBind_508_, v_____x_509_);
return v_res_511_;
}
}
lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object* v_text_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, uint8_t v___x_515_, lean_object* v_p_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_toPure_519_, lean_object* v_toBind_520_, lean_object* v_tok_521_, lean_object* v_env_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_box(v___x_515_);
lean_inc(v_toBind_520_);
lean_inc_ref(v_inst_517_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_524_, 0, v_text_512_);
lean_closure_set(v___f_524_, 1, v_inst_513_);
lean_closure_set(v___f_524_, 2, v_inst_514_);
lean_closure_set(v___f_524_, 3, v___x_523_);
lean_closure_set(v___f_524_, 4, v_env_522_);
lean_closure_set(v___f_524_, 5, v_p_516_);
lean_closure_set(v___f_524_, 6, v_inst_517_);
lean_closure_set(v___f_524_, 7, v_inst_518_);
lean_closure_set(v___f_524_, 8, v_toPure_519_);
lean_closure_set(v___f_524_, 9, v_toBind_520_);
v___x_525_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_517_, v_tok_521_);
v___x_526_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_525_, v___f_524_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_512_ = stack[0].m_obj;
lean_object* v_inst_513_ = stack[1].m_obj;
lean_object* v_inst_514_ = stack[2].m_obj;
uint8_t v___x_515_ = stack[3].m_num;
lean_object* v_p_516_ = stack[4].m_obj;
lean_object* v_inst_517_ = stack[5].m_obj;
lean_object* v_inst_518_ = stack[6].m_obj;
lean_object* v_toPure_519_ = stack[7].m_obj;
lean_object* v_toBind_520_ = stack[8].m_obj;
lean_object* v_tok_521_ = stack[9].m_obj;
lean_object* v_env_522_ = stack[10].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_Doc_parseContent___redArg___lam__3(v_text_512_, v_inst_513_, v_inst_514_, v___x_515_, v_p_516_, v_inst_517_, v_inst_518_, v_toPure_519_, v_toBind_520_, v_tok_521_, v_env_522_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object* v_text_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v___x_531_, lean_object* v_p_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_toPure_535_, lean_object* v_toBind_536_, lean_object* v_tok_537_, lean_object* v_env_538_){
_start:
{
uint8_t v___x_489__boxed_539_; lean_object* v_res_540_; 
v___x_489__boxed_539_ = lean_unbox(v___x_531_);
v_res_540_ = l_Lean_Doc_parseContent___redArg___lam__3(v_text_528_, v_inst_529_, v_inst_530_, v___x_489__boxed_539_, v_p_532_, v_inst_533_, v_inst_534_, v_toPure_535_, v_toBind_536_, v_tok_537_, v_env_538_);
lean_dec(v_tok_537_);
return v_res_540_;
}
}
lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, uint8_t v___x_544_, lean_object* v_p_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_toPure_548_, lean_object* v_toBind_549_, lean_object* v_tok_550_, lean_object* v_text_551_){
_start:
{
lean_object* v_getEnv_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
v_getEnv_552_ = lean_ctor_get(v_inst_541_, 0);
lean_inc(v_getEnv_552_);
lean_dec_ref(v_inst_541_);
v___x_553_ = lean_box(v___x_544_);
lean_inc(v_toBind_549_);
v___f_554_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_554_, 0, v_text_551_);
lean_closure_set(v___f_554_, 1, v_inst_542_);
lean_closure_set(v___f_554_, 2, v_inst_543_);
lean_closure_set(v___f_554_, 3, v___x_553_);
lean_closure_set(v___f_554_, 4, v_p_545_);
lean_closure_set(v___f_554_, 5, v_inst_546_);
lean_closure_set(v___f_554_, 6, v_inst_547_);
lean_closure_set(v___f_554_, 7, v_toPure_548_);
lean_closure_set(v___f_554_, 8, v_toBind_549_);
lean_closure_set(v___f_554_, 9, v_tok_550_);
v___x_555_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v_getEnv_552_, v___f_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_541_ = stack[0].m_obj;
lean_object* v_inst_542_ = stack[1].m_obj;
lean_object* v_inst_543_ = stack[2].m_obj;
uint8_t v___x_544_ = stack[3].m_num;
lean_object* v_p_545_ = stack[4].m_obj;
lean_object* v_inst_546_ = stack[5].m_obj;
lean_object* v_inst_547_ = stack[6].m_obj;
lean_object* v_toPure_548_ = stack[7].m_obj;
lean_object* v_toBind_549_ = stack[8].m_obj;
lean_object* v_tok_550_ = stack[9].m_obj;
lean_object* v_text_551_ = stack[10].m_obj;
lean_object* v_res_556_;
v_res_556_ = l_Lean_Doc_parseContent___redArg___lam__4(v_inst_541_, v_inst_542_, v_inst_543_, v___x_544_, v_p_545_, v_inst_546_, v_inst_547_, v_toPure_548_, v_toBind_549_, v_tok_550_, v_text_551_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v___x_560_, lean_object* v_p_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_toPure_564_, lean_object* v_toBind_565_, lean_object* v_tok_566_, lean_object* v_text_567_){
_start:
{
uint8_t v___x_527__boxed_568_; lean_object* v_res_569_; 
v___x_527__boxed_568_ = lean_unbox(v___x_560_);
v_res_569_ = l_Lean_Doc_parseContent___redArg___lam__4(v_inst_557_, v_inst_558_, v_inst_559_, v___x_527__boxed_568_, v_p_561_, v_inst_562_, v_inst_563_, v_toPure_564_, v_toBind_565_, v_tok_566_, v_text_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_p_576_, lean_object* v_tok_577_, lean_object* v_contents_578_){
_start:
{
uint8_t v___x_579_; uint8_t v___y_581_; lean_object* v___x_589_; 
v___x_579_ = 1;
v___x_589_ = l_Lean_Syntax_getPos_x3f(v_tok_577_, v___x_579_);
if (lean_obj_tag(v___x_589_) == 0)
{
v___y_581_ = v___x_579_;
goto v___jp_580_;
}
else
{
uint8_t v___x_590_; 
lean_dec_ref_known(v___x_589_, 1);
v___x_590_ = 0;
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
v___jp_580_:
{
if (v___y_581_ == 0)
{
lean_object* v_toApplicative_582_; lean_object* v_toBind_583_; lean_object* v_toPure_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; 
v_toApplicative_582_ = lean_ctor_get(v_inst_570_, 0);
lean_dec_ref(v_contents_578_);
v_toBind_583_ = lean_ctor_get(v_inst_570_, 1);
lean_inc_n(v_toBind_583_, 2);
v_toPure_584_ = lean_ctor_get(v_toApplicative_582_, 1);
lean_inc(v_toPure_584_);
v___x_585_ = lean_box(v___x_579_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_586_, 0, v_inst_572_);
lean_closure_set(v___f_586_, 1, v_inst_574_);
lean_closure_set(v___f_586_, 2, v_inst_575_);
lean_closure_set(v___f_586_, 3, v___x_585_);
lean_closure_set(v___f_586_, 4, v_p_576_);
lean_closure_set(v___f_586_, 5, v_inst_570_);
lean_closure_set(v___f_586_, 6, v_inst_573_);
lean_closure_set(v___f_586_, 7, v_toPure_584_);
lean_closure_set(v___f_586_, 8, v_toBind_583_);
lean_closure_set(v___f_586_, 9, v_tok_577_);
v___x_587_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v_inst_571_, v___f_586_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; 
lean_dec(v_tok_577_);
lean_dec(v_inst_571_);
v___x_588_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_570_, v_inst_572_, v_inst_573_, v_inst_574_, v_inst_575_, v_p_576_, v_contents_578_);
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object* v_m_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_p_598_, lean_object* v_tok_599_, lean_object* v_contents_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Doc_parseContent___redArg(v_inst_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_, v_inst_597_, v_p_598_, v_tok_599_, v_contents_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_fst_604_ = lean_ctor_get(v_a_603_, 0);
v_snd_605_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v_a_603_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_a_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_dec_le(v___x_609_, v_fst_604_);
if (v___x_610_ == 0)
{
lean_object* v___x_612_; 
if (v_isShared_608_ == 0)
{
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_snd_605_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_614_ = lean_string_utf8_prev(v_str_602_, v_fst_604_);
lean_dec(v_fst_604_);
v___x_615_ = lean_nat_add(v_snd_605_, v___x_609_);
lean_dec(v_snd_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_615_);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_617_ = v___x_607_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_615_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_a_603_ = v___x_617_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_621_, v_a_622_);
lean_dec_ref(v_str_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_624_, lean_object* v_p_625_){
_start:
{
lean_object* v_n_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_snd_629_; 
v_n_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_p_625_);
lean_ctor_set(v___x_627_, 1, v_n_626_);
v___x_628_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_624_, v___x_627_);
v_snd_629_ = lean_ctor_get(v___x_628_, 1);
lean_inc(v_snd_629_);
lean_dec_ref(v___x_628_);
return v_snd_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_630_, lean_object* v_p_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_630_, v_p_631_);
lean_dec_ref(v_str_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_633_, lean_object* v_inst_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_633_, v_a_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_637_, lean_object* v_inst_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_637_, v_inst_638_, v_a_639_);
lean_dec_ref(v_str_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_641_, lean_object* v_p_642_, lean_object* v_j_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_zero_645_; uint8_t v_isZero_646_; 
v_zero_645_ = lean_unsigned_to_nat(0u);
v_isZero_646_ = lean_nat_dec_eq(v_j_643_, v_zero_645_);
if (v_isZero_646_ == 1)
{
lean_dec(v_j_643_);
return v_a_644_;
}
else
{
lean_object* v_one_647_; lean_object* v_n_648_; lean_object* v___x_649_; 
lean_dec(v_a_644_);
v_one_647_ = lean_unsigned_to_nat(1u);
v_n_648_ = lean_nat_sub(v_j_643_, v_one_647_);
lean_dec(v_j_643_);
v___x_649_ = lean_string_utf8_next(v_str_641_, v_p_642_);
v_j_643_ = v_n_648_;
v_a_644_ = v___x_649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_651_, lean_object* v_p_652_, lean_object* v_j_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_651_, v_p_652_, v_j_653_, v_a_654_);
lean_dec(v_p_652_);
lean_dec_ref(v_str_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_656_, lean_object* v_n_657_, lean_object* v_p_658_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v_p_658_);
v___x_659_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_656_, v_p_658_, v_n_657_, v_p_658_);
lean_dec(v_p_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_660_, lean_object* v_n_661_, lean_object* v_p_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_660_, v_n_661_, v_p_662_);
lean_dec_ref(v_str_660_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_664_, lean_object* v_p_665_, lean_object* v_n_666_, lean_object* v_j_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_664_, v_p_665_, v_j_667_, v_a_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_671_, lean_object* v_p_672_, lean_object* v_n_673_, lean_object* v_j_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_671_, v_p_672_, v_n_673_, v_j_674_, v_a_675_, v_a_676_);
lean_dec(v_n_673_);
lean_dec(v_p_672_);
lean_dec_ref(v_str_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_678_, lean_object* v_posOfStr_679_, lean_object* v_str_680_, lean_object* v_posInStr_681_){
_start:
{
lean_object* v_source_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_source_682_ = lean_ctor_get(v_text_678_, 0);
v___x_683_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_680_, v_posInStr_681_);
lean_inc(v_posOfStr_679_);
v___x_684_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_682_, v_posOfStr_679_, v___x_683_, v_posOfStr_679_);
lean_dec(v_posOfStr_679_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_685_, lean_object* v_posOfStr_686_, lean_object* v_str_687_, lean_object* v_posInStr_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_685_, v_posOfStr_686_, v_str_687_, v_posInStr_688_);
lean_dec_ref(v_str_687_);
lean_dec_ref(v_text_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_690_, lean_object* v_posOfStr_691_, lean_object* v_str_692_, lean_object* v_a_693_){
_start:
{
switch(lean_obj_tag(v_a_693_))
{
case 0:
{
lean_object* v_pos_694_; lean_object* v_endPos_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; 
v_pos_694_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_pos_694_);
v_endPos_695_ = lean_ctor_get(v_a_693_, 3);
lean_inc(v_endPos_695_);
lean_dec_ref_known(v_a_693_, 4);
lean_inc(v_posOfStr_691_);
v___x_696_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_690_, v_posOfStr_691_, v_str_692_, v_pos_694_);
v___x_697_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_690_, v_posOfStr_691_, v_str_692_, v_endPos_695_);
v___x_698_ = 1;
v___x_699_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_699_, 0, v___x_696_);
lean_ctor_set(v___x_699_, 1, v___x_697_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*2, v___x_698_);
return v___x_699_;
}
case 1:
{
lean_object* v_pos_700_; lean_object* v_endPos_701_; uint8_t v_canonical_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
v_pos_700_ = lean_ctor_get(v_a_693_, 0);
v_endPos_701_ = lean_ctor_get(v_a_693_, 1);
v_canonical_702_ = lean_ctor_get_uint8(v_a_693_, sizeof(void*)*2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_711_ == 0)
{
v___x_704_ = v_a_693_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_endPos_701_);
lean_inc(v_pos_700_);
lean_dec(v_a_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
lean_inc(v_posOfStr_691_);
v___x_706_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_690_, v_posOfStr_691_, v_str_692_, v_pos_700_);
v___x_707_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_690_, v_posOfStr_691_, v_str_692_, v_endPos_701_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_707_);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*2, v_canonical_702_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
default: 
{
lean_dec(v_posOfStr_691_);
return v_a_693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_712_, lean_object* v_posOfStr_713_, lean_object* v_str_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_712_, v_posOfStr_713_, v_str_714_, v_a_715_);
lean_dec_ref(v_str_714_);
lean_dec_ref(v_text_712_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_717_, lean_object* v_posOfStr_718_, lean_object* v_str_719_, lean_object* v_a_720_){
_start:
{
switch(lean_obj_tag(v_a_720_))
{
case 0:
{
lean_dec(v_posOfStr_718_);
return v_a_720_;
}
case 1:
{
lean_object* v_info_721_; lean_object* v_kind_722_; lean_object* v_args_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_734_; 
v_info_721_ = lean_ctor_get(v_a_720_, 0);
v_kind_722_ = lean_ctor_get(v_a_720_, 1);
v_args_723_ = lean_ctor_get(v_a_720_, 2);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_734_ == 0)
{
v___x_725_ = v_a_720_;
v_isShared_726_ = v_isSharedCheck_734_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_args_723_);
lean_inc(v_kind_722_);
lean_inc(v_info_721_);
lean_dec(v_a_720_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_734_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
lean_inc(v_posOfStr_718_);
v___x_727_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_717_, v_posOfStr_718_, v_str_719_, v_info_721_);
v_sz_728_ = lean_array_size(v_args_723_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_717_, v_posOfStr_718_, v_str_719_, v_sz_728_, v___x_729_, v_args_723_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 2, v___x_730_);
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_kind_722_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
case 2:
{
lean_object* v_info_735_; lean_object* v_val_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_info_735_ = lean_ctor_get(v_a_720_, 0);
v_val_736_ = lean_ctor_get(v_a_720_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v_a_720_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_val_736_);
lean_inc(v_info_735_);
lean_dec(v_a_720_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_717_, v_posOfStr_718_, v_str_719_, v_info_735_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_val_736_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
default: 
{
lean_object* v_info_745_; lean_object* v_rawVal_746_; lean_object* v_val_747_; lean_object* v_preresolved_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_info_745_ = lean_ctor_get(v_a_720_, 0);
v_rawVal_746_ = lean_ctor_get(v_a_720_, 1);
v_val_747_ = lean_ctor_get(v_a_720_, 2);
v_preresolved_748_ = lean_ctor_get(v_a_720_, 3);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_a_720_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_preresolved_748_);
lean_inc(v_val_747_);
lean_inc(v_rawVal_746_);
lean_inc(v_info_745_);
lean_dec(v_a_720_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_717_, v_posOfStr_718_, v_str_719_, v_info_745_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_rawVal_746_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_val_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_preresolved_748_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_757_, lean_object* v_posOfStr_758_, lean_object* v_str_759_, size_t v_sz_760_, size_t v_i_761_, lean_object* v_bs_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = lean_usize_dec_lt(v_i_761_, v_sz_760_);
if (v___x_763_ == 0)
{
lean_dec(v_posOfStr_758_);
return v_bs_762_;
}
else
{
lean_object* v_v_764_; lean_object* v___x_765_; lean_object* v_bs_x27_766_; lean_object* v___x_767_; size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
v_v_764_ = lean_array_uget(v_bs_762_, v_i_761_);
v___x_765_ = lean_unsigned_to_nat(0u);
v_bs_x27_766_ = lean_array_uset(v_bs_762_, v_i_761_, v___x_765_);
lean_inc(v_posOfStr_758_);
v___x_767_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_757_, v_posOfStr_758_, v_str_759_, v_v_764_);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_761_, v___x_768_);
v___x_770_ = lean_array_uset(v_bs_x27_766_, v_i_761_, v___x_767_);
v_i_761_ = v___x_769_;
v_bs_762_ = v___x_770_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_757_ = stack[0].m_obj;
lean_object* v_posOfStr_758_ = stack[1].m_obj;
lean_object* v_str_759_ = stack[2].m_obj;
size_t v_sz_760_ = stack[3].m_num;
size_t v_i_761_ = stack[4].m_num;
lean_object* v_bs_762_ = stack[5].m_obj;
lean_object* v_res_772_;
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_757_, v_posOfStr_758_, v_str_759_, v_sz_760_, v_i_761_, v_bs_762_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_773_, lean_object* v_posOfStr_774_, lean_object* v_str_775_, lean_object* v_sz_776_, lean_object* v_i_777_, lean_object* v_bs_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_776_);
lean_dec(v_sz_776_);
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_773_, v_posOfStr_774_, v_str_775_, v_sz_boxed_779_, v_i_boxed_780_, v_bs_778_);
lean_dec_ref(v_str_775_);
lean_dec_ref(v_text_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_782_, lean_object* v_posOfStr_783_, lean_object* v_str_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_782_, v_posOfStr_783_, v_str_784_, v_a_785_);
lean_dec_ref(v_str_784_);
lean_dec_ref(v_text_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_787_, lean_object* v_h__1_788_, lean_object* v_h__2_789_, lean_object* v_h__3_790_, lean_object* v_h__4_791_){
_start:
{
switch(lean_obj_tag(v_x_787_))
{
case 0:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_h__3_790_);
lean_dec(v_h__2_789_);
lean_dec(v_h__1_788_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_apply_1(v_h__4_791_, v___x_792_);
return v___x_793_;
}
case 1:
{
lean_object* v_info_794_; lean_object* v_kind_795_; lean_object* v_args_796_; lean_object* v___x_797_; 
lean_dec(v_h__4_791_);
lean_dec(v_h__3_790_);
lean_dec(v_h__2_789_);
v_info_794_ = lean_ctor_get(v_x_787_, 0);
lean_inc(v_info_794_);
v_kind_795_ = lean_ctor_get(v_x_787_, 1);
lean_inc(v_kind_795_);
v_args_796_ = lean_ctor_get(v_x_787_, 2);
lean_inc_ref(v_args_796_);
lean_dec_ref_known(v_x_787_, 3);
v___x_797_ = lean_apply_3(v_h__1_788_, v_info_794_, v_kind_795_, v_args_796_);
return v___x_797_;
}
case 2:
{
lean_object* v_info_798_; lean_object* v_val_799_; lean_object* v___x_800_; 
lean_dec(v_h__4_791_);
lean_dec(v_h__2_789_);
lean_dec(v_h__1_788_);
v_info_798_ = lean_ctor_get(v_x_787_, 0);
lean_inc(v_info_798_);
v_val_799_ = lean_ctor_get(v_x_787_, 1);
lean_inc_ref(v_val_799_);
lean_dec_ref_known(v_x_787_, 2);
v___x_800_ = lean_apply_2(v_h__3_790_, v_info_798_, v_val_799_);
return v___x_800_;
}
default: 
{
lean_object* v_info_801_; lean_object* v_rawVal_802_; lean_object* v_val_803_; lean_object* v_preresolved_804_; lean_object* v___x_805_; 
lean_dec(v_h__4_791_);
lean_dec(v_h__3_790_);
lean_dec(v_h__1_788_);
v_info_801_ = lean_ctor_get(v_x_787_, 0);
lean_inc(v_info_801_);
v_rawVal_802_ = lean_ctor_get(v_x_787_, 1);
lean_inc_ref(v_rawVal_802_);
v_val_803_ = lean_ctor_get(v_x_787_, 2);
lean_inc(v_val_803_);
v_preresolved_804_ = lean_ctor_get(v_x_787_, 3);
lean_inc(v_preresolved_804_);
lean_dec_ref_known(v_x_787_, 4);
v___x_805_ = lean_apply_4(v_h__2_789_, v_info_801_, v_rawVal_802_, v_val_803_, v_preresolved_804_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_806_, lean_object* v_x_807_, lean_object* v_h__1_808_, lean_object* v_h__2_809_, lean_object* v_h__3_810_, lean_object* v_h__4_811_){
_start:
{
switch(lean_obj_tag(v_x_807_))
{
case 0:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_h__3_810_);
lean_dec(v_h__2_809_);
lean_dec(v_h__1_808_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_apply_1(v_h__4_811_, v___x_812_);
return v___x_813_;
}
case 1:
{
lean_object* v_info_814_; lean_object* v_kind_815_; lean_object* v_args_816_; lean_object* v___x_817_; 
lean_dec(v_h__4_811_);
lean_dec(v_h__3_810_);
lean_dec(v_h__2_809_);
v_info_814_ = lean_ctor_get(v_x_807_, 0);
lean_inc(v_info_814_);
v_kind_815_ = lean_ctor_get(v_x_807_, 1);
lean_inc(v_kind_815_);
v_args_816_ = lean_ctor_get(v_x_807_, 2);
lean_inc_ref(v_args_816_);
lean_dec_ref_known(v_x_807_, 3);
v___x_817_ = lean_apply_3(v_h__1_808_, v_info_814_, v_kind_815_, v_args_816_);
return v___x_817_;
}
case 2:
{
lean_object* v_info_818_; lean_object* v_val_819_; lean_object* v___x_820_; 
lean_dec(v_h__4_811_);
lean_dec(v_h__2_809_);
lean_dec(v_h__1_808_);
v_info_818_ = lean_ctor_get(v_x_807_, 0);
lean_inc(v_info_818_);
v_val_819_ = lean_ctor_get(v_x_807_, 1);
lean_inc_ref(v_val_819_);
lean_dec_ref_known(v_x_807_, 2);
v___x_820_ = lean_apply_2(v_h__3_810_, v_info_818_, v_val_819_);
return v___x_820_;
}
default: 
{
lean_object* v_info_821_; lean_object* v_rawVal_822_; lean_object* v_val_823_; lean_object* v_preresolved_824_; lean_object* v___x_825_; 
lean_dec(v_h__4_811_);
lean_dec(v_h__3_810_);
lean_dec(v_h__1_808_);
v_info_821_ = lean_ctor_get(v_x_807_, 0);
lean_inc(v_info_821_);
v_rawVal_822_ = lean_ctor_get(v_x_807_, 1);
lean_inc_ref(v_rawVal_822_);
v_val_823_ = lean_ctor_get(v_x_807_, 2);
lean_inc(v_val_823_);
v_preresolved_824_ = lean_ctor_get(v_x_807_, 3);
lean_inc(v_preresolved_824_);
lean_dec_ref_known(v_x_807_, 4);
v___x_825_ = lean_apply_4(v_h__2_809_, v_info_821_, v_rawVal_822_, v_val_823_, v_preresolved_824_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_826_, lean_object* v_h__1_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_apply_2(v_h__1_827_, v_x_826_, lean_box(0));
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_829_, lean_object* v_P_830_, lean_object* v_motive_831_, lean_object* v_x_832_, lean_object* v_h__1_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_apply_2(v_h__1_833_, v_x_832_, lean_box(0));
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_toPure_835_, lean_object* v_____do__lift_836_){
_start:
{
if (lean_obj_tag(v_____do__lift_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_a_837_ = lean_ctor_get(v_____do__lift_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_____do__lift_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v_____do__lift_836_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v_____do__lift_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_toPure_835_, lean_box(0), v___x_842_);
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_a_846_ = lean_ctor_get(v_____do__lift_836_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_____do__lift_836_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v_____do__lift_836_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v_____do__lift_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 0);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_apply_2(v_toPure_835_, lean_box(0), v___x_851_);
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_text_855_, lean_object* v_pos_856_, lean_object* v_str_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_fst_859_ = lean_ctor_get(v_x_858_, 0);
v_snd_860_ = lean_ctor_get(v_x_858_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v_x_858_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_inc(v_fst_859_);
lean_dec(v_x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_855_, v_pos_856_, v_str_857_, v_fst_859_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_snd_860_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_text_869_, lean_object* v_pos_870_, lean_object* v_str_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_text_869_, v_pos_870_, v_str_871_, v_x_872_);
lean_dec_ref(v_str_871_);
lean_dec_ref(v_text_869_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_env_874_, lean_object* v_p_875_, lean_object* v_ictx_876_, lean_object* v_s_877_, lean_object* v_text_878_, lean_object* v_pos_879_, lean_object* v_str_880_, lean_object* v___f_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_toPure_884_, lean_object* v_____do__lift_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_s_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_886_ = lean_box(0);
v___x_887_ = lean_box(0);
lean_inc_ref(v_env_874_);
v___x_888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_888_, 0, v_env_874_);
lean_ctor_set(v___x_888_, 1, v_____do__lift_885_);
lean_ctor_set(v___x_888_, 2, v___x_886_);
lean_ctor_set(v___x_888_, 3, v___x_887_);
v___x_889_ = l_Lean_Parser_getTokenTable(v_env_874_);
lean_inc_ref(v_ictx_876_);
v_s_890_ = l_Lean_Parser_ParserFn_run(v_p_875_, v_ictx_876_, v___x_888_, v___x_889_, v_s_877_);
lean_inc_ref(v_s_890_);
v___x_891_ = l_Lean_Parser_ParserState_allErrors(v_s_890_);
v___x_892_ = lean_array_get_size(v___x_891_);
lean_dec_ref(v___x_891_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_nat_dec_eq(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v_stxStack_895_; lean_object* v_lhsPrec_896_; lean_object* v_pos_897_; lean_object* v_cache_898_; lean_object* v_errorMsg_899_; lean_object* v_recoveredErrors_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_toPure_884_);
v_stxStack_895_ = lean_ctor_get(v_s_890_, 0);
v_lhsPrec_896_ = lean_ctor_get(v_s_890_, 1);
v_pos_897_ = lean_ctor_get(v_s_890_, 2);
v_cache_898_ = lean_ctor_get(v_s_890_, 3);
v_errorMsg_899_ = lean_ctor_get(v_s_890_, 4);
v_recoveredErrors_900_ = lean_ctor_get(v_s_890_, 5);
v_isSharedCheck_937_ = !lean_is_exclusive(v_s_890_);
if (v_isSharedCheck_937_ == 0)
{
v___x_902_ = v_s_890_;
v_isShared_903_ = v_isSharedCheck_937_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_recoveredErrors_900_);
lean_inc(v_errorMsg_899_);
lean_inc(v_cache_898_);
lean_inc(v_pos_897_);
lean_inc(v_lhsPrec_896_);
lean_inc(v_stxStack_895_);
lean_dec(v_s_890_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_937_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___y_906_; 
lean_inc(v_pos_879_);
v___x_904_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_878_, v_pos_879_, v_str_880_, v_pos_897_);
if (lean_obj_tag(v_errorMsg_899_) == 0)
{
lean_dec(v_pos_879_);
v___y_906_ = v_errorMsg_899_;
goto v___jp_905_;
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_936_; 
v_val_918_ = lean_ctor_get(v_errorMsg_899_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_errorMsg_899_);
if (v_isSharedCheck_936_ == 0)
{
v___x_920_ = v_errorMsg_899_;
v_isShared_921_ = v_isSharedCheck_936_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_val_918_);
lean_dec(v_errorMsg_899_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_936_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_unexpectedTk_922_; lean_object* v_unexpected_923_; lean_object* v_expected_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_935_; 
v_unexpectedTk_922_ = lean_ctor_get(v_val_918_, 0);
v_unexpected_923_ = lean_ctor_get(v_val_918_, 1);
v_expected_924_ = lean_ctor_get(v_val_918_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_val_918_);
if (v_isSharedCheck_935_ == 0)
{
v___x_926_ = v_val_918_;
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_expected_924_);
lean_inc(v_unexpected_923_);
lean_inc(v_unexpectedTk_922_);
lean_dec(v_val_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_935_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_878_, v_pos_879_, v_str_880_, v_unexpectedTk_922_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_unexpected_923_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_expected_924_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_930_);
v___x_932_ = v___x_920_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
v___y_906_ = v___x_932_;
goto v___jp_905_;
}
}
}
}
}
v___jp_905_:
{
lean_object* v___x_907_; size_t v_sz_908_; size_t v___x_909_; lean_object* v___x_910_; lean_object* v_s_912_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v_sz_908_ = lean_array_size(v_recoveredErrors_900_);
v___x_909_ = ((size_t)0ULL);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_907_, v___f_881_, v_sz_908_, v___x_909_, v_recoveredErrors_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 5, v___x_910_);
lean_ctor_set(v___x_902_, 4, v___y_906_);
lean_ctor_set(v___x_902_, 2, v___x_904_);
v_s_912_ = v___x_902_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_stxStack_895_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_lhsPrec_896_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_cache_898_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v___y_906_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v___x_910_);
v_s_912_ = v_reuseFailAlloc_917_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_913_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_876_, v_s_912_);
v___x_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = l_Lean_MessageData_ofFormat(v___x_914_);
v___x_916_ = l_Lean_throwError___redArg(v_inst_882_, v_inst_883_, v___x_915_);
return v___x_916_;
}
}
}
}
else
{
lean_object* v_stxStack_938_; lean_object* v_pos_939_; uint8_t v___x_940_; 
lean_dec_ref(v___f_881_);
v_stxStack_938_ = lean_ctor_get(v_s_890_, 0);
v_pos_939_ = lean_ctor_get(v_s_890_, 2);
v___x_940_ = l_Lean_Parser_InputContext_atEnd(v_ictx_876_, v_pos_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_toPure_884_);
lean_dec(v_pos_879_);
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_942_ = l_Lean_Parser_ParserState_mkError(v_s_890_, v___x_941_);
v___x_943_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_876_, v___x_942_);
v___x_944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___x_945_ = l_Lean_MessageData_ofFormat(v___x_944_);
v___x_946_ = l_Lean_throwError___redArg(v_inst_882_, v_inst_883_, v___x_945_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc_ref(v_stxStack_938_);
lean_dec_ref(v_s_890_);
lean_dec_ref(v_inst_883_);
lean_dec_ref(v_inst_882_);
lean_dec_ref(v_ictx_876_);
v___x_947_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_938_);
lean_dec_ref(v_stxStack_938_);
v___x_948_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_878_, v_pos_879_, v_str_880_, v___x_947_);
v___x_949_ = lean_apply_2(v_toPure_884_, lean_box(0), v___x_948_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_env_950_, lean_object* v_p_951_, lean_object* v_ictx_952_, lean_object* v_s_953_, lean_object* v_text_954_, lean_object* v_pos_955_, lean_object* v_str_956_, lean_object* v___f_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_toPure_960_, lean_object* v_____do__lift_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_env_950_, v_p_951_, v_ictx_952_, v_s_953_, v_text_954_, v_pos_955_, v_str_956_, v___f_957_, v_inst_958_, v_inst_959_, v_toPure_960_, v_____do__lift_961_);
lean_dec_ref(v_str_956_);
lean_dec_ref(v_text_954_);
return v_res_962_;
}
}
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_963_, lean_object* v_str_964_, uint8_t v___x_965_, lean_object* v_env_966_, lean_object* v_p_967_, lean_object* v_text_968_, lean_object* v_pos_969_, lean_object* v___f_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_toPure_973_, lean_object* v_toBind_974_, lean_object* v_____do__lift_975_){
_start:
{
lean_object* v_getOptions_976_; lean_object* v___x_977_; lean_object* v_ictx_978_; lean_object* v_s_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v_getOptions_976_ = lean_ctor_get(v_inst_963_, 0);
lean_inc(v_getOptions_976_);
lean_dec_ref(v_inst_963_);
v___x_977_ = lean_string_utf8_byte_size(v_str_964_);
lean_inc_ref(v_str_964_);
v_ictx_978_ = l_Lean_Parser_mkInputContext___redArg(v_str_964_, v_____do__lift_975_, v___x_965_, v___x_977_);
v_s_979_ = l_Lean_Parser_mkParserState(v_str_964_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_980_, 0, v_env_966_);
lean_closure_set(v___f_980_, 1, v_p_967_);
lean_closure_set(v___f_980_, 2, v_ictx_978_);
lean_closure_set(v___f_980_, 3, v_s_979_);
lean_closure_set(v___f_980_, 4, v_text_968_);
lean_closure_set(v___f_980_, 5, v_pos_969_);
lean_closure_set(v___f_980_, 6, v_str_964_);
lean_closure_set(v___f_980_, 7, v___f_970_);
lean_closure_set(v___f_980_, 8, v_inst_971_);
lean_closure_set(v___f_980_, 9, v_inst_972_);
lean_closure_set(v___f_980_, 10, v_toPure_973_);
v___x_981_ = lean_apply_4(v_toBind_974_, lean_box(0), lean_box(0), v_getOptions_976_, v___f_980_);
return v___x_981_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseQuotedStrLit___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_963_ = stack[0].m_obj;
lean_object* v_str_964_ = stack[1].m_obj;
uint8_t v___x_965_ = stack[2].m_num;
lean_object* v_env_966_ = stack[3].m_obj;
lean_object* v_p_967_ = stack[4].m_obj;
lean_object* v_text_968_ = stack[5].m_obj;
lean_object* v_pos_969_ = stack[6].m_obj;
lean_object* v___f_970_ = stack[7].m_obj;
lean_object* v_inst_971_ = stack[8].m_obj;
lean_object* v_inst_972_ = stack[9].m_obj;
lean_object* v_toPure_973_ = stack[10].m_obj;
lean_object* v_toBind_974_ = stack[11].m_obj;
lean_object* v_____do__lift_975_ = stack[12].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_963_, v_str_964_, v___x_965_, v_env_966_, v_p_967_, v_text_968_, v_pos_969_, v___f_970_, v_inst_971_, v_inst_972_, v_toPure_973_, v_toBind_974_, v_____do__lift_975_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_983_, lean_object* v_str_984_, lean_object* v___x_985_, lean_object* v_env_986_, lean_object* v_p_987_, lean_object* v_text_988_, lean_object* v_pos_989_, lean_object* v___f_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_toPure_993_, lean_object* v_toBind_994_, lean_object* v_____do__lift_995_){
_start:
{
uint8_t v___x_1116__boxed_996_; lean_object* v_res_997_; 
v___x_1116__boxed_996_ = lean_unbox(v___x_985_);
v_res_997_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_983_, v_str_984_, v___x_1116__boxed_996_, v_env_986_, v_p_987_, v_text_988_, v_pos_989_, v___f_990_, v_inst_991_, v_inst_992_, v_toPure_993_, v_toBind_994_, v_____do__lift_995_);
return v_res_997_;
}
}
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v_inst_998_, lean_object* v_strLit_999_, lean_object* v_text_1000_, lean_object* v_inst_1001_, uint8_t v___x_1002_, lean_object* v_env_1003_, lean_object* v_p_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_toPure_1007_, lean_object* v_toBind_1008_, lean_object* v_pos_1009_){
_start:
{
lean_object* v_getFileName_1010_; lean_object* v_str_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
v_getFileName_1010_ = lean_ctor_get(v_inst_998_, 2);
lean_inc(v_getFileName_1010_);
lean_dec_ref(v_inst_998_);
v_str_1011_ = l_Lean_TSyntax_getString(v_strLit_999_);
lean_inc_ref(v_str_1011_);
lean_inc(v_pos_1009_);
lean_inc_ref(v_text_1000_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1012_, 0, v_text_1000_);
lean_closure_set(v___f_1012_, 1, v_pos_1009_);
lean_closure_set(v___f_1012_, 2, v_str_1011_);
v___x_1013_ = lean_box(v___x_1002_);
lean_inc(v_toBind_1008_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_1014_, 0, v_inst_1001_);
lean_closure_set(v___f_1014_, 1, v_str_1011_);
lean_closure_set(v___f_1014_, 2, v___x_1013_);
lean_closure_set(v___f_1014_, 3, v_env_1003_);
lean_closure_set(v___f_1014_, 4, v_p_1004_);
lean_closure_set(v___f_1014_, 5, v_text_1000_);
lean_closure_set(v___f_1014_, 6, v_pos_1009_);
lean_closure_set(v___f_1014_, 7, v___f_1012_);
lean_closure_set(v___f_1014_, 8, v_inst_1005_);
lean_closure_set(v___f_1014_, 9, v_inst_1006_);
lean_closure_set(v___f_1014_, 10, v_toPure_1007_);
lean_closure_set(v___f_1014_, 11, v_toBind_1008_);
v___x_1015_ = lean_apply_4(v_toBind_1008_, lean_box(0), lean_box(0), v_getFileName_1010_, v___f_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseQuotedStrLit___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_998_ = stack[0].m_obj;
lean_object* v_strLit_999_ = stack[1].m_obj;
lean_object* v_text_1000_ = stack[2].m_obj;
lean_object* v_inst_1001_ = stack[3].m_obj;
uint8_t v___x_1002_ = stack[4].m_num;
lean_object* v_env_1003_ = stack[5].m_obj;
lean_object* v_p_1004_ = stack[6].m_obj;
lean_object* v_inst_1005_ = stack[7].m_obj;
lean_object* v_inst_1006_ = stack[8].m_obj;
lean_object* v_toPure_1007_ = stack[9].m_obj;
lean_object* v_toBind_1008_ = stack[10].m_obj;
lean_object* v_pos_1009_ = stack[11].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_998_, v_strLit_999_, v_text_1000_, v_inst_1001_, v___x_1002_, v_env_1003_, v_p_1004_, v_inst_1005_, v_inst_1006_, v_toPure_1007_, v_toBind_1008_, v_pos_1009_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object* v_inst_1017_, lean_object* v_strLit_1018_, lean_object* v_text_1019_, lean_object* v_inst_1020_, lean_object* v___x_1021_, lean_object* v_env_1022_, lean_object* v_p_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_toPure_1026_, lean_object* v_toBind_1027_, lean_object* v_pos_1028_){
_start:
{
uint8_t v___x_1156__boxed_1029_; lean_object* v_res_1030_; 
v___x_1156__boxed_1029_ = lean_unbox(v___x_1021_);
v_res_1030_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_1017_, v_strLit_1018_, v_text_1019_, v_inst_1020_, v___x_1156__boxed_1029_, v_env_1022_, v_p_1023_, v_inst_1024_, v_inst_1025_, v_toPure_1026_, v_toBind_1027_, v_pos_1028_);
lean_dec(v_strLit_1018_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_1031_, lean_object* v_pos_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_apply_1(v___f_1031_, v_pos_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_text_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_strLit_1040_, lean_object* v_toBind_1041_, lean_object* v___f_1042_, lean_object* v_toPure_1043_, lean_object* v___f_1044_, lean_object* v_____r_1045_, lean_object* v_pos_1046_){
_start:
{
lean_object* v_source_1047_; uint32_t v___x_1048_; uint32_t v___x_1049_; uint8_t v___x_1050_; 
v_source_1047_ = lean_ctor_get(v_text_1037_, 0);
v___x_1048_ = lean_string_utf8_get(v_source_1047_, v_pos_1046_);
v___x_1049_ = 34;
v___x_1050_ = lean_uint32_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v___f_1044_);
lean_dec(v_toPure_1043_);
v___x_1051_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1);
v___x_1052_ = l_Lean_throwErrorAt___redArg(v_inst_1038_, v_inst_1039_, v_strLit_1040_, v___x_1051_);
v___x_1053_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v___x_1052_, v___f_1042_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec(v___f_1042_);
lean_dec(v_strLit_1040_);
lean_dec_ref(v_inst_1039_);
lean_dec_ref(v_inst_1038_);
v___x_1054_ = lean_string_utf8_next(v_source_1047_, v_pos_1046_);
v___x_1055_ = lean_apply_2(v_toPure_1043_, lean_box(0), v___x_1054_);
v___x_1056_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v___x_1055_, v___f_1044_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_text_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_strLit_1060_, lean_object* v_toBind_1061_, lean_object* v___f_1062_, lean_object* v_toPure_1063_, lean_object* v___f_1064_, lean_object* v_____r_1065_, lean_object* v_pos_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_text_1057_, v_inst_1058_, v_inst_1059_, v_strLit_1060_, v_toBind_1061_, v___f_1062_, v_toPure_1063_, v___f_1064_, v_____r_1065_, v_pos_1066_);
lean_dec(v_pos_1066_);
lean_dec_ref(v_text_1057_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v___f_1068_, lean_object* v_____s_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_apply_2(v___f_1068_, v___x_1070_, v_____s_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_1072_, lean_object* v_toPure_1073_, lean_object* v_toBind_1074_, lean_object* v___f_1075_, lean_object* v_b_1076_){
_start:
{
uint32_t v___x_1077_; uint32_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_string_utf8_get(v_source_1072_, v_b_1076_);
v___x_1078_ = 35;
v___x_1079_ = lean_uint32_dec_eq(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_b_1076_);
v___x_1081_ = lean_apply_2(v_toPure_1073_, lean_box(0), v___x_1080_);
v___x_1082_ = lean_apply_4(v_toBind_1074_, lean_box(0), lean_box(0), v___x_1081_, v___f_1075_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = lean_string_utf8_next(v_source_1072_, v_b_1076_);
lean_dec(v_b_1076_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = lean_apply_2(v_toPure_1073_, lean_box(0), v___x_1084_);
v___x_1086_ = lean_apply_4(v_toBind_1074_, lean_box(0), lean_box(0), v___x_1085_, v___f_1075_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_1087_, lean_object* v_toPure_1088_, lean_object* v_toBind_1089_, lean_object* v___f_1090_, lean_object* v_b_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_1087_, v_toPure_1088_, v_toBind_1089_, v___f_1090_, v_b_1091_);
lean_dec_ref(v_source_1087_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_1093_, lean_object* v___f_1094_, lean_object* v_toPure_1095_, lean_object* v_toBind_1096_, lean_object* v___f_1097_, lean_object* v_inst_1098_, lean_object* v___f_1099_, lean_object* v_____x_1100_){
_start:
{
lean_object* v_start_1101_; lean_object* v_source_1102_; uint32_t v___x_1103_; uint32_t v___x_1104_; uint8_t v___x_1105_; 
v_start_1101_ = lean_ctor_get(v_____x_1100_, 0);
lean_inc(v_start_1101_);
lean_dec_ref(v_____x_1100_);
v_source_1102_ = lean_ctor_get(v_text_1093_, 0);
lean_inc_ref(v_source_1102_);
lean_dec_ref(v_text_1093_);
v___x_1103_ = lean_string_utf8_get(v_source_1102_, v_start_1101_);
v___x_1104_ = 114;
v___x_1105_ = lean_uint32_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_source_1102_);
lean_dec(v___f_1099_);
lean_dec_ref(v_inst_1098_);
lean_dec(v___f_1097_);
lean_dec(v_toBind_1096_);
lean_dec(v_toPure_1095_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_apply_2(v___f_1094_, v___x_1106_, v_start_1101_);
return v___x_1107_;
}
else
{
lean_object* v___f_1108_; lean_object* v_pos_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v___f_1094_);
lean_inc(v_toBind_1096_);
lean_inc_ref(v_source_1102_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_1108_, 0, v_source_1102_);
lean_closure_set(v___f_1108_, 1, v_toPure_1095_);
lean_closure_set(v___f_1108_, 2, v_toBind_1096_);
lean_closure_set(v___f_1108_, 3, v___f_1097_);
v_pos_1109_ = lean_string_utf8_next(v_source_1102_, v_start_1101_);
lean_dec(v_start_1101_);
lean_dec_ref(v_source_1102_);
v___x_1110_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_1098_, v___f_1108_, v_pos_1109_);
v___x_1111_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1110_, v___f_1099_);
return v___x_1111_;
}
}
}
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_1112_, lean_object* v_strLit_1113_, lean_object* v_text_1114_, lean_object* v_inst_1115_, uint8_t v___x_1116_, lean_object* v_p_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_toPure_1120_, lean_object* v_toBind_1121_, lean_object* v___f_1122_, lean_object* v_env_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1124_ = lean_box(v___x_1116_);
lean_inc_n(v_toBind_1121_, 3);
lean_inc_n(v_toPure_1120_, 2);
lean_inc_ref(v_inst_1119_);
lean_inc_ref_n(v_inst_1118_, 3);
lean_inc_ref_n(v_text_1114_, 2);
lean_inc_n(v_strLit_1113_, 2);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1125_, 0, v_inst_1112_);
lean_closure_set(v___f_1125_, 1, v_strLit_1113_);
lean_closure_set(v___f_1125_, 2, v_text_1114_);
lean_closure_set(v___f_1125_, 3, v_inst_1115_);
lean_closure_set(v___f_1125_, 4, v___x_1124_);
lean_closure_set(v___f_1125_, 5, v_env_1123_);
lean_closure_set(v___f_1125_, 6, v_p_1117_);
lean_closure_set(v___f_1125_, 7, v_inst_1118_);
lean_closure_set(v___f_1125_, 8, v_inst_1119_);
lean_closure_set(v___f_1125_, 9, v_toPure_1120_);
lean_closure_set(v___f_1125_, 10, v_toBind_1121_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1126_, 0, v___f_1125_);
lean_inc_ref(v___f_1126_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_1127_, 0, v_text_1114_);
lean_closure_set(v___f_1127_, 1, v_inst_1118_);
lean_closure_set(v___f_1127_, 2, v_inst_1119_);
lean_closure_set(v___f_1127_, 3, v_strLit_1113_);
lean_closure_set(v___f_1127_, 4, v_toBind_1121_);
lean_closure_set(v___f_1127_, 5, v___f_1126_);
lean_closure_set(v___f_1127_, 6, v_toPure_1120_);
lean_closure_set(v___f_1127_, 7, v___f_1126_);
lean_inc_ref(v___f_1127_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1128_, 0, v___f_1127_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 8, 7);
lean_closure_set(v___f_1129_, 0, v_text_1114_);
lean_closure_set(v___f_1129_, 1, v___f_1127_);
lean_closure_set(v___f_1129_, 2, v_toPure_1120_);
lean_closure_set(v___f_1129_, 3, v_toBind_1121_);
lean_closure_set(v___f_1129_, 4, v___f_1122_);
lean_closure_set(v___f_1129_, 5, v_inst_1118_);
lean_closure_set(v___f_1129_, 6, v___f_1128_);
v___x_1130_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_1118_, v_strLit_1113_);
lean_dec(v_strLit_1113_);
v___x_1131_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1130_, v___f_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseQuotedStrLit___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1112_ = stack[0].m_obj;
lean_object* v_strLit_1113_ = stack[1].m_obj;
lean_object* v_text_1114_ = stack[2].m_obj;
lean_object* v_inst_1115_ = stack[3].m_obj;
uint8_t v___x_1116_ = stack[4].m_num;
lean_object* v_p_1117_ = stack[5].m_obj;
lean_object* v_inst_1118_ = stack[6].m_obj;
lean_object* v_inst_1119_ = stack[7].m_obj;
lean_object* v_toPure_1120_ = stack[8].m_obj;
lean_object* v_toBind_1121_ = stack[9].m_obj;
lean_object* v___f_1122_ = stack[10].m_obj;
lean_object* v_env_1123_ = stack[11].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_1112_, v_strLit_1113_, v_text_1114_, v_inst_1115_, v___x_1116_, v_p_1117_, v_inst_1118_, v_inst_1119_, v_toPure_1120_, v_toBind_1121_, v___f_1122_, v_env_1123_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_1133_, lean_object* v_strLit_1134_, lean_object* v_text_1135_, lean_object* v_inst_1136_, lean_object* v___x_1137_, lean_object* v_p_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_toPure_1141_, lean_object* v_toBind_1142_, lean_object* v___f_1143_, lean_object* v_env_1144_){
_start:
{
uint8_t v___x_1352__boxed_1145_; lean_object* v_res_1146_; 
v___x_1352__boxed_1145_ = lean_unbox(v___x_1137_);
v_res_1146_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_1133_, v_strLit_1134_, v_text_1135_, v_inst_1136_, v___x_1352__boxed_1145_, v_p_1138_, v_inst_1139_, v_inst_1140_, v_toPure_1141_, v_toBind_1142_, v___f_1143_, v_env_1144_);
return v_res_1146_;
}
}
lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_strLit_1149_, lean_object* v_inst_1150_, uint8_t v___x_1151_, lean_object* v_p_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_toPure_1155_, lean_object* v_toBind_1156_, lean_object* v___f_1157_, lean_object* v_text_1158_){
_start:
{
lean_object* v_getEnv_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; 
v_getEnv_1159_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc(v_getEnv_1159_);
lean_dec_ref(v_inst_1147_);
v___x_1160_ = lean_box(v___x_1151_);
lean_inc(v_toBind_1156_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_1161_, 0, v_inst_1148_);
lean_closure_set(v___f_1161_, 1, v_strLit_1149_);
lean_closure_set(v___f_1161_, 2, v_text_1158_);
lean_closure_set(v___f_1161_, 3, v_inst_1150_);
lean_closure_set(v___f_1161_, 4, v___x_1160_);
lean_closure_set(v___f_1161_, 5, v_p_1152_);
lean_closure_set(v___f_1161_, 6, v_inst_1153_);
lean_closure_set(v___f_1161_, 7, v_inst_1154_);
lean_closure_set(v___f_1161_, 8, v_toPure_1155_);
lean_closure_set(v___f_1161_, 9, v_toBind_1156_);
lean_closure_set(v___f_1161_, 10, v___f_1157_);
v___x_1162_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v_getEnv_1159_, v___f_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseQuotedStrLit___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1147_ = stack[0].m_obj;
lean_object* v_inst_1148_ = stack[1].m_obj;
lean_object* v_strLit_1149_ = stack[2].m_obj;
lean_object* v_inst_1150_ = stack[3].m_obj;
uint8_t v___x_1151_ = stack[4].m_num;
lean_object* v_p_1152_ = stack[5].m_obj;
lean_object* v_inst_1153_ = stack[6].m_obj;
lean_object* v_inst_1154_ = stack[7].m_obj;
lean_object* v_toPure_1155_ = stack[8].m_obj;
lean_object* v_toBind_1156_ = stack[9].m_obj;
lean_object* v___f_1157_ = stack[10].m_obj;
lean_object* v_text_1158_ = stack[11].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_1147_, v_inst_1148_, v_strLit_1149_, v_inst_1150_, v___x_1151_, v_p_1152_, v_inst_1153_, v_inst_1154_, v_toPure_1155_, v_toBind_1156_, v___f_1157_, v_text_1158_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_strLit_1166_, lean_object* v_inst_1167_, lean_object* v___x_1168_, lean_object* v_p_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_toPure_1172_, lean_object* v_toBind_1173_, lean_object* v___f_1174_, lean_object* v_text_1175_){
_start:
{
uint8_t v___x_1407__boxed_1176_; lean_object* v_res_1177_; 
v___x_1407__boxed_1176_ = lean_unbox(v___x_1168_);
v_res_1177_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_1164_, v_inst_1165_, v_strLit_1166_, v_inst_1167_, v___x_1407__boxed_1176_, v_p_1169_, v_inst_1170_, v_inst_1171_, v_toPure_1172_, v_toBind_1173_, v___f_1174_, v_text_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_p_1184_, lean_object* v_strLit_1185_){
_start:
{
uint8_t v___x_1186_; uint8_t v___y_1188_; lean_object* v___x_1198_; 
v___x_1186_ = 1;
v___x_1198_ = l_Lean_Syntax_getPos_x3f(v_strLit_1185_, v___x_1186_);
if (lean_obj_tag(v___x_1198_) == 0)
{
v___y_1188_ = v___x_1186_;
goto v___jp_1187_;
}
else
{
uint8_t v___x_1199_; 
lean_dec_ref_known(v___x_1198_, 1);
v___x_1199_ = 0;
v___y_1188_ = v___x_1199_;
goto v___jp_1187_;
}
v___jp_1187_:
{
if (v___y_1188_ == 0)
{
lean_object* v_toApplicative_1189_; lean_object* v_toBind_1190_; lean_object* v_toPure_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v_toApplicative_1189_ = lean_ctor_get(v_inst_1178_, 0);
v_toBind_1190_ = lean_ctor_get(v_inst_1178_, 1);
lean_inc_n(v_toBind_1190_, 2);
v_toPure_1191_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_inc_n(v_toPure_1191_, 2);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1192_, 0, v_toPure_1191_);
v___x_1193_ = lean_box(v___x_1186_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 12, 11);
lean_closure_set(v___f_1194_, 0, v_inst_1180_);
lean_closure_set(v___f_1194_, 1, v_inst_1182_);
lean_closure_set(v___f_1194_, 2, v_strLit_1185_);
lean_closure_set(v___f_1194_, 3, v_inst_1183_);
lean_closure_set(v___f_1194_, 4, v___x_1193_);
lean_closure_set(v___f_1194_, 5, v_p_1184_);
lean_closure_set(v___f_1194_, 6, v_inst_1178_);
lean_closure_set(v___f_1194_, 7, v_inst_1181_);
lean_closure_set(v___f_1194_, 8, v_toPure_1191_);
lean_closure_set(v___f_1194_, 9, v_toBind_1190_);
lean_closure_set(v___f_1194_, 10, v___f_1192_);
v___x_1195_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v_inst_1179_, v___f_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_inst_1179_);
v___x_1196_ = l_Lean_TSyntax_getString(v_strLit_1185_);
lean_dec(v_strLit_1185_);
v___x_1197_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_1178_, v_inst_1180_, v_inst_1181_, v_inst_1182_, v_inst_1183_, v_p_1184_, v___x_1196_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_p_1207_, lean_object* v_strLit_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_inst_1205_, v_inst_1206_, v_p_1207_, v_strLit_1208_);
return v___x_1209_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object* v_s_1210_, lean_object* v_toPure_1211_, uint8_t v_err_1212_){
_start:
{
lean_object* v_stxStack_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_stxStack_1213_ = lean_ctor_get(v_s_1210_, 0);
v___x_1214_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1213_);
v___x_1215_ = lean_box(v_err_1212_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_apply_2(v_toPure_1211_, lean_box(0), v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1210_ = stack[0].m_obj;
lean_object* v_toPure_1211_ = stack[1].m_obj;
uint8_t v_err_1212_ = stack[2].m_num;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_Doc_parseContent_x27___redArg___lam__0(v_s_1210_, v_toPure_1211_, v_err_1212_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object* v_s_1219_, lean_object* v_toPure_1220_, lean_object* v_err_1221_){
_start:
{
uint8_t v_err_boxed_1222_; lean_object* v_res_1223_; 
v_err_boxed_1222_ = lean_unbox(v_err_1221_);
v_res_1223_ = l_Lean_Doc_parseContent_x27___redArg___lam__0(v_s_1219_, v_toPure_1220_, v_err_boxed_1222_);
lean_dec_ref(v_s_1219_);
return v_res_1223_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object* v___f_1224_, uint8_t v_err_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(v_err_1225_);
v___x_1227_ = lean_apply_1(v___f_1224_, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1224_ = stack[0].m_obj;
uint8_t v_err_1225_ = stack[1].m_num;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_Doc_parseContent_x27___redArg___lam__1(v___f_1224_, v_err_1225_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object* v___f_1229_, lean_object* v_err_1230_){
_start:
{
uint8_t v_err_boxed_1231_; lean_object* v_res_1232_; 
v_err_boxed_1231_ = lean_unbox(v_err_1230_);
v_res_1232_ = l_Lean_Doc_parseContent_x27___redArg___lam__1(v___f_1229_, v_err_boxed_1231_);
return v_res_1232_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object* v_toPure_1233_, uint8_t v___x_1234_, lean_object* v_toBind_1235_, lean_object* v___f_1236_, lean_object* v_____r_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_box(v___x_1234_);
v___x_1239_ = lean_apply_2(v_toPure_1233_, lean_box(0), v___x_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1235_, lean_box(0), lean_box(0), v___x_1239_, v___f_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1233_ = stack[0].m_obj;
uint8_t v___x_1234_ = stack[1].m_num;
lean_object* v_toBind_1235_ = stack[2].m_obj;
lean_object* v___f_1236_ = stack[3].m_obj;
lean_object* v_____r_1237_ = stack[4].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l_Lean_Doc_parseContent_x27___redArg___lam__2(v_toPure_1233_, v___x_1234_, v_toBind_1235_, v___f_1236_, v_____r_1237_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object* v_toPure_1242_, lean_object* v___x_1243_, lean_object* v_toBind_1244_, lean_object* v___f_1245_, lean_object* v_____r_1246_){
_start:
{
uint8_t v___x_806__boxed_1247_; lean_object* v_res_1248_; 
v___x_806__boxed_1247_ = lean_unbox(v___x_1243_);
v_res_1248_ = l_Lean_Doc_parseContent_x27___redArg___lam__2(v_toPure_1242_, v___x_806__boxed_1247_, v_toBind_1244_, v___f_1245_, v_____r_1246_);
return v_res_1248_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object* v_env_1249_, lean_object* v_p_1250_, lean_object* v_ictx_1251_, lean_object* v_s_1252_, lean_object* v_toPure_1253_, uint8_t v___x_1254_, lean_object* v_toBind_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, uint8_t v___y_1260_, lean_object* v_____do__lift_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_s_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_box(0);
lean_inc_ref(v_env_1249_);
v___x_1264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1264_, 0, v_env_1249_);
lean_ctor_set(v___x_1264_, 1, v_____do__lift_1261_);
lean_ctor_set(v___x_1264_, 2, v___x_1262_);
lean_ctor_set(v___x_1264_, 3, v___x_1263_);
v___x_1265_ = l_Lean_Parser_getTokenTable(v_env_1249_);
lean_inc_ref(v_ictx_1251_);
v_s_1266_ = l_Lean_Parser_ParserFn_run(v_p_1250_, v_ictx_1251_, v___x_1264_, v___x_1265_, v_s_1252_);
lean_inc(v_toPure_1253_);
lean_inc_ref_n(v_s_1266_, 2);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1267_, 0, v_s_1266_);
lean_closure_set(v___f_1267_, 1, v_toPure_1253_);
v___x_1268_ = l_Lean_Parser_ParserState_allErrors(v_s_1266_);
v___x_1269_ = lean_array_get_size(v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_nat_dec_eq(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1272_, 0, v___f_1267_);
v___x_1273_ = lean_box(v___x_1254_);
lean_inc(v_toBind_1255_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1274_, 0, v_toPure_1253_);
lean_closure_set(v___f_1274_, 1, v___x_1273_);
lean_closure_set(v___f_1274_, 2, v_toBind_1255_);
lean_closure_set(v___f_1274_, 3, v___f_1272_);
v___x_1275_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1251_, v_s_1266_);
v___x_1276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
v___x_1277_ = l_Lean_MessageData_ofFormat(v___x_1276_);
v___x_1278_ = l_Lean_logError___redArg(v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v___x_1277_);
v___x_1279_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1278_, v___f_1274_);
return v___x_1279_;
}
else
{
lean_object* v_pos_1280_; uint8_t v___x_1281_; 
v_pos_1280_ = lean_ctor_get(v_s_1266_, 2);
v___x_1281_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1251_, v_pos_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1282_, 0, v___f_1267_);
v___x_1283_ = lean_box(v___x_1254_);
lean_inc(v_toBind_1255_);
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1284_, 0, v_toPure_1253_);
lean_closure_set(v___f_1284_, 1, v___x_1283_);
lean_closure_set(v___f_1284_, 2, v_toBind_1255_);
lean_closure_set(v___f_1284_, 3, v___f_1282_);
v___x_1285_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1286_ = l_Lean_Parser_ParserState_mkError(v_s_1266_, v___x_1285_);
v___x_1287_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1251_, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
v___x_1289_ = l_Lean_MessageData_ofFormat(v___x_1288_);
v___x_1290_ = l_Lean_logError___redArg(v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v___x_1289_);
v___x_1291_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1290_, v___f_1284_);
return v___x_1291_;
}
else
{
lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_s_1266_);
lean_dec_ref(v_inst_1259_);
lean_dec(v_inst_1258_);
lean_dec_ref(v_inst_1257_);
lean_dec_ref(v_inst_1256_);
lean_dec_ref(v_ictx_1251_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1292_, 0, v___f_1267_);
v___x_1293_ = lean_box(v___y_1260_);
v___x_1294_ = lean_apply_2(v_toPure_1253_, lean_box(0), v___x_1293_);
v___x_1295_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1294_, v___f_1292_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1249_ = stack[0].m_obj;
lean_object* v_p_1250_ = stack[1].m_obj;
lean_object* v_ictx_1251_ = stack[2].m_obj;
lean_object* v_s_1252_ = stack[3].m_obj;
lean_object* v_toPure_1253_ = stack[4].m_obj;
uint8_t v___x_1254_ = stack[5].m_num;
lean_object* v_toBind_1255_ = stack[6].m_obj;
lean_object* v_inst_1256_ = stack[7].m_obj;
lean_object* v_inst_1257_ = stack[8].m_obj;
lean_object* v_inst_1258_ = stack[9].m_obj;
lean_object* v_inst_1259_ = stack[10].m_obj;
uint8_t v___y_1260_ = stack[11].m_num;
lean_object* v_____do__lift_1261_ = stack[12].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_Doc_parseContent_x27___redArg___lam__6(v_env_1249_, v_p_1250_, v_ictx_1251_, v_s_1252_, v_toPure_1253_, v___x_1254_, v_toBind_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v___y_1260_, v_____do__lift_1261_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object* v_env_1297_, lean_object* v_p_1298_, lean_object* v_ictx_1299_, lean_object* v_s_1300_, lean_object* v_toPure_1301_, lean_object* v___x_1302_, lean_object* v_toBind_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v___y_1308_, lean_object* v_____do__lift_1309_){
_start:
{
uint8_t v___x_831__boxed_1310_; uint8_t v___y_836__boxed_1311_; lean_object* v_res_1312_; 
v___x_831__boxed_1310_ = lean_unbox(v___x_1302_);
v___y_836__boxed_1311_ = lean_unbox(v___y_1308_);
v_res_1312_ = l_Lean_Doc_parseContent_x27___redArg___lam__6(v_env_1297_, v_p_1298_, v_ictx_1299_, v_s_1300_, v_toPure_1301_, v___x_831__boxed_1310_, v_toBind_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v___y_836__boxed_1311_, v_____do__lift_1309_);
return v_res_1312_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object* v_source_1313_, uint8_t v___x_1314_, lean_object* v___y_1315_, lean_object* v_inst_1316_, lean_object* v_env_1317_, lean_object* v_p_1318_, lean_object* v_toPure_1319_, lean_object* v_toBind_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, uint8_t v___y_1324_, lean_object* v_tok_1325_, lean_object* v___x_1326_, lean_object* v_____do__lift_1327_){
_start:
{
lean_object* v_ictx_1328_; lean_object* v___x_1329_; lean_object* v___y_1331_; lean_object* v___x_1338_; 
lean_inc_ref(v_source_1313_);
v_ictx_1328_ = l_Lean_Parser_mkInputContext___redArg(v_source_1313_, v_____do__lift_1327_, v___x_1314_, v___y_1315_);
v___x_1329_ = l_Lean_Parser_mkParserState(v_source_1313_);
lean_dec_ref(v_source_1313_);
v___x_1338_ = l_Lean_Syntax_getPos_x3f(v_tok_1325_, v___x_1314_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1340_ = l_panic___redArg(v___x_1326_, v___x_1339_);
v___y_1331_ = v___x_1340_;
goto v___jp_1330_;
}
else
{
lean_object* v_val_1341_; 
v_val_1341_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v___x_1338_, 1);
v___y_1331_ = v_val_1341_;
goto v___jp_1330_;
}
v___jp_1330_:
{
lean_object* v_getOptions_1332_; lean_object* v_s_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; 
v_getOptions_1332_ = lean_ctor_get(v_inst_1316_, 0);
lean_inc(v_getOptions_1332_);
v_s_1333_ = l_Lean_Parser_ParserState_setPos(v___x_1329_, v___y_1331_);
v___x_1334_ = lean_box(v___x_1314_);
v___x_1335_ = lean_box(v___y_1324_);
lean_inc(v_toBind_1320_);
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1336_, 0, v_env_1317_);
lean_closure_set(v___f_1336_, 1, v_p_1318_);
lean_closure_set(v___f_1336_, 2, v_ictx_1328_);
lean_closure_set(v___f_1336_, 3, v_s_1333_);
lean_closure_set(v___f_1336_, 4, v_toPure_1319_);
lean_closure_set(v___f_1336_, 5, v___x_1334_);
lean_closure_set(v___f_1336_, 6, v_toBind_1320_);
lean_closure_set(v___f_1336_, 7, v_inst_1321_);
lean_closure_set(v___f_1336_, 8, v_inst_1322_);
lean_closure_set(v___f_1336_, 9, v_inst_1323_);
lean_closure_set(v___f_1336_, 10, v_inst_1316_);
lean_closure_set(v___f_1336_, 11, v___x_1335_);
v___x_1337_ = lean_apply_4(v_toBind_1320_, lean_box(0), lean_box(0), v_getOptions_1332_, v___f_1336_);
return v___x_1337_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_source_1313_ = stack[0].m_obj;
uint8_t v___x_1314_ = stack[1].m_num;
lean_object* v___y_1315_ = stack[2].m_obj;
lean_object* v_inst_1316_ = stack[3].m_obj;
lean_object* v_env_1317_ = stack[4].m_obj;
lean_object* v_p_1318_ = stack[5].m_obj;
lean_object* v_toPure_1319_ = stack[6].m_obj;
lean_object* v_toBind_1320_ = stack[7].m_obj;
lean_object* v_inst_1321_ = stack[8].m_obj;
lean_object* v_inst_1322_ = stack[9].m_obj;
lean_object* v_inst_1323_ = stack[10].m_obj;
uint8_t v___y_1324_ = stack[11].m_num;
lean_object* v_tok_1325_ = stack[12].m_obj;
lean_object* v___x_1326_ = stack[13].m_obj;
lean_object* v_____do__lift_1327_ = stack[14].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_Doc_parseContent_x27___redArg___lam__3(v_source_1313_, v___x_1314_, v___y_1315_, v_inst_1316_, v_env_1317_, v_p_1318_, v_toPure_1319_, v_toBind_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v___y_1324_, v_tok_1325_, v___x_1326_, v_____do__lift_1327_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object* v_source_1343_, lean_object* v___x_1344_, lean_object* v___y_1345_, lean_object* v_inst_1346_, lean_object* v_env_1347_, lean_object* v_p_1348_, lean_object* v_toPure_1349_, lean_object* v_toBind_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v___y_1354_, lean_object* v_tok_1355_, lean_object* v___x_1356_, lean_object* v_____do__lift_1357_){
_start:
{
uint8_t v___x_971__boxed_1358_; uint8_t v___y_977__boxed_1359_; lean_object* v_res_1360_; 
v___x_971__boxed_1358_ = lean_unbox(v___x_1344_);
v___y_977__boxed_1359_ = lean_unbox(v___y_1354_);
v_res_1360_ = l_Lean_Doc_parseContent_x27___redArg___lam__3(v_source_1343_, v___x_971__boxed_1358_, v___y_1345_, v_inst_1346_, v_env_1347_, v_p_1348_, v_toPure_1349_, v_toBind_1350_, v_inst_1351_, v_inst_1352_, v_inst_1353_, v___y_977__boxed_1359_, v_tok_1355_, v___x_1356_, v_____do__lift_1357_);
lean_dec(v___x_1356_);
lean_dec(v_tok_1355_);
return v_res_1360_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object* v_text_1361_, lean_object* v_inst_1362_, uint8_t v___x_1363_, lean_object* v_inst_1364_, lean_object* v_p_1365_, lean_object* v_toPure_1366_, lean_object* v_toBind_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, uint8_t v___y_1370_, lean_object* v_tok_1371_, lean_object* v___x_1372_, lean_object* v_env_1373_){
_start:
{
lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1383_; lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Syntax_getTailPos_x3f(v_tok_1371_, v___x_1363_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1389_ = l_panic___redArg(v___x_1372_, v___x_1388_);
v___y_1383_ = v___x_1389_;
goto v___jp_1382_;
}
else
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1387_, 1);
v___y_1383_ = v_val_1390_;
goto v___jp_1382_;
}
v___jp_1374_:
{
lean_object* v_getFileName_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; 
v_getFileName_1377_ = lean_ctor_get(v_inst_1362_, 2);
lean_inc(v_getFileName_1377_);
v___x_1378_ = lean_box(v___x_1363_);
v___x_1379_ = lean_box(v___y_1370_);
lean_inc(v_toBind_1367_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1380_, 0, v___y_1375_);
lean_closure_set(v___f_1380_, 1, v___x_1378_);
lean_closure_set(v___f_1380_, 2, v___y_1376_);
lean_closure_set(v___f_1380_, 3, v_inst_1364_);
lean_closure_set(v___f_1380_, 4, v_env_1373_);
lean_closure_set(v___f_1380_, 5, v_p_1365_);
lean_closure_set(v___f_1380_, 6, v_toPure_1366_);
lean_closure_set(v___f_1380_, 7, v_toBind_1367_);
lean_closure_set(v___f_1380_, 8, v_inst_1368_);
lean_closure_set(v___f_1380_, 9, v_inst_1362_);
lean_closure_set(v___f_1380_, 10, v_inst_1369_);
lean_closure_set(v___f_1380_, 11, v___x_1379_);
lean_closure_set(v___f_1380_, 12, v_tok_1371_);
lean_closure_set(v___f_1380_, 13, v___x_1372_);
v___x_1381_ = lean_apply_4(v_toBind_1367_, lean_box(0), lean_box(0), v_getFileName_1377_, v___f_1380_);
return v___x_1381_;
}
v___jp_1382_:
{
lean_object* v_source_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_source_1384_ = lean_ctor_get(v_text_1361_, 0);
lean_inc_ref(v_source_1384_);
lean_dec_ref(v_text_1361_);
v___x_1385_ = lean_string_utf8_byte_size(v_source_1384_);
v___x_1386_ = lean_nat_dec_le(v___y_1383_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v___y_1383_);
v___y_1375_ = v_source_1384_;
v___y_1376_ = v___x_1385_;
goto v___jp_1374_;
}
else
{
v___y_1375_ = v_source_1384_;
v___y_1376_ = v___y_1383_;
goto v___jp_1374_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_1361_ = stack[0].m_obj;
lean_object* v_inst_1362_ = stack[1].m_obj;
uint8_t v___x_1363_ = stack[2].m_num;
lean_object* v_inst_1364_ = stack[3].m_obj;
lean_object* v_p_1365_ = stack[4].m_obj;
lean_object* v_toPure_1366_ = stack[5].m_obj;
lean_object* v_toBind_1367_ = stack[6].m_obj;
lean_object* v_inst_1368_ = stack[7].m_obj;
lean_object* v_inst_1369_ = stack[8].m_obj;
uint8_t v___y_1370_ = stack[9].m_num;
lean_object* v_tok_1371_ = stack[10].m_obj;
lean_object* v___x_1372_ = stack[11].m_obj;
lean_object* v_env_1373_ = stack[12].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_Lean_Doc_parseContent_x27___redArg___lam__4(v_text_1361_, v_inst_1362_, v___x_1363_, v_inst_1364_, v_p_1365_, v_toPure_1366_, v_toBind_1367_, v_inst_1368_, v_inst_1369_, v___y_1370_, v_tok_1371_, v___x_1372_, v_env_1373_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object* v_text_1392_, lean_object* v_inst_1393_, lean_object* v___x_1394_, lean_object* v_inst_1395_, lean_object* v_p_1396_, lean_object* v_toPure_1397_, lean_object* v_toBind_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v___y_1401_, lean_object* v_tok_1402_, lean_object* v___x_1403_, lean_object* v_env_1404_){
_start:
{
uint8_t v___x_1065__boxed_1405_; uint8_t v___y_1069__boxed_1406_; lean_object* v_res_1407_; 
v___x_1065__boxed_1405_ = lean_unbox(v___x_1394_);
v___y_1069__boxed_1406_ = lean_unbox(v___y_1401_);
v_res_1407_ = l_Lean_Doc_parseContent_x27___redArg___lam__4(v_text_1392_, v_inst_1393_, v___x_1065__boxed_1405_, v_inst_1395_, v_p_1396_, v_toPure_1397_, v_toBind_1398_, v_inst_1399_, v_inst_1400_, v___y_1069__boxed_1406_, v_tok_1402_, v___x_1403_, v_env_1404_);
return v_res_1407_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object* v_inst_1408_, lean_object* v_inst_1409_, uint8_t v___x_1410_, lean_object* v_inst_1411_, lean_object* v_p_1412_, lean_object* v_toPure_1413_, lean_object* v_toBind_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, uint8_t v___y_1417_, lean_object* v_tok_1418_, lean_object* v___x_1419_, lean_object* v_text_1420_){
_start:
{
lean_object* v_getEnv_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; 
v_getEnv_1421_ = lean_ctor_get(v_inst_1408_, 0);
lean_inc(v_getEnv_1421_);
lean_dec_ref(v_inst_1408_);
v___x_1422_ = lean_box(v___x_1410_);
v___x_1423_ = lean_box(v___y_1417_);
lean_inc(v_toBind_1414_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed), 13, 12);
lean_closure_set(v___f_1424_, 0, v_text_1420_);
lean_closure_set(v___f_1424_, 1, v_inst_1409_);
lean_closure_set(v___f_1424_, 2, v___x_1422_);
lean_closure_set(v___f_1424_, 3, v_inst_1411_);
lean_closure_set(v___f_1424_, 4, v_p_1412_);
lean_closure_set(v___f_1424_, 5, v_toPure_1413_);
lean_closure_set(v___f_1424_, 6, v_toBind_1414_);
lean_closure_set(v___f_1424_, 7, v_inst_1415_);
lean_closure_set(v___f_1424_, 8, v_inst_1416_);
lean_closure_set(v___f_1424_, 9, v___x_1423_);
lean_closure_set(v___f_1424_, 10, v_tok_1418_);
lean_closure_set(v___f_1424_, 11, v___x_1419_);
v___x_1425_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v_getEnv_1421_, v___f_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1408_ = stack[0].m_obj;
lean_object* v_inst_1409_ = stack[1].m_obj;
uint8_t v___x_1410_ = stack[2].m_num;
lean_object* v_inst_1411_ = stack[3].m_obj;
lean_object* v_p_1412_ = stack[4].m_obj;
lean_object* v_toPure_1413_ = stack[5].m_obj;
lean_object* v_toBind_1414_ = stack[6].m_obj;
lean_object* v_inst_1415_ = stack[7].m_obj;
lean_object* v_inst_1416_ = stack[8].m_obj;
uint8_t v___y_1417_ = stack[9].m_num;
lean_object* v_tok_1418_ = stack[10].m_obj;
lean_object* v___x_1419_ = stack[11].m_obj;
lean_object* v_text_1420_ = stack[12].m_obj;
lean_object* v_res_1426_;
v_res_1426_ = l_Lean_Doc_parseContent_x27___redArg___lam__5(v_inst_1408_, v_inst_1409_, v___x_1410_, v_inst_1411_, v_p_1412_, v_toPure_1413_, v_toBind_1414_, v_inst_1415_, v_inst_1416_, v___y_1417_, v_tok_1418_, v___x_1419_, v_text_1420_);
stack->m_obj
 = v_res_1426_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v___x_1429_, lean_object* v_inst_1430_, lean_object* v_p_1431_, lean_object* v_toPure_1432_, lean_object* v_toBind_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v___y_1436_, lean_object* v_tok_1437_, lean_object* v___x_1438_, lean_object* v_text_1439_){
_start:
{
uint8_t v___x_1151__boxed_1440_; uint8_t v___y_1155__boxed_1441_; lean_object* v_res_1442_; 
v___x_1151__boxed_1440_ = lean_unbox(v___x_1429_);
v___y_1155__boxed_1441_ = lean_unbox(v___y_1436_);
v_res_1442_ = l_Lean_Doc_parseContent_x27___redArg___lam__5(v_inst_1427_, v_inst_1428_, v___x_1151__boxed_1440_, v_inst_1430_, v_p_1431_, v_toPure_1432_, v_toBind_1433_, v_inst_1434_, v_inst_1435_, v___y_1155__boxed_1441_, v_tok_1437_, v___x_1438_, v_text_1439_);
return v_res_1442_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object* v_st_1443_, lean_object* v_toPure_1444_, uint8_t v_err_1445_){
_start:
{
lean_object* v_stxStack_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_stxStack_1446_ = lean_ctor_get(v_st_1443_, 0);
v___x_1447_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1446_);
v___x_1448_ = lean_box(v_err_1445_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_apply_2(v_toPure_1444_, lean_box(0), v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_st_1443_ = stack[0].m_obj;
lean_object* v_toPure_1444_ = stack[1].m_obj;
uint8_t v_err_1445_ = stack[2].m_num;
lean_object* v_res_1451_;
v_res_1451_ = l_Lean_Doc_parseContent_x27___redArg___lam__7(v_st_1443_, v_toPure_1444_, v_err_1445_);
stack->m_obj
 = v_res_1451_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object* v_st_1452_, lean_object* v_toPure_1453_, lean_object* v_err_1454_){
_start:
{
uint8_t v_err_boxed_1455_; lean_object* v_res_1456_; 
v_err_boxed_1455_ = lean_unbox(v_err_1454_);
v_res_1456_ = l_Lean_Doc_parseContent_x27___redArg___lam__7(v_st_1452_, v_toPure_1453_, v_err_boxed_1455_);
lean_dec_ref(v_st_1452_);
return v_res_1456_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object* v_env_1457_, lean_object* v_contents_1458_, lean_object* v_p_1459_, lean_object* v_ictx_1460_, lean_object* v_toPure_1461_, uint8_t v___x_1462_, lean_object* v_toBind_1463_, lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_____do__lift_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v_st_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_box(0);
lean_inc_ref(v_env_1457_);
v___x_1471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1471_, 0, v_env_1457_);
lean_ctor_set(v___x_1471_, 1, v_____do__lift_1468_);
lean_ctor_set(v___x_1471_, 2, v___x_1469_);
lean_ctor_set(v___x_1471_, 3, v___x_1470_);
v___x_1472_ = l_Lean_Parser_getTokenTable(v_env_1457_);
v___x_1473_ = l_Lean_Parser_mkParserState(v_contents_1458_);
lean_inc_ref(v_ictx_1460_);
v_st_1474_ = l_Lean_Parser_ParserFn_run(v_p_1459_, v_ictx_1460_, v___x_1471_, v___x_1472_, v___x_1473_);
lean_inc(v_toPure_1461_);
lean_inc_ref_n(v_st_1474_, 2);
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1475_, 0, v_st_1474_);
lean_closure_set(v___f_1475_, 1, v_toPure_1461_);
v___x_1476_ = l_Lean_Parser_ParserState_allErrors(v_st_1474_);
v___x_1477_ = lean_array_get_size(v___x_1476_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_nat_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1480_, 0, v___f_1475_);
v___x_1481_ = lean_box(v___x_1462_);
lean_inc(v_toBind_1463_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1482_, 0, v_toPure_1461_);
lean_closure_set(v___f_1482_, 1, v___x_1481_);
lean_closure_set(v___f_1482_, 2, v_toBind_1463_);
lean_closure_set(v___f_1482_, 3, v___f_1480_);
v___x_1483_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1460_, v_st_1474_);
v___x_1484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofFormat(v___x_1484_);
v___x_1486_ = l_Lean_logError___redArg(v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v___x_1485_);
v___x_1487_ = lean_apply_4(v_toBind_1463_, lean_box(0), lean_box(0), v___x_1486_, v___f_1482_);
return v___x_1487_;
}
else
{
lean_object* v_pos_1488_; uint8_t v___x_1489_; 
v_pos_1488_ = lean_ctor_get(v_st_1474_, 2);
v___x_1489_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1460_, v_pos_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1490_, 0, v___f_1475_);
v___x_1491_ = lean_box(v___x_1462_);
lean_inc(v_toBind_1463_);
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1492_, 0, v_toPure_1461_);
lean_closure_set(v___f_1492_, 1, v___x_1491_);
lean_closure_set(v___f_1492_, 2, v_toBind_1463_);
lean_closure_set(v___f_1492_, 3, v___f_1490_);
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1494_ = l_Lean_Parser_ParserState_mkError(v_st_1474_, v___x_1493_);
v___x_1495_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1460_, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
v___x_1497_ = l_Lean_MessageData_ofFormat(v___x_1496_);
v___x_1498_ = l_Lean_logError___redArg(v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v___x_1497_);
v___x_1499_ = lean_apply_4(v_toBind_1463_, lean_box(0), lean_box(0), v___x_1498_, v___f_1492_);
return v___x_1499_;
}
else
{
lean_object* v___f_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_st_1474_);
lean_dec_ref(v_inst_1467_);
lean_dec(v_inst_1466_);
lean_dec_ref(v_inst_1465_);
lean_dec_ref(v_inst_1464_);
lean_dec_ref(v_ictx_1460_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1500_, 0, v___f_1475_);
v___x_1501_ = 0;
v___x_1502_ = lean_box(v___x_1501_);
v___x_1503_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1502_);
v___x_1504_ = lean_apply_4(v_toBind_1463_, lean_box(0), lean_box(0), v___x_1503_, v___f_1500_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1457_ = stack[0].m_obj;
lean_object* v_contents_1458_ = stack[1].m_obj;
lean_object* v_p_1459_ = stack[2].m_obj;
lean_object* v_ictx_1460_ = stack[3].m_obj;
lean_object* v_toPure_1461_ = stack[4].m_obj;
uint8_t v___x_1462_ = stack[5].m_num;
lean_object* v_toBind_1463_ = stack[6].m_obj;
lean_object* v_inst_1464_ = stack[7].m_obj;
lean_object* v_inst_1465_ = stack[8].m_obj;
lean_object* v_inst_1466_ = stack[9].m_obj;
lean_object* v_inst_1467_ = stack[10].m_obj;
lean_object* v_____do__lift_1468_ = stack[11].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l_Lean_Doc_parseContent_x27___redArg___lam__13(v_env_1457_, v_contents_1458_, v_p_1459_, v_ictx_1460_, v_toPure_1461_, v___x_1462_, v_toBind_1463_, v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v_____do__lift_1468_);
stack->m_obj
 = v_res_1505_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object* v_env_1506_, lean_object* v_contents_1507_, lean_object* v_p_1508_, lean_object* v_ictx_1509_, lean_object* v_toPure_1510_, lean_object* v___x_1511_, lean_object* v_toBind_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_____do__lift_1517_){
_start:
{
uint8_t v___x_1214__boxed_1518_; lean_object* v_res_1519_; 
v___x_1214__boxed_1518_ = lean_unbox(v___x_1511_);
v_res_1519_ = l_Lean_Doc_parseContent_x27___redArg___lam__13(v_env_1506_, v_contents_1507_, v_p_1508_, v_ictx_1509_, v_toPure_1510_, v___x_1214__boxed_1518_, v_toBind_1512_, v_inst_1513_, v_inst_1514_, v_inst_1515_, v_inst_1516_, v_____do__lift_1517_);
lean_dec_ref(v_contents_1507_);
return v_res_1519_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object* v_inst_1520_, lean_object* v_contents_1521_, uint8_t v___x_1522_, lean_object* v_env_1523_, lean_object* v_p_1524_, lean_object* v_toPure_1525_, lean_object* v_toBind_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_____do__lift_1530_){
_start:
{
lean_object* v_getOptions_1531_; lean_object* v___x_1532_; lean_object* v_ictx_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; 
v_getOptions_1531_ = lean_ctor_get(v_inst_1520_, 0);
lean_inc(v_getOptions_1531_);
v___x_1532_ = lean_string_utf8_byte_size(v_contents_1521_);
lean_inc_ref(v_contents_1521_);
v_ictx_1533_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1521_, v_____do__lift_1530_, v___x_1522_, v___x_1532_);
v___x_1534_ = lean_box(v___x_1522_);
lean_inc(v_toBind_1526_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_1535_, 0, v_env_1523_);
lean_closure_set(v___f_1535_, 1, v_contents_1521_);
lean_closure_set(v___f_1535_, 2, v_p_1524_);
lean_closure_set(v___f_1535_, 3, v_ictx_1533_);
lean_closure_set(v___f_1535_, 4, v_toPure_1525_);
lean_closure_set(v___f_1535_, 5, v___x_1534_);
lean_closure_set(v___f_1535_, 6, v_toBind_1526_);
lean_closure_set(v___f_1535_, 7, v_inst_1527_);
lean_closure_set(v___f_1535_, 8, v_inst_1528_);
lean_closure_set(v___f_1535_, 9, v_inst_1529_);
lean_closure_set(v___f_1535_, 10, v_inst_1520_);
v___x_1536_ = lean_apply_4(v_toBind_1526_, lean_box(0), lean_box(0), v_getOptions_1531_, v___f_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1520_ = stack[0].m_obj;
lean_object* v_contents_1521_ = stack[1].m_obj;
uint8_t v___x_1522_ = stack[2].m_num;
lean_object* v_env_1523_ = stack[3].m_obj;
lean_object* v_p_1524_ = stack[4].m_obj;
lean_object* v_toPure_1525_ = stack[5].m_obj;
lean_object* v_toBind_1526_ = stack[6].m_obj;
lean_object* v_inst_1527_ = stack[7].m_obj;
lean_object* v_inst_1528_ = stack[8].m_obj;
lean_object* v_inst_1529_ = stack[9].m_obj;
lean_object* v_____do__lift_1530_ = stack[10].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_Lean_Doc_parseContent_x27___redArg___lam__8(v_inst_1520_, v_contents_1521_, v___x_1522_, v_env_1523_, v_p_1524_, v_toPure_1525_, v_toBind_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_____do__lift_1530_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object* v_inst_1538_, lean_object* v_contents_1539_, lean_object* v___x_1540_, lean_object* v_env_1541_, lean_object* v_p_1542_, lean_object* v_toPure_1543_, lean_object* v_toBind_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_____do__lift_1548_){
_start:
{
uint8_t v___x_1347__boxed_1549_; lean_object* v_res_1550_; 
v___x_1347__boxed_1549_ = lean_unbox(v___x_1540_);
v_res_1550_ = l_Lean_Doc_parseContent_x27___redArg___lam__8(v_inst_1538_, v_contents_1539_, v___x_1347__boxed_1549_, v_env_1541_, v_p_1542_, v_toPure_1543_, v_toBind_1544_, v_inst_1545_, v_inst_1546_, v_inst_1547_, v_____do__lift_1548_);
return v_res_1550_;
}
}
lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_contents_1553_, uint8_t v___x_1554_, lean_object* v_p_1555_, lean_object* v_toPure_1556_, lean_object* v_toBind_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_env_1560_){
_start:
{
lean_object* v_getFileName_1561_; lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
v_getFileName_1561_ = lean_ctor_get(v_inst_1551_, 2);
lean_inc(v_getFileName_1561_);
v___x_1562_ = lean_box(v___x_1554_);
lean_inc(v_toBind_1557_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_1563_, 0, v_inst_1552_);
lean_closure_set(v___f_1563_, 1, v_contents_1553_);
lean_closure_set(v___f_1563_, 2, v___x_1562_);
lean_closure_set(v___f_1563_, 3, v_env_1560_);
lean_closure_set(v___f_1563_, 4, v_p_1555_);
lean_closure_set(v___f_1563_, 5, v_toPure_1556_);
lean_closure_set(v___f_1563_, 6, v_toBind_1557_);
lean_closure_set(v___f_1563_, 7, v_inst_1558_);
lean_closure_set(v___f_1563_, 8, v_inst_1551_);
lean_closure_set(v___f_1563_, 9, v_inst_1559_);
v___x_1564_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v_getFileName_1561_, v___f_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT void l_Lean_Doc_parseContent_x27___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1551_ = stack[0].m_obj;
lean_object* v_inst_1552_ = stack[1].m_obj;
lean_object* v_contents_1553_ = stack[2].m_obj;
uint8_t v___x_1554_ = stack[3].m_num;
lean_object* v_p_1555_ = stack[4].m_obj;
lean_object* v_toPure_1556_ = stack[5].m_obj;
lean_object* v_toBind_1557_ = stack[6].m_obj;
lean_object* v_inst_1558_ = stack[7].m_obj;
lean_object* v_inst_1559_ = stack[8].m_obj;
lean_object* v_env_1560_ = stack[9].m_obj;
lean_object* v_res_1565_;
v_res_1565_ = l_Lean_Doc_parseContent_x27___redArg___lam__9(v_inst_1551_, v_inst_1552_, v_contents_1553_, v___x_1554_, v_p_1555_, v_toPure_1556_, v_toBind_1557_, v_inst_1558_, v_inst_1559_, v_env_1560_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_contents_1568_, lean_object* v___x_1569_, lean_object* v_p_1570_, lean_object* v_toPure_1571_, lean_object* v_toBind_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_env_1575_){
_start:
{
uint8_t v___x_1390__boxed_1576_; lean_object* v_res_1577_; 
v___x_1390__boxed_1576_ = lean_unbox(v___x_1569_);
v_res_1577_ = l_Lean_Doc_parseContent_x27___redArg___lam__9(v_inst_1566_, v_inst_1567_, v_contents_1568_, v___x_1390__boxed_1576_, v_p_1570_, v_toPure_1571_, v_toBind_1572_, v_inst_1573_, v_inst_1574_, v_env_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_p_1584_, lean_object* v_tok_1585_, lean_object* v_contents_1586_){
_start:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; uint8_t v___y_1590_; lean_object* v___x_1605_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = 1;
v___x_1605_ = l_Lean_Syntax_getPos_x3f(v_tok_1585_, v___x_1588_);
if (lean_obj_tag(v___x_1605_) == 0)
{
v___y_1590_ = v___x_1588_;
goto v___jp_1589_;
}
else
{
uint8_t v___x_1606_; 
lean_dec_ref_known(v___x_1605_, 1);
v___x_1606_ = 0;
v___y_1590_ = v___x_1606_;
goto v___jp_1589_;
}
v___jp_1589_:
{
if (v___y_1590_ == 0)
{
lean_object* v_toApplicative_1591_; lean_object* v_toBind_1592_; lean_object* v_toPure_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; 
v_toApplicative_1591_ = lean_ctor_get(v_inst_1578_, 0);
lean_dec_ref(v_contents_1586_);
v_toBind_1592_ = lean_ctor_get(v_inst_1578_, 1);
lean_inc_n(v_toBind_1592_, 2);
v_toPure_1593_ = lean_ctor_get(v_toApplicative_1591_, 1);
lean_inc(v_toPure_1593_);
v___x_1594_ = lean_box(v___x_1588_);
v___x_1595_ = lean_box(v___y_1590_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1596_, 0, v_inst_1580_);
lean_closure_set(v___f_1596_, 1, v_inst_1582_);
lean_closure_set(v___f_1596_, 2, v___x_1594_);
lean_closure_set(v___f_1596_, 3, v_inst_1583_);
lean_closure_set(v___f_1596_, 4, v_p_1584_);
lean_closure_set(v___f_1596_, 5, v_toPure_1593_);
lean_closure_set(v___f_1596_, 6, v_toBind_1592_);
lean_closure_set(v___f_1596_, 7, v_inst_1578_);
lean_closure_set(v___f_1596_, 8, v_inst_1581_);
lean_closure_set(v___f_1596_, 9, v___x_1595_);
lean_closure_set(v___f_1596_, 10, v_tok_1585_);
lean_closure_set(v___f_1596_, 11, v___x_1587_);
v___x_1597_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v_inst_1579_, v___f_1596_);
return v___x_1597_;
}
else
{
lean_object* v_toApplicative_1598_; lean_object* v_toBind_1599_; lean_object* v_toPure_1600_; lean_object* v_getEnv_1601_; lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; 
v_toApplicative_1598_ = lean_ctor_get(v_inst_1578_, 0);
lean_dec(v_tok_1585_);
lean_dec(v_inst_1579_);
v_toBind_1599_ = lean_ctor_get(v_inst_1578_, 1);
lean_inc_n(v_toBind_1599_, 2);
v_toPure_1600_ = lean_ctor_get(v_toApplicative_1598_, 1);
lean_inc(v_toPure_1600_);
v_getEnv_1601_ = lean_ctor_get(v_inst_1580_, 0);
lean_inc(v_getEnv_1601_);
lean_dec_ref(v_inst_1580_);
v___x_1602_ = lean_box(v___x_1588_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1603_, 0, v_inst_1582_);
lean_closure_set(v___f_1603_, 1, v_inst_1583_);
lean_closure_set(v___f_1603_, 2, v_contents_1586_);
lean_closure_set(v___f_1603_, 3, v___x_1602_);
lean_closure_set(v___f_1603_, 4, v_p_1584_);
lean_closure_set(v___f_1603_, 5, v_toPure_1600_);
lean_closure_set(v___f_1603_, 6, v_toBind_1599_);
lean_closure_set(v___f_1603_, 7, v_inst_1578_);
lean_closure_set(v___f_1603_, 8, v_inst_1581_);
v___x_1604_ = lean_apply_4(v_toBind_1599_, lean_box(0), lean_box(0), v_getEnv_1601_, v___f_1603_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_p_1614_, lean_object* v_tok_1615_, lean_object* v_contents_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1608_, v_inst_1609_, v_inst_1610_, v_inst_1611_, v_inst_1612_, v_inst_1613_, v_p_1614_, v_tok_1615_, v_contents_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_p_1624_, lean_object* v_c_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = l_Lean_TSyntax_getVersoCode(v_c_1625_);
v___x_1627_ = l_Lean_Doc_parseContent___redArg(v_inst_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v_p_1624_, v_c_1625_, v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object* v_m_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_p_1635_, lean_object* v_c_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Doc_parseVersoCode___redArg(v_inst_1629_, v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_p_1635_, v_c_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_p_1644_, lean_object* v_c_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = l_Lean_TSyntax_getVersoCodeBlock(v_c_1645_);
v___x_1647_ = l_Lean_Doc_parseContent___redArg(v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_inst_1642_, v_inst_1643_, v_p_1644_, v_c_1645_, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object* v_m_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_p_1655_, lean_object* v_c_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Doc_parseVersoCodeBlock___redArg(v_inst_1649_, v_inst_1650_, v_inst_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_, v_p_1655_, v_c_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_p_1664_, lean_object* v_c_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = l_Lean_TSyntax_getVersoCode(v_c_1665_);
v___x_1667_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1658_, v_inst_1659_, v_inst_1660_, v_inst_1661_, v_inst_1662_, v_inst_1663_, v_p_1664_, v_c_1665_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object* v_m_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_p_1675_, lean_object* v_c_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Doc_parseVersoCode_x27___redArg(v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_p_1675_, v_c_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_p_1684_, lean_object* v_s_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = l_Lean_TSyntax_getString(v_s_1685_);
v___x_1687_ = l_Lean_Doc_parseContent___redArg(v_inst_1678_, v_inst_1679_, v_inst_1680_, v_inst_1681_, v_inst_1682_, v_inst_1683_, v_p_1684_, v_s_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_p_1695_, lean_object* v_s_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Doc_parseStrLit___redArg(v_inst_1689_, v_inst_1690_, v_inst_1691_, v_inst_1692_, v_inst_1693_, v_inst_1694_, v_p_1695_, v_s_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_p_1704_, lean_object* v_s_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = l_Lean_TSyntax_getString(v_s_1705_);
v___x_1707_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_, v_inst_1702_, v_inst_1703_, v_p_1704_, v_s_1705_, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_p_1715_, lean_object* v_s_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1709_, v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_inst_1714_, v_p_1715_, v_s_1716_);
return v___x_1717_;
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
