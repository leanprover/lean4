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
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_contents_360_, lean_object* v_env_361_, lean_object* v_p_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_toPure_365_, lean_object* v_toBind_366_, lean_object* v_inst_367_, lean_object* v_____do__lift_368_){
_start:
{
uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v_ictx_371_; lean_object* v___f_372_; lean_object* v___x_373_; 
v___x_369_ = 1;
v___x_370_ = lean_string_utf8_byte_size(v_contents_360_);
lean_inc_ref(v_contents_360_);
v_ictx_371_ = l_Lean_Parser_mkInputContext___redArg(v_contents_360_, v_____do__lift_368_, v___x_369_, v___x_370_);
v___f_372_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_372_, 0, v_env_361_);
lean_closure_set(v___f_372_, 1, v_contents_360_);
lean_closure_set(v___f_372_, 2, v_p_362_);
lean_closure_set(v___f_372_, 3, v_ictx_371_);
lean_closure_set(v___f_372_, 4, v_inst_363_);
lean_closure_set(v___f_372_, 5, v_inst_364_);
lean_closure_set(v___f_372_, 6, v_toPure_365_);
v___x_373_ = lean_apply_4(v_toBind_366_, lean_box(0), lean_box(0), v_inst_367_, v___f_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_374_, lean_object* v_contents_375_, lean_object* v_p_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_toPure_379_, lean_object* v_toBind_380_, lean_object* v_inst_381_, lean_object* v_env_382_){
_start:
{
lean_object* v_getFileName_383_; lean_object* v___f_384_; lean_object* v___x_385_; 
v_getFileName_383_ = lean_ctor_get(v_inst_374_, 2);
lean_inc(v_getFileName_383_);
lean_dec_ref(v_inst_374_);
lean_inc(v_toBind_380_);
v___f_384_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_384_, 0, v_contents_375_);
lean_closure_set(v___f_384_, 1, v_env_382_);
lean_closure_set(v___f_384_, 2, v_p_376_);
lean_closure_set(v___f_384_, 3, v_inst_377_);
lean_closure_set(v___f_384_, 4, v_inst_378_);
lean_closure_set(v___f_384_, 5, v_toPure_379_);
lean_closure_set(v___f_384_, 6, v_toBind_380_);
lean_closure_set(v___f_384_, 7, v_inst_381_);
v___x_385_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v_getFileName_383_, v___f_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_p_391_, lean_object* v_contents_392_){
_start:
{
lean_object* v_toApplicative_393_; lean_object* v_toBind_394_; lean_object* v_getEnv_395_; lean_object* v_toPure_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v_toApplicative_393_ = lean_ctor_get(v_inst_386_, 0);
v_toBind_394_ = lean_ctor_get(v_inst_386_, 1);
lean_inc_n(v_toBind_394_, 2);
v_getEnv_395_ = lean_ctor_get(v_inst_387_, 0);
lean_inc(v_getEnv_395_);
lean_dec_ref(v_inst_387_);
v_toPure_396_ = lean_ctor_get(v_toApplicative_393_, 1);
lean_inc(v_toPure_396_);
v___f_397_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_397_, 0, v_inst_389_);
lean_closure_set(v___f_397_, 1, v_contents_392_);
lean_closure_set(v___f_397_, 2, v_p_391_);
lean_closure_set(v___f_397_, 3, v_inst_386_);
lean_closure_set(v___f_397_, 4, v_inst_388_);
lean_closure_set(v___f_397_, 5, v_toPure_396_);
lean_closure_set(v___f_397_, 6, v_toBind_394_);
lean_closure_set(v___f_397_, 7, v_inst_390_);
v___x_398_ = lean_apply_4(v_toBind_394_, lean_box(0), lean_box(0), v_getEnv_395_, v___f_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_p_405_, lean_object* v_contents_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_inst_404_, v_p_405_, v_contents_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object* v_env_408_, lean_object* v_p_409_, lean_object* v_ictx_410_, lean_object* v_s_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_toPure_414_, lean_object* v_____do__lift_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_s_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_box(0);
lean_inc_ref(v_env_408_);
v___x_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_418_, 0, v_env_408_);
lean_ctor_set(v___x_418_, 1, v_____do__lift_415_);
lean_ctor_set(v___x_418_, 2, v___x_416_);
lean_ctor_set(v___x_418_, 3, v___x_417_);
v___x_419_ = l_Lean_Parser_getTokenTable(v_env_408_);
lean_inc_ref(v_ictx_410_);
v_s_420_ = l_Lean_Parser_ParserFn_run(v_p_409_, v_ictx_410_, v___x_418_, v___x_419_, v_s_411_);
lean_inc_ref(v_s_420_);
v___x_421_ = l_Lean_Parser_ParserState_allErrors(v_s_420_);
v___x_422_ = lean_array_get_size(v___x_421_);
lean_dec_ref(v___x_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_nat_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_toPure_414_);
v___x_425_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_410_, v_s_420_);
v___x_426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
v___x_427_ = l_Lean_MessageData_ofFormat(v___x_426_);
v___x_428_ = l_Lean_throwError___redArg(v_inst_412_, v_inst_413_, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v_stxStack_429_; lean_object* v_pos_430_; uint8_t v___x_431_; 
v_stxStack_429_ = lean_ctor_get(v_s_420_, 0);
lean_inc_ref(v_stxStack_429_);
v_pos_430_ = lean_ctor_get(v_s_420_, 2);
lean_inc(v_pos_430_);
v___x_431_ = l_Lean_Parser_InputContext_atEnd(v_ictx_410_, v_pos_430_);
lean_dec(v_pos_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_stxStack_429_);
lean_dec(v_toPure_414_);
v___x_432_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_433_ = l_Lean_Parser_ParserState_mkError(v_s_420_, v___x_432_);
v___x_434_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_410_, v___x_433_);
v___x_435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
v___x_436_ = l_Lean_MessageData_ofFormat(v___x_435_);
v___x_437_ = l_Lean_throwError___redArg(v_inst_412_, v_inst_413_, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref(v_s_420_);
lean_dec_ref(v_inst_413_);
lean_dec_ref(v_inst_412_);
lean_dec_ref(v_ictx_410_);
v___x_438_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_429_);
lean_dec_ref(v_stxStack_429_);
v___x_439_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object* v_source_440_, uint8_t v___x_441_, lean_object* v___y_442_, lean_object* v_start_443_, lean_object* v_env_444_, lean_object* v_p_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_toPure_448_, lean_object* v_toBind_449_, lean_object* v_inst_450_, lean_object* v_____do__lift_451_){
_start:
{
lean_object* v_ictx_452_; lean_object* v___x_453_; lean_object* v_s_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
lean_inc_ref(v_source_440_);
v_ictx_452_ = l_Lean_Parser_mkInputContext___redArg(v_source_440_, v_____do__lift_451_, v___x_441_, v___y_442_);
v___x_453_ = l_Lean_Parser_mkParserState(v_source_440_);
lean_dec_ref(v_source_440_);
v_s_454_ = l_Lean_Parser_ParserState_setPos(v___x_453_, v_start_443_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__0), 8, 7);
lean_closure_set(v___f_455_, 0, v_env_444_);
lean_closure_set(v___f_455_, 1, v_p_445_);
lean_closure_set(v___f_455_, 2, v_ictx_452_);
lean_closure_set(v___f_455_, 3, v_s_454_);
lean_closure_set(v___f_455_, 4, v_inst_446_);
lean_closure_set(v___f_455_, 5, v_inst_447_);
lean_closure_set(v___f_455_, 6, v_toPure_448_);
v___x_456_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v_inst_450_, v___f_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object* v_source_457_, lean_object* v___x_458_, lean_object* v___y_459_, lean_object* v_start_460_, lean_object* v_env_461_, lean_object* v_p_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_toPure_465_, lean_object* v_toBind_466_, lean_object* v_inst_467_, lean_object* v_____do__lift_468_){
_start:
{
uint8_t v___x_362__boxed_469_; lean_object* v_res_470_; 
v___x_362__boxed_469_ = lean_unbox(v___x_458_);
v_res_470_ = l_Lean_Doc_parseContent___redArg___lam__1(v_source_457_, v___x_362__boxed_469_, v___y_459_, v_start_460_, v_env_461_, v_p_462_, v_inst_463_, v_inst_464_, v_toPure_465_, v_toBind_466_, v_inst_467_, v_____do__lift_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object* v_text_471_, lean_object* v_inst_472_, uint8_t v___x_473_, lean_object* v_env_474_, lean_object* v_p_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_toPure_478_, lean_object* v_toBind_479_, lean_object* v_inst_480_, lean_object* v_____x_481_){
_start:
{
lean_object* v_start_482_; lean_object* v_stop_483_; lean_object* v_source_484_; lean_object* v___y_486_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_start_482_ = lean_ctor_get(v_____x_481_, 0);
lean_inc(v_start_482_);
v_stop_483_ = lean_ctor_get(v_____x_481_, 1);
lean_inc(v_stop_483_);
lean_dec_ref(v_____x_481_);
v_source_484_ = lean_ctor_get(v_text_471_, 0);
lean_inc_ref(v_source_484_);
lean_dec_ref(v_text_471_);
v___x_491_ = lean_string_utf8_byte_size(v_source_484_);
v___x_492_ = lean_nat_dec_le(v_stop_483_, v___x_491_);
if (v___x_492_ == 0)
{
lean_dec(v_stop_483_);
v___y_486_ = v___x_491_;
goto v___jp_485_;
}
else
{
v___y_486_ = v_stop_483_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v_getFileName_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; 
v_getFileName_487_ = lean_ctor_get(v_inst_472_, 2);
lean_inc(v_getFileName_487_);
lean_dec_ref(v_inst_472_);
v___x_488_ = lean_box(v___x_473_);
lean_inc(v_toBind_479_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_489_, 0, v_source_484_);
lean_closure_set(v___f_489_, 1, v___x_488_);
lean_closure_set(v___f_489_, 2, v___y_486_);
lean_closure_set(v___f_489_, 3, v_start_482_);
lean_closure_set(v___f_489_, 4, v_env_474_);
lean_closure_set(v___f_489_, 5, v_p_475_);
lean_closure_set(v___f_489_, 6, v_inst_476_);
lean_closure_set(v___f_489_, 7, v_inst_477_);
lean_closure_set(v___f_489_, 8, v_toPure_478_);
lean_closure_set(v___f_489_, 9, v_toBind_479_);
lean_closure_set(v___f_489_, 10, v_inst_480_);
v___x_490_ = lean_apply_4(v_toBind_479_, lean_box(0), lean_box(0), v_getFileName_487_, v___f_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object* v_text_493_, lean_object* v_inst_494_, lean_object* v___x_495_, lean_object* v_env_496_, lean_object* v_p_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_toPure_500_, lean_object* v_toBind_501_, lean_object* v_inst_502_, lean_object* v_____x_503_){
_start:
{
uint8_t v___x_390__boxed_504_; lean_object* v_res_505_; 
v___x_390__boxed_504_ = lean_unbox(v___x_495_);
v_res_505_ = l_Lean_Doc_parseContent___redArg___lam__2(v_text_493_, v_inst_494_, v___x_390__boxed_504_, v_env_496_, v_p_497_, v_inst_498_, v_inst_499_, v_toPure_500_, v_toBind_501_, v_inst_502_, v_____x_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object* v_text_506_, lean_object* v_inst_507_, uint8_t v___x_508_, lean_object* v_p_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_toPure_512_, lean_object* v_toBind_513_, lean_object* v_inst_514_, lean_object* v_tok_515_, lean_object* v_env_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_box(v___x_508_);
lean_inc(v_toBind_513_);
lean_inc_ref(v_inst_510_);
v___f_518_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_518_, 0, v_text_506_);
lean_closure_set(v___f_518_, 1, v_inst_507_);
lean_closure_set(v___f_518_, 2, v___x_517_);
lean_closure_set(v___f_518_, 3, v_env_516_);
lean_closure_set(v___f_518_, 4, v_p_509_);
lean_closure_set(v___f_518_, 5, v_inst_510_);
lean_closure_set(v___f_518_, 6, v_inst_511_);
lean_closure_set(v___f_518_, 7, v_toPure_512_);
lean_closure_set(v___f_518_, 8, v_toBind_513_);
lean_closure_set(v___f_518_, 9, v_inst_514_);
v___x_519_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_510_, v_tok_515_);
v___x_520_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v___x_519_, v___f_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object* v_text_521_, lean_object* v_inst_522_, lean_object* v___x_523_, lean_object* v_p_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_toPure_527_, lean_object* v_toBind_528_, lean_object* v_inst_529_, lean_object* v_tok_530_, lean_object* v_env_531_){
_start:
{
uint8_t v___x_426__boxed_532_; lean_object* v_res_533_; 
v___x_426__boxed_532_ = lean_unbox(v___x_523_);
v_res_533_ = l_Lean_Doc_parseContent___redArg___lam__3(v_text_521_, v_inst_522_, v___x_426__boxed_532_, v_p_524_, v_inst_525_, v_inst_526_, v_toPure_527_, v_toBind_528_, v_inst_529_, v_tok_530_, v_env_531_);
lean_dec(v_tok_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object* v_inst_534_, lean_object* v_inst_535_, uint8_t v___x_536_, lean_object* v_p_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_toPure_540_, lean_object* v_toBind_541_, lean_object* v_inst_542_, lean_object* v_tok_543_, lean_object* v_text_544_){
_start:
{
lean_object* v_getEnv_545_; lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v_getEnv_545_ = lean_ctor_get(v_inst_534_, 0);
lean_inc(v_getEnv_545_);
lean_dec_ref(v_inst_534_);
v___x_546_ = lean_box(v___x_536_);
lean_inc(v_toBind_541_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_547_, 0, v_text_544_);
lean_closure_set(v___f_547_, 1, v_inst_535_);
lean_closure_set(v___f_547_, 2, v___x_546_);
lean_closure_set(v___f_547_, 3, v_p_537_);
lean_closure_set(v___f_547_, 4, v_inst_538_);
lean_closure_set(v___f_547_, 5, v_inst_539_);
lean_closure_set(v___f_547_, 6, v_toPure_540_);
lean_closure_set(v___f_547_, 7, v_toBind_541_);
lean_closure_set(v___f_547_, 8, v_inst_542_);
lean_closure_set(v___f_547_, 9, v_tok_543_);
v___x_548_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v_getEnv_545_, v___f_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v___x_551_, lean_object* v_p_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_toPure_555_, lean_object* v_toBind_556_, lean_object* v_inst_557_, lean_object* v_tok_558_, lean_object* v_text_559_){
_start:
{
uint8_t v___x_450__boxed_560_; lean_object* v_res_561_; 
v___x_450__boxed_560_ = lean_unbox(v___x_551_);
v_res_561_ = l_Lean_Doc_parseContent___redArg___lam__4(v_inst_549_, v_inst_550_, v___x_450__boxed_560_, v_p_552_, v_inst_553_, v_inst_554_, v_toPure_555_, v_toBind_556_, v_inst_557_, v_tok_558_, v_text_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_p_568_, lean_object* v_tok_569_, lean_object* v_contents_570_){
_start:
{
uint8_t v___x_571_; uint8_t v___y_573_; lean_object* v___x_581_; 
v___x_571_ = 1;
v___x_581_ = l_Lean_Syntax_getPos_x3f(v_tok_569_, v___x_571_);
if (lean_obj_tag(v___x_581_) == 0)
{
v___y_573_ = v___x_571_;
goto v___jp_572_;
}
else
{
uint8_t v___x_582_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_582_ = 0;
v___y_573_ = v___x_582_;
goto v___jp_572_;
}
v___jp_572_:
{
if (v___y_573_ == 0)
{
lean_object* v_toApplicative_574_; lean_object* v_toBind_575_; lean_object* v_toPure_576_; lean_object* v___x_577_; lean_object* v___f_578_; lean_object* v___x_579_; 
v_toApplicative_574_ = lean_ctor_get(v_inst_562_, 0);
lean_dec_ref(v_contents_570_);
v_toBind_575_ = lean_ctor_get(v_inst_562_, 1);
lean_inc_n(v_toBind_575_, 2);
v_toPure_576_ = lean_ctor_get(v_toApplicative_574_, 1);
lean_inc(v_toPure_576_);
v___x_577_ = lean_box(v___x_571_);
v___f_578_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_578_, 0, v_inst_564_);
lean_closure_set(v___f_578_, 1, v_inst_566_);
lean_closure_set(v___f_578_, 2, v___x_577_);
lean_closure_set(v___f_578_, 3, v_p_568_);
lean_closure_set(v___f_578_, 4, v_inst_562_);
lean_closure_set(v___f_578_, 5, v_inst_565_);
lean_closure_set(v___f_578_, 6, v_toPure_576_);
lean_closure_set(v___f_578_, 7, v_toBind_575_);
lean_closure_set(v___f_578_, 8, v_inst_567_);
lean_closure_set(v___f_578_, 9, v_tok_569_);
v___x_579_ = lean_apply_4(v_toBind_575_, lean_box(0), lean_box(0), v_inst_563_, v___f_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
lean_dec(v_tok_569_);
lean_dec(v_inst_563_);
v___x_580_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_562_, v_inst_564_, v_inst_565_, v_inst_566_, v_inst_567_, v_p_568_, v_contents_570_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object* v_m_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_p_590_, lean_object* v_tok_591_, lean_object* v_contents_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Doc_parseContent___redArg(v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_p_590_, v_tok_591_, v_contents_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_612_; 
v_fst_596_ = lean_ctor_get(v_a_595_, 0);
v_snd_597_ = lean_ctor_get(v_a_595_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_612_ == 0)
{
v___x_599_ = v_a_595_;
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snd_597_);
lean_inc(v_fst_596_);
lean_dec(v_a_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_dec_le(v___x_601_, v_fst_596_);
if (v___x_602_ == 0)
{
lean_object* v___x_604_; 
if (v_isShared_600_ == 0)
{
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_fst_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_597_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_string_utf8_prev(v_str_594_, v_fst_596_);
lean_dec(v_fst_596_);
v___x_607_ = lean_nat_add(v_snd_597_, v___x_601_);
lean_dec(v_snd_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_607_);
lean_ctor_set(v___x_599_, 0, v___x_606_);
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_607_);
v___x_609_ = v_reuseFailAlloc_611_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v_a_595_ = v___x_609_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_613_, v_a_614_);
lean_dec_ref(v_str_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_616_, lean_object* v_p_617_){
_start:
{
lean_object* v_n_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_snd_621_; 
v_n_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_p_617_);
lean_ctor_set(v___x_619_, 1, v_n_618_);
v___x_620_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_616_, v___x_619_);
v_snd_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_snd_621_);
lean_dec_ref(v___x_620_);
return v_snd_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_622_, lean_object* v_p_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_622_, v_p_623_);
lean_dec_ref(v_str_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_625_, lean_object* v_inst_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_625_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_629_, lean_object* v_inst_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_629_, v_inst_630_, v_a_631_);
lean_dec_ref(v_str_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_633_, lean_object* v_p_634_, lean_object* v_j_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_zero_637_; uint8_t v_isZero_638_; 
v_zero_637_ = lean_unsigned_to_nat(0u);
v_isZero_638_ = lean_nat_dec_eq(v_j_635_, v_zero_637_);
if (v_isZero_638_ == 1)
{
lean_dec(v_j_635_);
return v_a_636_;
}
else
{
lean_object* v_one_639_; lean_object* v_n_640_; lean_object* v___x_641_; 
lean_dec(v_a_636_);
v_one_639_ = lean_unsigned_to_nat(1u);
v_n_640_ = lean_nat_sub(v_j_635_, v_one_639_);
lean_dec(v_j_635_);
v___x_641_ = lean_string_utf8_next(v_str_633_, v_p_634_);
v_j_635_ = v_n_640_;
v_a_636_ = v___x_641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_643_, lean_object* v_p_644_, lean_object* v_j_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_643_, v_p_644_, v_j_645_, v_a_646_);
lean_dec(v_p_644_);
lean_dec_ref(v_str_643_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_648_, lean_object* v_n_649_, lean_object* v_p_650_){
_start:
{
lean_object* v___x_651_; 
lean_inc(v_p_650_);
v___x_651_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_648_, v_p_650_, v_n_649_, v_p_650_);
lean_dec(v_p_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_652_, lean_object* v_n_653_, lean_object* v_p_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_652_, v_n_653_, v_p_654_);
lean_dec_ref(v_str_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_656_, lean_object* v_p_657_, lean_object* v_n_658_, lean_object* v_j_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_656_, v_p_657_, v_j_659_, v_a_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_663_, lean_object* v_p_664_, lean_object* v_n_665_, lean_object* v_j_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_663_, v_p_664_, v_n_665_, v_j_666_, v_a_667_, v_a_668_);
lean_dec(v_n_665_);
lean_dec(v_p_664_);
lean_dec_ref(v_str_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_670_, lean_object* v_posOfStr_671_, lean_object* v_str_672_, lean_object* v_posInStr_673_){
_start:
{
lean_object* v_source_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_source_674_ = lean_ctor_get(v_text_670_, 0);
v___x_675_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_672_, v_posInStr_673_);
lean_inc(v_posOfStr_671_);
v___x_676_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_674_, v_posOfStr_671_, v___x_675_, v_posOfStr_671_);
lean_dec(v_posOfStr_671_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_677_, lean_object* v_posOfStr_678_, lean_object* v_str_679_, lean_object* v_posInStr_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_677_, v_posOfStr_678_, v_str_679_, v_posInStr_680_);
lean_dec_ref(v_str_679_);
lean_dec_ref(v_text_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_682_, lean_object* v_posOfStr_683_, lean_object* v_str_684_, lean_object* v_a_685_){
_start:
{
switch(lean_obj_tag(v_a_685_))
{
case 0:
{
lean_object* v_pos_686_; lean_object* v_endPos_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; 
v_pos_686_ = lean_ctor_get(v_a_685_, 1);
lean_inc(v_pos_686_);
v_endPos_687_ = lean_ctor_get(v_a_685_, 3);
lean_inc(v_endPos_687_);
lean_dec_ref_known(v_a_685_, 4);
lean_inc(v_posOfStr_683_);
v___x_688_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_682_, v_posOfStr_683_, v_str_684_, v_pos_686_);
v___x_689_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_682_, v_posOfStr_683_, v_str_684_, v_endPos_687_);
v___x_690_ = 1;
v___x_691_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_691_, 0, v___x_688_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*2, v___x_690_);
return v___x_691_;
}
case 1:
{
lean_object* v_pos_692_; lean_object* v_endPos_693_; uint8_t v_canonical_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_703_; 
v_pos_692_ = lean_ctor_get(v_a_685_, 0);
v_endPos_693_ = lean_ctor_get(v_a_685_, 1);
v_canonical_694_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*2);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_685_);
if (v_isSharedCheck_703_ == 0)
{
v___x_696_ = v_a_685_;
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_endPos_693_);
lean_inc(v_pos_692_);
lean_dec(v_a_685_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
lean_inc(v_posOfStr_683_);
v___x_698_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_682_, v_posOfStr_683_, v_str_684_, v_pos_692_);
v___x_699_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_682_, v_posOfStr_683_, v_str_684_, v_endPos_693_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_699_);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_702_, sizeof(void*)*2, v_canonical_694_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
default: 
{
lean_dec(v_posOfStr_683_);
return v_a_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_704_, lean_object* v_posOfStr_705_, lean_object* v_str_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_704_, v_posOfStr_705_, v_str_706_, v_a_707_);
lean_dec_ref(v_str_706_);
lean_dec_ref(v_text_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_709_, lean_object* v_posOfStr_710_, lean_object* v_str_711_, lean_object* v_a_712_){
_start:
{
switch(lean_obj_tag(v_a_712_))
{
case 0:
{
lean_dec(v_posOfStr_710_);
return v_a_712_;
}
case 1:
{
lean_object* v_info_713_; lean_object* v_kind_714_; lean_object* v_args_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v_info_713_ = lean_ctor_get(v_a_712_, 0);
v_kind_714_ = lean_ctor_get(v_a_712_, 1);
v_args_715_ = lean_ctor_get(v_a_712_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v_a_712_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_args_715_);
lean_inc(v_kind_714_);
lean_inc(v_info_713_);
lean_dec(v_a_712_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; size_t v_sz_720_; size_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc(v_posOfStr_710_);
v___x_719_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_709_, v_posOfStr_710_, v_str_711_, v_info_713_);
v_sz_720_ = lean_array_size(v_args_715_);
v___x_721_ = ((size_t)0ULL);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_709_, v_posOfStr_710_, v_str_711_, v_sz_720_, v___x_721_, v_args_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 2, v___x_722_);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_724_ = v___x_717_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_kind_714_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
case 2:
{
lean_object* v_info_727_; lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_info_727_ = lean_ctor_get(v_a_712_, 0);
v_val_728_ = lean_ctor_get(v_a_712_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_a_712_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_inc(v_info_727_);
lean_dec(v_a_712_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_709_, v_posOfStr_710_, v_str_711_, v_info_727_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_val_728_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
default: 
{
lean_object* v_info_737_; lean_object* v_rawVal_738_; lean_object* v_val_739_; lean_object* v_preresolved_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
v_info_737_ = lean_ctor_get(v_a_712_, 0);
v_rawVal_738_ = lean_ctor_get(v_a_712_, 1);
v_val_739_ = lean_ctor_get(v_a_712_, 2);
v_preresolved_740_ = lean_ctor_get(v_a_712_, 3);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_748_ == 0)
{
v___x_742_ = v_a_712_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_preresolved_740_);
lean_inc(v_val_739_);
lean_inc(v_rawVal_738_);
lean_inc(v_info_737_);
lean_dec(v_a_712_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_709_, v_posOfStr_710_, v_str_711_, v_info_737_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_rawVal_738_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_val_739_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_preresolved_740_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_749_, lean_object* v_posOfStr_750_, lean_object* v_str_751_, size_t v_sz_752_, size_t v_i_753_, lean_object* v_bs_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_755_ == 0)
{
lean_dec(v_posOfStr_750_);
return v_bs_754_;
}
else
{
lean_object* v_v_756_; lean_object* v___x_757_; lean_object* v_bs_x27_758_; lean_object* v___x_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v_v_756_ = lean_array_uget(v_bs_754_, v_i_753_);
v___x_757_ = lean_unsigned_to_nat(0u);
v_bs_x27_758_ = lean_array_uset(v_bs_754_, v_i_753_, v___x_757_);
lean_inc(v_posOfStr_750_);
v___x_759_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_749_, v_posOfStr_750_, v_str_751_, v_v_756_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_add(v_i_753_, v___x_760_);
v___x_762_ = lean_array_uset(v_bs_x27_758_, v_i_753_, v___x_759_);
v_i_753_ = v___x_761_;
v_bs_754_ = v___x_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_764_, lean_object* v_posOfStr_765_, lean_object* v_str_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_bs_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_764_, v_posOfStr_765_, v_str_766_, v_sz_boxed_770_, v_i_boxed_771_, v_bs_769_);
lean_dec_ref(v_str_766_);
lean_dec_ref(v_text_764_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_773_, lean_object* v_posOfStr_774_, lean_object* v_str_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_773_, v_posOfStr_774_, v_str_775_, v_a_776_);
lean_dec_ref(v_str_775_);
lean_dec_ref(v_text_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_778_, lean_object* v_h__1_779_, lean_object* v_h__2_780_, lean_object* v_h__3_781_, lean_object* v_h__4_782_){
_start:
{
switch(lean_obj_tag(v_x_778_))
{
case 0:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v_h__3_781_);
lean_dec(v_h__2_780_);
lean_dec(v_h__1_779_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_apply_1(v_h__4_782_, v___x_783_);
return v___x_784_;
}
case 1:
{
lean_object* v_info_785_; lean_object* v_kind_786_; lean_object* v_args_787_; lean_object* v___x_788_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__3_781_);
lean_dec(v_h__2_780_);
v_info_785_ = lean_ctor_get(v_x_778_, 0);
lean_inc(v_info_785_);
v_kind_786_ = lean_ctor_get(v_x_778_, 1);
lean_inc(v_kind_786_);
v_args_787_ = lean_ctor_get(v_x_778_, 2);
lean_inc_ref(v_args_787_);
lean_dec_ref_known(v_x_778_, 3);
v___x_788_ = lean_apply_3(v_h__1_779_, v_info_785_, v_kind_786_, v_args_787_);
return v___x_788_;
}
case 2:
{
lean_object* v_info_789_; lean_object* v_val_790_; lean_object* v___x_791_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__2_780_);
lean_dec(v_h__1_779_);
v_info_789_ = lean_ctor_get(v_x_778_, 0);
lean_inc(v_info_789_);
v_val_790_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_val_790_);
lean_dec_ref_known(v_x_778_, 2);
v___x_791_ = lean_apply_2(v_h__3_781_, v_info_789_, v_val_790_);
return v___x_791_;
}
default: 
{
lean_object* v_info_792_; lean_object* v_rawVal_793_; lean_object* v_val_794_; lean_object* v_preresolved_795_; lean_object* v___x_796_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__3_781_);
lean_dec(v_h__1_779_);
v_info_792_ = lean_ctor_get(v_x_778_, 0);
lean_inc(v_info_792_);
v_rawVal_793_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_rawVal_793_);
v_val_794_ = lean_ctor_get(v_x_778_, 2);
lean_inc(v_val_794_);
v_preresolved_795_ = lean_ctor_get(v_x_778_, 3);
lean_inc(v_preresolved_795_);
lean_dec_ref_known(v_x_778_, 4);
v___x_796_ = lean_apply_4(v_h__2_780_, v_info_792_, v_rawVal_793_, v_val_794_, v_preresolved_795_);
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_797_, lean_object* v_x_798_, lean_object* v_h__1_799_, lean_object* v_h__2_800_, lean_object* v_h__3_801_, lean_object* v_h__4_802_){
_start:
{
switch(lean_obj_tag(v_x_798_))
{
case 0:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_h__3_801_);
lean_dec(v_h__2_800_);
lean_dec(v_h__1_799_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_1(v_h__4_802_, v___x_803_);
return v___x_804_;
}
case 1:
{
lean_object* v_info_805_; lean_object* v_kind_806_; lean_object* v_args_807_; lean_object* v___x_808_; 
lean_dec(v_h__4_802_);
lean_dec(v_h__3_801_);
lean_dec(v_h__2_800_);
v_info_805_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_info_805_);
v_kind_806_ = lean_ctor_get(v_x_798_, 1);
lean_inc(v_kind_806_);
v_args_807_ = lean_ctor_get(v_x_798_, 2);
lean_inc_ref(v_args_807_);
lean_dec_ref_known(v_x_798_, 3);
v___x_808_ = lean_apply_3(v_h__1_799_, v_info_805_, v_kind_806_, v_args_807_);
return v___x_808_;
}
case 2:
{
lean_object* v_info_809_; lean_object* v_val_810_; lean_object* v___x_811_; 
lean_dec(v_h__4_802_);
lean_dec(v_h__2_800_);
lean_dec(v_h__1_799_);
v_info_809_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_info_809_);
v_val_810_ = lean_ctor_get(v_x_798_, 1);
lean_inc_ref(v_val_810_);
lean_dec_ref_known(v_x_798_, 2);
v___x_811_ = lean_apply_2(v_h__3_801_, v_info_809_, v_val_810_);
return v___x_811_;
}
default: 
{
lean_object* v_info_812_; lean_object* v_rawVal_813_; lean_object* v_val_814_; lean_object* v_preresolved_815_; lean_object* v___x_816_; 
lean_dec(v_h__4_802_);
lean_dec(v_h__3_801_);
lean_dec(v_h__1_799_);
v_info_812_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_info_812_);
v_rawVal_813_ = lean_ctor_get(v_x_798_, 1);
lean_inc_ref(v_rawVal_813_);
v_val_814_ = lean_ctor_get(v_x_798_, 2);
lean_inc(v_val_814_);
v_preresolved_815_ = lean_ctor_get(v_x_798_, 3);
lean_inc(v_preresolved_815_);
lean_dec_ref_known(v_x_798_, 4);
v___x_816_ = lean_apply_4(v_h__2_800_, v_info_812_, v_rawVal_813_, v_val_814_, v_preresolved_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_817_, lean_object* v_h__1_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lean_apply_2(v_h__1_818_, v_x_817_, lean_box(0));
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_820_, lean_object* v_P_821_, lean_object* v_motive_822_, lean_object* v_x_823_, lean_object* v_h__1_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_2(v_h__1_824_, v_x_823_, lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_toPure_826_, lean_object* v_____do__lift_827_){
_start:
{
if (lean_obj_tag(v_____do__lift_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_a_828_ = lean_ctor_get(v_____do__lift_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_____do__lift_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_830_ = v_____do__lift_827_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v_____do__lift_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 1);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_apply_2(v_toPure_826_, lean_box(0), v___x_833_);
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_a_837_ = lean_ctor_get(v_____do__lift_827_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_____do__lift_827_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v_____do__lift_827_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v_____do__lift_827_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_toPure_826_, lean_box(0), v___x_842_);
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_text_846_, lean_object* v_pos_847_, lean_object* v_str_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_fst_850_ = lean_ctor_get(v_x_849_, 0);
v_snd_851_ = lean_ctor_get(v_x_849_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_x_849_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v_x_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_846_, v_pos_847_, v_str_848_, v_fst_850_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_snd_851_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_text_860_, lean_object* v_pos_861_, lean_object* v_str_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_text_860_, v_pos_861_, v_str_862_, v_x_863_);
lean_dec_ref(v_str_862_);
lean_dec_ref(v_text_860_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_env_865_, lean_object* v_p_866_, lean_object* v_ictx_867_, lean_object* v_s_868_, lean_object* v_text_869_, lean_object* v_pos_870_, lean_object* v_str_871_, lean_object* v___f_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_toPure_875_, lean_object* v_____do__lift_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_s_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_877_ = lean_box(0);
v___x_878_ = lean_box(0);
lean_inc_ref(v_env_865_);
v___x_879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_879_, 0, v_env_865_);
lean_ctor_set(v___x_879_, 1, v_____do__lift_876_);
lean_ctor_set(v___x_879_, 2, v___x_877_);
lean_ctor_set(v___x_879_, 3, v___x_878_);
v___x_880_ = l_Lean_Parser_getTokenTable(v_env_865_);
lean_inc_ref(v_ictx_867_);
v_s_881_ = l_Lean_Parser_ParserFn_run(v_p_866_, v_ictx_867_, v___x_879_, v___x_880_, v_s_868_);
lean_inc_ref(v_s_881_);
v___x_882_ = l_Lean_Parser_ParserState_allErrors(v_s_881_);
v___x_883_ = lean_array_get_size(v___x_882_);
lean_dec_ref(v___x_882_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_nat_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v_stxStack_886_; lean_object* v_lhsPrec_887_; lean_object* v_pos_888_; lean_object* v_cache_889_; lean_object* v_errorMsg_890_; lean_object* v_recoveredErrors_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_toPure_875_);
v_stxStack_886_ = lean_ctor_get(v_s_881_, 0);
v_lhsPrec_887_ = lean_ctor_get(v_s_881_, 1);
v_pos_888_ = lean_ctor_get(v_s_881_, 2);
v_cache_889_ = lean_ctor_get(v_s_881_, 3);
v_errorMsg_890_ = lean_ctor_get(v_s_881_, 4);
v_recoveredErrors_891_ = lean_ctor_get(v_s_881_, 5);
v_isSharedCheck_928_ = !lean_is_exclusive(v_s_881_);
if (v_isSharedCheck_928_ == 0)
{
v___x_893_ = v_s_881_;
v_isShared_894_ = v_isSharedCheck_928_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_recoveredErrors_891_);
lean_inc(v_errorMsg_890_);
lean_inc(v_cache_889_);
lean_inc(v_pos_888_);
lean_inc(v_lhsPrec_887_);
lean_inc(v_stxStack_886_);
lean_dec(v_s_881_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_928_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___y_897_; 
lean_inc(v_pos_870_);
v___x_895_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_869_, v_pos_870_, v_str_871_, v_pos_888_);
if (lean_obj_tag(v_errorMsg_890_) == 0)
{
lean_dec(v_pos_870_);
v___y_897_ = v_errorMsg_890_;
goto v___jp_896_;
}
else
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_927_; 
v_val_909_ = lean_ctor_get(v_errorMsg_890_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v_errorMsg_890_);
if (v_isSharedCheck_927_ == 0)
{
v___x_911_ = v_errorMsg_890_;
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v_errorMsg_890_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_unexpectedTk_913_; lean_object* v_unexpected_914_; lean_object* v_expected_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_926_; 
v_unexpectedTk_913_ = lean_ctor_get(v_val_909_, 0);
v_unexpected_914_ = lean_ctor_get(v_val_909_, 1);
v_expected_915_ = lean_ctor_get(v_val_909_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_val_909_);
if (v_isSharedCheck_926_ == 0)
{
v___x_917_ = v_val_909_;
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_expected_915_);
lean_inc(v_unexpected_914_);
lean_inc(v_unexpectedTk_913_);
lean_dec(v_val_909_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_869_, v_pos_870_, v_str_871_, v_unexpectedTk_913_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_unexpected_914_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_expected_915_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_921_);
v___x_923_ = v___x_911_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v___y_897_ = v___x_923_;
goto v___jp_896_;
}
}
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; lean_object* v_s_903_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_argumentRange___redArg___lam__3___closed__9));
v_sz_899_ = lean_array_size(v_recoveredErrors_891_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_898_, v___f_872_, v_sz_899_, v___x_900_, v_recoveredErrors_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 5, v___x_901_);
lean_ctor_set(v___x_893_, 4, v___y_897_);
lean_ctor_set(v___x_893_, 2, v___x_895_);
v_s_903_ = v___x_893_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_stxStack_886_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_lhsPrec_887_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_cache_889_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v___y_897_);
lean_ctor_set(v_reuseFailAlloc_908_, 5, v___x_901_);
v_s_903_ = v_reuseFailAlloc_908_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_867_, v_s_903_);
v___x_905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = l_Lean_MessageData_ofFormat(v___x_905_);
v___x_907_ = l_Lean_throwError___redArg(v_inst_873_, v_inst_874_, v___x_906_);
return v___x_907_;
}
}
}
}
else
{
lean_object* v_stxStack_929_; lean_object* v_pos_930_; uint8_t v___x_931_; 
lean_dec_ref(v___f_872_);
v_stxStack_929_ = lean_ctor_get(v_s_881_, 0);
lean_inc_ref(v_stxStack_929_);
v_pos_930_ = lean_ctor_get(v_s_881_, 2);
lean_inc(v_pos_930_);
v___x_931_ = l_Lean_Parser_InputContext_atEnd(v_ictx_867_, v_pos_930_);
lean_dec(v_pos_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_stxStack_929_);
lean_dec(v_toPure_875_);
lean_dec(v_pos_870_);
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_933_ = l_Lean_Parser_ParserState_mkError(v_s_881_, v___x_932_);
v___x_934_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_867_, v___x_933_);
v___x_935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
v___x_936_ = l_Lean_MessageData_ofFormat(v___x_935_);
v___x_937_ = l_Lean_throwError___redArg(v_inst_873_, v_inst_874_, v___x_936_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_s_881_);
lean_dec_ref(v_inst_874_);
lean_dec_ref(v_inst_873_);
lean_dec_ref(v_ictx_867_);
v___x_938_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_929_);
lean_dec_ref(v_stxStack_929_);
v___x_939_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_869_, v_pos_870_, v_str_871_, v___x_938_);
v___x_940_ = lean_apply_2(v_toPure_875_, lean_box(0), v___x_939_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_env_941_, lean_object* v_p_942_, lean_object* v_ictx_943_, lean_object* v_s_944_, lean_object* v_text_945_, lean_object* v_pos_946_, lean_object* v_str_947_, lean_object* v___f_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_toPure_951_, lean_object* v_____do__lift_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_env_941_, v_p_942_, v_ictx_943_, v_s_944_, v_text_945_, v_pos_946_, v_str_947_, v___f_948_, v_inst_949_, v_inst_950_, v_toPure_951_, v_____do__lift_952_);
lean_dec_ref(v_str_947_);
lean_dec_ref(v_text_945_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_str_954_, uint8_t v___x_955_, lean_object* v_env_956_, lean_object* v_p_957_, lean_object* v_text_958_, lean_object* v_pos_959_, lean_object* v___f_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_toPure_963_, lean_object* v_toBind_964_, lean_object* v_inst_965_, lean_object* v_____do__lift_966_){
_start:
{
lean_object* v___x_967_; lean_object* v_ictx_968_; lean_object* v_s_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
v___x_967_ = lean_string_utf8_byte_size(v_str_954_);
lean_inc_ref(v_str_954_);
v_ictx_968_ = l_Lean_Parser_mkInputContext___redArg(v_str_954_, v_____do__lift_966_, v___x_955_, v___x_967_);
v_s_969_ = l_Lean_Parser_mkParserState(v_str_954_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_970_, 0, v_env_956_);
lean_closure_set(v___f_970_, 1, v_p_957_);
lean_closure_set(v___f_970_, 2, v_ictx_968_);
lean_closure_set(v___f_970_, 3, v_s_969_);
lean_closure_set(v___f_970_, 4, v_text_958_);
lean_closure_set(v___f_970_, 5, v_pos_959_);
lean_closure_set(v___f_970_, 6, v_str_954_);
lean_closure_set(v___f_970_, 7, v___f_960_);
lean_closure_set(v___f_970_, 8, v_inst_961_);
lean_closure_set(v___f_970_, 9, v_inst_962_);
lean_closure_set(v___f_970_, 10, v_toPure_963_);
v___x_971_ = lean_apply_4(v_toBind_964_, lean_box(0), lean_box(0), v_inst_965_, v___f_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_str_972_, lean_object* v___x_973_, lean_object* v_env_974_, lean_object* v_p_975_, lean_object* v_text_976_, lean_object* v_pos_977_, lean_object* v___f_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_toPure_981_, lean_object* v_toBind_982_, lean_object* v_inst_983_, lean_object* v_____do__lift_984_){
_start:
{
uint8_t v___x_1022__boxed_985_; lean_object* v_res_986_; 
v___x_1022__boxed_985_ = lean_unbox(v___x_973_);
v_res_986_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_str_972_, v___x_1022__boxed_985_, v_env_974_, v_p_975_, v_text_976_, v_pos_977_, v___f_978_, v_inst_979_, v_inst_980_, v_toPure_981_, v_toBind_982_, v_inst_983_, v_____do__lift_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v_inst_987_, lean_object* v_strLit_988_, lean_object* v_text_989_, uint8_t v___x_990_, lean_object* v_env_991_, lean_object* v_p_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_toPure_995_, lean_object* v_toBind_996_, lean_object* v_inst_997_, lean_object* v_pos_998_){
_start:
{
lean_object* v_getFileName_999_; lean_object* v_str_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; 
v_getFileName_999_ = lean_ctor_get(v_inst_987_, 2);
lean_inc(v_getFileName_999_);
lean_dec_ref(v_inst_987_);
v_str_1000_ = l_Lean_TSyntax_getString(v_strLit_988_);
lean_inc_ref(v_str_1000_);
lean_inc(v_pos_998_);
lean_inc_ref(v_text_989_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1001_, 0, v_text_989_);
lean_closure_set(v___f_1001_, 1, v_pos_998_);
lean_closure_set(v___f_1001_, 2, v_str_1000_);
v___x_1002_ = lean_box(v___x_990_);
lean_inc(v_toBind_996_);
v___f_1003_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_1003_, 0, v_str_1000_);
lean_closure_set(v___f_1003_, 1, v___x_1002_);
lean_closure_set(v___f_1003_, 2, v_env_991_);
lean_closure_set(v___f_1003_, 3, v_p_992_);
lean_closure_set(v___f_1003_, 4, v_text_989_);
lean_closure_set(v___f_1003_, 5, v_pos_998_);
lean_closure_set(v___f_1003_, 6, v___f_1001_);
lean_closure_set(v___f_1003_, 7, v_inst_993_);
lean_closure_set(v___f_1003_, 8, v_inst_994_);
lean_closure_set(v___f_1003_, 9, v_toPure_995_);
lean_closure_set(v___f_1003_, 10, v_toBind_996_);
lean_closure_set(v___f_1003_, 11, v_inst_997_);
v___x_1004_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v_getFileName_999_, v___f_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object* v_inst_1005_, lean_object* v_strLit_1006_, lean_object* v_text_1007_, lean_object* v___x_1008_, lean_object* v_env_1009_, lean_object* v_p_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_toPure_1013_, lean_object* v_toBind_1014_, lean_object* v_inst_1015_, lean_object* v_pos_1016_){
_start:
{
uint8_t v___x_1047__boxed_1017_; lean_object* v_res_1018_; 
v___x_1047__boxed_1017_ = lean_unbox(v___x_1008_);
v_res_1018_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_1005_, v_strLit_1006_, v_text_1007_, v___x_1047__boxed_1017_, v_env_1009_, v_p_1010_, v_inst_1011_, v_inst_1012_, v_toPure_1013_, v_toBind_1014_, v_inst_1015_, v_pos_1016_);
lean_dec(v_strLit_1006_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_1019_, lean_object* v_pos_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_apply_1(v___f_1019_, v_pos_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_text_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_strLit_1028_, lean_object* v_toBind_1029_, lean_object* v___f_1030_, lean_object* v_toPure_1031_, lean_object* v___f_1032_, lean_object* v_____r_1033_, lean_object* v_pos_1034_){
_start:
{
lean_object* v_source_1035_; uint32_t v___x_1036_; uint32_t v___x_1037_; uint8_t v___x_1038_; 
v_source_1035_ = lean_ctor_get(v_text_1025_, 0);
v___x_1036_ = lean_string_utf8_get(v_source_1035_, v_pos_1034_);
v___x_1037_ = 34;
v___x_1038_ = lean_uint32_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec(v___f_1032_);
lean_dec(v_toPure_1031_);
v___x_1039_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1);
v___x_1040_ = l_Lean_throwErrorAt___redArg(v_inst_1026_, v_inst_1027_, v_strLit_1028_, v___x_1039_);
v___x_1041_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1040_, v___f_1030_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___f_1030_);
lean_dec(v_strLit_1028_);
lean_dec_ref(v_inst_1027_);
lean_dec_ref(v_inst_1026_);
v___x_1042_ = lean_string_utf8_next(v_source_1035_, v_pos_1034_);
v___x_1043_ = lean_apply_2(v_toPure_1031_, lean_box(0), v___x_1042_);
v___x_1044_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1043_, v___f_1032_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_text_1045_, lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_strLit_1048_, lean_object* v_toBind_1049_, lean_object* v___f_1050_, lean_object* v_toPure_1051_, lean_object* v___f_1052_, lean_object* v_____r_1053_, lean_object* v_pos_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_text_1045_, v_inst_1046_, v_inst_1047_, v_strLit_1048_, v_toBind_1049_, v___f_1050_, v_toPure_1051_, v___f_1052_, v_____r_1053_, v_pos_1054_);
lean_dec(v_pos_1054_);
lean_dec_ref(v_text_1045_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v___f_1056_, lean_object* v_____s_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_apply_2(v___f_1056_, v___x_1058_, v_____s_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_1060_, lean_object* v_toPure_1061_, lean_object* v_toBind_1062_, lean_object* v___f_1063_, lean_object* v_b_1064_){
_start:
{
uint32_t v___x_1065_; uint32_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_string_utf8_get(v_source_1060_, v_b_1064_);
v___x_1066_ = 35;
v___x_1067_ = lean_uint32_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_b_1064_);
v___x_1069_ = lean_apply_2(v_toPure_1061_, lean_box(0), v___x_1068_);
v___x_1070_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1069_, v___f_1063_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_string_utf8_next(v_source_1060_, v_b_1064_);
lean_dec(v_b_1064_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = lean_apply_2(v_toPure_1061_, lean_box(0), v___x_1072_);
v___x_1074_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1073_, v___f_1063_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_1075_, lean_object* v_toPure_1076_, lean_object* v_toBind_1077_, lean_object* v___f_1078_, lean_object* v_b_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_1075_, v_toPure_1076_, v_toBind_1077_, v___f_1078_, v_b_1079_);
lean_dec_ref(v_source_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_1081_, lean_object* v___f_1082_, lean_object* v_toPure_1083_, lean_object* v_toBind_1084_, lean_object* v___f_1085_, lean_object* v_inst_1086_, lean_object* v___f_1087_, lean_object* v_____x_1088_){
_start:
{
lean_object* v_start_1089_; lean_object* v_source_1090_; uint32_t v___x_1091_; uint32_t v___x_1092_; uint8_t v___x_1093_; 
v_start_1089_ = lean_ctor_get(v_____x_1088_, 0);
lean_inc(v_start_1089_);
lean_dec_ref(v_____x_1088_);
v_source_1090_ = lean_ctor_get(v_text_1081_, 0);
lean_inc_ref(v_source_1090_);
lean_dec_ref(v_text_1081_);
v___x_1091_ = lean_string_utf8_get(v_source_1090_, v_start_1089_);
v___x_1092_ = 114;
v___x_1093_ = lean_uint32_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_source_1090_);
lean_dec(v___f_1087_);
lean_dec_ref(v_inst_1086_);
lean_dec(v___f_1085_);
lean_dec(v_toBind_1084_);
lean_dec(v_toPure_1083_);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_apply_2(v___f_1082_, v___x_1094_, v_start_1089_);
return v___x_1095_;
}
else
{
lean_object* v___f_1096_; lean_object* v_pos_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v___f_1082_);
lean_inc(v_toBind_1084_);
lean_inc_ref(v_source_1090_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_1096_, 0, v_source_1090_);
lean_closure_set(v___f_1096_, 1, v_toPure_1083_);
lean_closure_set(v___f_1096_, 2, v_toBind_1084_);
lean_closure_set(v___f_1096_, 3, v___f_1085_);
v_pos_1097_ = lean_string_utf8_next(v_source_1090_, v_start_1089_);
lean_dec(v_start_1089_);
lean_dec_ref(v_source_1090_);
v___x_1098_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_1086_, v___f_1096_, v_pos_1097_);
v___x_1099_ = lean_apply_4(v_toBind_1084_, lean_box(0), lean_box(0), v___x_1098_, v___f_1087_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_1100_, lean_object* v_strLit_1101_, lean_object* v_text_1102_, uint8_t v___x_1103_, lean_object* v_p_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_toPure_1107_, lean_object* v_toBind_1108_, lean_object* v_inst_1109_, lean_object* v___f_1110_, lean_object* v_env_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1112_ = lean_box(v___x_1103_);
lean_inc_n(v_toBind_1108_, 3);
lean_inc_n(v_toPure_1107_, 2);
lean_inc_ref(v_inst_1106_);
lean_inc_ref_n(v_inst_1105_, 3);
lean_inc_ref_n(v_text_1102_, 2);
lean_inc_n(v_strLit_1101_, 2);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1113_, 0, v_inst_1100_);
lean_closure_set(v___f_1113_, 1, v_strLit_1101_);
lean_closure_set(v___f_1113_, 2, v_text_1102_);
lean_closure_set(v___f_1113_, 3, v___x_1112_);
lean_closure_set(v___f_1113_, 4, v_env_1111_);
lean_closure_set(v___f_1113_, 5, v_p_1104_);
lean_closure_set(v___f_1113_, 6, v_inst_1105_);
lean_closure_set(v___f_1113_, 7, v_inst_1106_);
lean_closure_set(v___f_1113_, 8, v_toPure_1107_);
lean_closure_set(v___f_1113_, 9, v_toBind_1108_);
lean_closure_set(v___f_1113_, 10, v_inst_1109_);
v___f_1114_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1114_, 0, v___f_1113_);
lean_inc_ref(v___f_1114_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_1115_, 0, v_text_1102_);
lean_closure_set(v___f_1115_, 1, v_inst_1105_);
lean_closure_set(v___f_1115_, 2, v_inst_1106_);
lean_closure_set(v___f_1115_, 3, v_strLit_1101_);
lean_closure_set(v___f_1115_, 4, v_toBind_1108_);
lean_closure_set(v___f_1115_, 5, v___f_1114_);
lean_closure_set(v___f_1115_, 6, v_toPure_1107_);
lean_closure_set(v___f_1115_, 7, v___f_1114_);
lean_inc_ref(v___f_1115_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6), 2, 1);
lean_closure_set(v___f_1116_, 0, v___f_1115_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 8, 7);
lean_closure_set(v___f_1117_, 0, v_text_1102_);
lean_closure_set(v___f_1117_, 1, v___f_1115_);
lean_closure_set(v___f_1117_, 2, v_toPure_1107_);
lean_closure_set(v___f_1117_, 3, v_toBind_1108_);
lean_closure_set(v___f_1117_, 4, v___f_1110_);
lean_closure_set(v___f_1117_, 5, v_inst_1105_);
lean_closure_set(v___f_1117_, 6, v___f_1116_);
v___x_1118_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_1105_, v_strLit_1101_);
lean_dec(v_strLit_1101_);
v___x_1119_ = lean_apply_4(v_toBind_1108_, lean_box(0), lean_box(0), v___x_1118_, v___f_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_1120_, lean_object* v_strLit_1121_, lean_object* v_text_1122_, lean_object* v___x_1123_, lean_object* v_p_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_toPure_1127_, lean_object* v_toBind_1128_, lean_object* v_inst_1129_, lean_object* v___f_1130_, lean_object* v_env_1131_){
_start:
{
uint8_t v___x_1175__boxed_1132_; lean_object* v_res_1133_; 
v___x_1175__boxed_1132_ = lean_unbox(v___x_1123_);
v_res_1133_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_1120_, v_strLit_1121_, v_text_1122_, v___x_1175__boxed_1132_, v_p_1124_, v_inst_1125_, v_inst_1126_, v_toPure_1127_, v_toBind_1128_, v_inst_1129_, v___f_1130_, v_env_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_strLit_1136_, uint8_t v___x_1137_, lean_object* v_p_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_toPure_1141_, lean_object* v_toBind_1142_, lean_object* v_inst_1143_, lean_object* v___f_1144_, lean_object* v_text_1145_){
_start:
{
lean_object* v_getEnv_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v_getEnv_1146_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc(v_getEnv_1146_);
lean_dec_ref(v_inst_1134_);
v___x_1147_ = lean_box(v___x_1137_);
lean_inc(v_toBind_1142_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_1148_, 0, v_inst_1135_);
lean_closure_set(v___f_1148_, 1, v_strLit_1136_);
lean_closure_set(v___f_1148_, 2, v_text_1145_);
lean_closure_set(v___f_1148_, 3, v___x_1147_);
lean_closure_set(v___f_1148_, 4, v_p_1138_);
lean_closure_set(v___f_1148_, 5, v_inst_1139_);
lean_closure_set(v___f_1148_, 6, v_inst_1140_);
lean_closure_set(v___f_1148_, 7, v_toPure_1141_);
lean_closure_set(v___f_1148_, 8, v_toBind_1142_);
lean_closure_set(v___f_1148_, 9, v_inst_1143_);
lean_closure_set(v___f_1148_, 10, v___f_1144_);
v___x_1149_ = lean_apply_4(v_toBind_1142_, lean_box(0), lean_box(0), v_getEnv_1146_, v___f_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_strLit_1152_, lean_object* v___x_1153_, lean_object* v_p_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_toPure_1157_, lean_object* v_toBind_1158_, lean_object* v_inst_1159_, lean_object* v___f_1160_, lean_object* v_text_1161_){
_start:
{
uint8_t v___x_1210__boxed_1162_; lean_object* v_res_1163_; 
v___x_1210__boxed_1162_ = lean_unbox(v___x_1153_);
v_res_1163_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_1150_, v_inst_1151_, v_strLit_1152_, v___x_1210__boxed_1162_, v_p_1154_, v_inst_1155_, v_inst_1156_, v_toPure_1157_, v_toBind_1158_, v_inst_1159_, v___f_1160_, v_text_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_p_1170_, lean_object* v_strLit_1171_){
_start:
{
uint8_t v___x_1172_; uint8_t v___y_1174_; lean_object* v___x_1184_; 
v___x_1172_ = 1;
v___x_1184_ = l_Lean_Syntax_getPos_x3f(v_strLit_1171_, v___x_1172_);
if (lean_obj_tag(v___x_1184_) == 0)
{
v___y_1174_ = v___x_1172_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_1185_; 
lean_dec_ref_known(v___x_1184_, 1);
v___x_1185_ = 0;
v___y_1174_ = v___x_1185_;
goto v___jp_1173_;
}
v___jp_1173_:
{
if (v___y_1174_ == 0)
{
lean_object* v_toApplicative_1175_; lean_object* v_toBind_1176_; lean_object* v_toPure_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v_toApplicative_1175_ = lean_ctor_get(v_inst_1164_, 0);
v_toBind_1176_ = lean_ctor_get(v_inst_1164_, 1);
lean_inc_n(v_toBind_1176_, 2);
v_toPure_1177_ = lean_ctor_get(v_toApplicative_1175_, 1);
lean_inc_n(v_toPure_1177_, 2);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1178_, 0, v_toPure_1177_);
v___x_1179_ = lean_box(v___x_1172_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 12, 11);
lean_closure_set(v___f_1180_, 0, v_inst_1166_);
lean_closure_set(v___f_1180_, 1, v_inst_1168_);
lean_closure_set(v___f_1180_, 2, v_strLit_1171_);
lean_closure_set(v___f_1180_, 3, v___x_1179_);
lean_closure_set(v___f_1180_, 4, v_p_1170_);
lean_closure_set(v___f_1180_, 5, v_inst_1164_);
lean_closure_set(v___f_1180_, 6, v_inst_1167_);
lean_closure_set(v___f_1180_, 7, v_toPure_1177_);
lean_closure_set(v___f_1180_, 8, v_toBind_1176_);
lean_closure_set(v___f_1180_, 9, v_inst_1169_);
lean_closure_set(v___f_1180_, 10, v___f_1178_);
v___x_1181_ = lean_apply_4(v_toBind_1176_, lean_box(0), lean_box(0), v_inst_1165_, v___f_1180_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_inst_1165_);
v___x_1182_ = l_Lean_TSyntax_getString(v_strLit_1171_);
lean_dec(v_strLit_1171_);
v___x_1183_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_1164_, v_inst_1166_, v_inst_1167_, v_inst_1168_, v_inst_1169_, v_p_1170_, v___x_1182_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_p_1193_, lean_object* v_strLit_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_1187_, v_inst_1188_, v_inst_1189_, v_inst_1190_, v_inst_1191_, v_inst_1192_, v_p_1193_, v_strLit_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object* v_s_1196_, lean_object* v_toPure_1197_, uint8_t v_err_1198_){
_start:
{
lean_object* v_stxStack_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_stxStack_1199_ = lean_ctor_get(v_s_1196_, 0);
v___x_1200_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1199_);
v___x_1201_ = lean_box(v_err_1198_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_apply_2(v_toPure_1197_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object* v_s_1204_, lean_object* v_toPure_1205_, lean_object* v_err_1206_){
_start:
{
uint8_t v_err_boxed_1207_; lean_object* v_res_1208_; 
v_err_boxed_1207_ = lean_unbox(v_err_1206_);
v_res_1208_ = l_Lean_Doc_parseContent_x27___redArg___lam__0(v_s_1204_, v_toPure_1205_, v_err_boxed_1207_);
lean_dec_ref(v_s_1204_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object* v___f_1209_, uint8_t v_err_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_box(v_err_1210_);
v___x_1212_ = lean_apply_1(v___f_1209_, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object* v___f_1213_, lean_object* v_err_1214_){
_start:
{
uint8_t v_err_boxed_1215_; lean_object* v_res_1216_; 
v_err_boxed_1215_ = lean_unbox(v_err_1214_);
v_res_1216_ = l_Lean_Doc_parseContent_x27___redArg___lam__1(v___f_1213_, v_err_boxed_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object* v_toPure_1217_, uint8_t v___x_1218_, lean_object* v_toBind_1219_, lean_object* v___f_1220_, lean_object* v_____r_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(v___x_1218_);
v___x_1223_ = lean_apply_2(v_toPure_1217_, lean_box(0), v___x_1222_);
v___x_1224_ = lean_apply_4(v_toBind_1219_, lean_box(0), lean_box(0), v___x_1223_, v___f_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object* v_toPure_1225_, lean_object* v___x_1226_, lean_object* v_toBind_1227_, lean_object* v___f_1228_, lean_object* v_____r_1229_){
_start:
{
uint8_t v___x_798__boxed_1230_; lean_object* v_res_1231_; 
v___x_798__boxed_1230_ = lean_unbox(v___x_1226_);
v_res_1231_ = l_Lean_Doc_parseContent_x27___redArg___lam__2(v_toPure_1225_, v___x_798__boxed_1230_, v_toBind_1227_, v___f_1228_, v_____r_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object* v_env_1232_, lean_object* v_p_1233_, lean_object* v_ictx_1234_, lean_object* v_s_1235_, lean_object* v_toPure_1236_, uint8_t v___x_1237_, lean_object* v_toBind_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, uint8_t v___y_1243_, lean_object* v_____do__lift_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_s_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_box(0);
lean_inc_ref(v_env_1232_);
v___x_1247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1247_, 0, v_env_1232_);
lean_ctor_set(v___x_1247_, 1, v_____do__lift_1244_);
lean_ctor_set(v___x_1247_, 2, v___x_1245_);
lean_ctor_set(v___x_1247_, 3, v___x_1246_);
v___x_1248_ = l_Lean_Parser_getTokenTable(v_env_1232_);
lean_inc_ref(v_ictx_1234_);
v_s_1249_ = l_Lean_Parser_ParserFn_run(v_p_1233_, v_ictx_1234_, v___x_1247_, v___x_1248_, v_s_1235_);
lean_inc(v_toPure_1236_);
lean_inc_ref_n(v_s_1249_, 2);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1250_, 0, v_s_1249_);
lean_closure_set(v___f_1250_, 1, v_toPure_1236_);
v___x_1251_ = l_Lean_Parser_ParserState_allErrors(v_s_1249_);
v___x_1252_ = lean_array_get_size(v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_nat_dec_eq(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1255_, 0, v___f_1250_);
v___x_1256_ = lean_box(v___x_1237_);
lean_inc(v_toBind_1238_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1257_, 0, v_toPure_1236_);
lean_closure_set(v___f_1257_, 1, v___x_1256_);
lean_closure_set(v___f_1257_, 2, v_toBind_1238_);
lean_closure_set(v___f_1257_, 3, v___f_1255_);
v___x_1258_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1234_, v_s_1249_);
v___x_1259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
v___x_1260_ = l_Lean_MessageData_ofFormat(v___x_1259_);
v___x_1261_ = l_Lean_logError___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v___x_1260_);
v___x_1262_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1261_, v___f_1257_);
return v___x_1262_;
}
else
{
lean_object* v_pos_1263_; uint8_t v___x_1264_; 
v_pos_1263_ = lean_ctor_get(v_s_1249_, 2);
lean_inc(v_pos_1263_);
v___x_1264_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1234_, v_pos_1263_);
lean_dec(v_pos_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1265_, 0, v___f_1250_);
v___x_1266_ = lean_box(v___x_1237_);
lean_inc(v_toBind_1238_);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1267_, 0, v_toPure_1236_);
lean_closure_set(v___f_1267_, 1, v___x_1266_);
lean_closure_set(v___f_1267_, 2, v_toBind_1238_);
lean_closure_set(v___f_1267_, 3, v___f_1265_);
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1269_ = l_Lean_Parser_ParserState_mkError(v_s_1249_, v___x_1268_);
v___x_1270_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1234_, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
v___x_1273_ = l_Lean_logError___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v___x_1272_);
v___x_1274_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1273_, v___f_1267_);
return v___x_1274_;
}
else
{
lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_s_1249_);
lean_dec(v_inst_1242_);
lean_dec(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_ictx_1234_);
v___f_1275_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1275_, 0, v___f_1250_);
v___x_1276_ = lean_box(v___y_1243_);
v___x_1277_ = lean_apply_2(v_toPure_1236_, lean_box(0), v___x_1276_);
v___x_1278_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1277_, v___f_1275_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object* v_env_1279_, lean_object* v_p_1280_, lean_object* v_ictx_1281_, lean_object* v_s_1282_, lean_object* v_toPure_1283_, lean_object* v___x_1284_, lean_object* v_toBind_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v___y_1290_, lean_object* v_____do__lift_1291_){
_start:
{
uint8_t v___x_814__boxed_1292_; uint8_t v___y_819__boxed_1293_; lean_object* v_res_1294_; 
v___x_814__boxed_1292_ = lean_unbox(v___x_1284_);
v___y_819__boxed_1293_ = lean_unbox(v___y_1290_);
v_res_1294_ = l_Lean_Doc_parseContent_x27___redArg___lam__6(v_env_1279_, v_p_1280_, v_ictx_1281_, v_s_1282_, v_toPure_1283_, v___x_814__boxed_1292_, v_toBind_1285_, v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v___y_819__boxed_1293_, v_____do__lift_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object* v_source_1295_, uint8_t v___x_1296_, lean_object* v___y_1297_, lean_object* v_env_1298_, lean_object* v_p_1299_, lean_object* v_toPure_1300_, lean_object* v_toBind_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, uint8_t v___y_1306_, lean_object* v_tok_1307_, lean_object* v___x_1308_, lean_object* v_____do__lift_1309_){
_start:
{
lean_object* v_ictx_1310_; lean_object* v___x_1311_; lean_object* v___y_1313_; lean_object* v___x_1319_; 
lean_inc_ref(v_source_1295_);
v_ictx_1310_ = l_Lean_Parser_mkInputContext___redArg(v_source_1295_, v_____do__lift_1309_, v___x_1296_, v___y_1297_);
v___x_1311_ = l_Lean_Parser_mkParserState(v_source_1295_);
lean_dec_ref(v_source_1295_);
v___x_1319_ = l_Lean_Syntax_getPos_x3f(v_tok_1307_, v___x_1296_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1321_ = l_panic___redArg(v___x_1308_, v___x_1320_);
v___y_1313_ = v___x_1321_;
goto v___jp_1312_;
}
else
{
lean_object* v_val_1322_; 
v_val_1322_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v___x_1319_, 1);
v___y_1313_ = v_val_1322_;
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v_s_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; 
v_s_1314_ = l_Lean_Parser_ParserState_setPos(v___x_1311_, v___y_1313_);
v___x_1315_ = lean_box(v___x_1296_);
v___x_1316_ = lean_box(v___y_1306_);
lean_inc(v_inst_1305_);
lean_inc(v_toBind_1301_);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1317_, 0, v_env_1298_);
lean_closure_set(v___f_1317_, 1, v_p_1299_);
lean_closure_set(v___f_1317_, 2, v_ictx_1310_);
lean_closure_set(v___f_1317_, 3, v_s_1314_);
lean_closure_set(v___f_1317_, 4, v_toPure_1300_);
lean_closure_set(v___f_1317_, 5, v___x_1315_);
lean_closure_set(v___f_1317_, 6, v_toBind_1301_);
lean_closure_set(v___f_1317_, 7, v_inst_1302_);
lean_closure_set(v___f_1317_, 8, v_inst_1303_);
lean_closure_set(v___f_1317_, 9, v_inst_1304_);
lean_closure_set(v___f_1317_, 10, v_inst_1305_);
lean_closure_set(v___f_1317_, 11, v___x_1316_);
v___x_1318_ = lean_apply_4(v_toBind_1301_, lean_box(0), lean_box(0), v_inst_1305_, v___f_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object* v_source_1323_, lean_object* v___x_1324_, lean_object* v___y_1325_, lean_object* v_env_1326_, lean_object* v_p_1327_, lean_object* v_toPure_1328_, lean_object* v_toBind_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v___y_1334_, lean_object* v_tok_1335_, lean_object* v___x_1336_, lean_object* v_____do__lift_1337_){
_start:
{
uint8_t v___x_908__boxed_1338_; uint8_t v___y_914__boxed_1339_; lean_object* v_res_1340_; 
v___x_908__boxed_1338_ = lean_unbox(v___x_1324_);
v___y_914__boxed_1339_ = lean_unbox(v___y_1334_);
v_res_1340_ = l_Lean_Doc_parseContent_x27___redArg___lam__3(v_source_1323_, v___x_908__boxed_1338_, v___y_1325_, v_env_1326_, v_p_1327_, v_toPure_1328_, v_toBind_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_inst_1333_, v___y_914__boxed_1339_, v_tok_1335_, v___x_1336_, v_____do__lift_1337_);
lean_dec(v___x_1336_);
lean_dec(v_tok_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object* v_text_1341_, lean_object* v_inst_1342_, uint8_t v___x_1343_, lean_object* v_p_1344_, lean_object* v_toPure_1345_, lean_object* v_toBind_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, uint8_t v___y_1350_, lean_object* v_tok_1351_, lean_object* v___x_1352_, lean_object* v_env_1353_){
_start:
{
lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1363_; lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Syntax_getTailPos_x3f(v_tok_1351_, v___x_1343_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1369_ = l_panic___redArg(v___x_1352_, v___x_1368_);
v___y_1363_ = v___x_1369_;
goto v___jp_1362_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1367_, 1);
v___y_1363_ = v_val_1370_;
goto v___jp_1362_;
}
v___jp_1354_:
{
lean_object* v_getFileName_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; 
v_getFileName_1357_ = lean_ctor_get(v_inst_1342_, 2);
lean_inc(v_getFileName_1357_);
v___x_1358_ = lean_box(v___x_1343_);
v___x_1359_ = lean_box(v___y_1350_);
lean_inc(v_toBind_1346_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1360_, 0, v___y_1355_);
lean_closure_set(v___f_1360_, 1, v___x_1358_);
lean_closure_set(v___f_1360_, 2, v___y_1356_);
lean_closure_set(v___f_1360_, 3, v_env_1353_);
lean_closure_set(v___f_1360_, 4, v_p_1344_);
lean_closure_set(v___f_1360_, 5, v_toPure_1345_);
lean_closure_set(v___f_1360_, 6, v_toBind_1346_);
lean_closure_set(v___f_1360_, 7, v_inst_1347_);
lean_closure_set(v___f_1360_, 8, v_inst_1342_);
lean_closure_set(v___f_1360_, 9, v_inst_1348_);
lean_closure_set(v___f_1360_, 10, v_inst_1349_);
lean_closure_set(v___f_1360_, 11, v___x_1359_);
lean_closure_set(v___f_1360_, 12, v_tok_1351_);
lean_closure_set(v___f_1360_, 13, v___x_1352_);
v___x_1361_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v_getFileName_1357_, v___f_1360_);
return v___x_1361_;
}
v___jp_1362_:
{
lean_object* v_source_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_source_1364_ = lean_ctor_get(v_text_1341_, 0);
lean_inc_ref(v_source_1364_);
lean_dec_ref(v_text_1341_);
v___x_1365_ = lean_string_utf8_byte_size(v_source_1364_);
v___x_1366_ = lean_nat_dec_le(v___y_1363_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_dec(v___y_1363_);
v___y_1355_ = v_source_1364_;
v___y_1356_ = v___x_1365_;
goto v___jp_1354_;
}
else
{
v___y_1355_ = v_source_1364_;
v___y_1356_ = v___y_1363_;
goto v___jp_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object* v_text_1371_, lean_object* v_inst_1372_, lean_object* v___x_1373_, lean_object* v_p_1374_, lean_object* v_toPure_1375_, lean_object* v_toBind_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v___y_1380_, lean_object* v_tok_1381_, lean_object* v___x_1382_, lean_object* v_env_1383_){
_start:
{
uint8_t v___x_973__boxed_1384_; uint8_t v___y_977__boxed_1385_; lean_object* v_res_1386_; 
v___x_973__boxed_1384_ = lean_unbox(v___x_1373_);
v___y_977__boxed_1385_ = lean_unbox(v___y_1380_);
v_res_1386_ = l_Lean_Doc_parseContent_x27___redArg___lam__4(v_text_1371_, v_inst_1372_, v___x_973__boxed_1384_, v_p_1374_, v_toPure_1375_, v_toBind_1376_, v_inst_1377_, v_inst_1378_, v_inst_1379_, v___y_977__boxed_1385_, v_tok_1381_, v___x_1382_, v_env_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object* v_inst_1387_, lean_object* v_inst_1388_, uint8_t v___x_1389_, lean_object* v_p_1390_, lean_object* v_toPure_1391_, lean_object* v_toBind_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, uint8_t v___y_1396_, lean_object* v_tok_1397_, lean_object* v___x_1398_, lean_object* v_text_1399_){
_start:
{
lean_object* v_getEnv_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v_getEnv_1400_ = lean_ctor_get(v_inst_1387_, 0);
lean_inc(v_getEnv_1400_);
lean_dec_ref(v_inst_1387_);
v___x_1401_ = lean_box(v___x_1389_);
v___x_1402_ = lean_box(v___y_1396_);
lean_inc(v_toBind_1392_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed), 13, 12);
lean_closure_set(v___f_1403_, 0, v_text_1399_);
lean_closure_set(v___f_1403_, 1, v_inst_1388_);
lean_closure_set(v___f_1403_, 2, v___x_1401_);
lean_closure_set(v___f_1403_, 3, v_p_1390_);
lean_closure_set(v___f_1403_, 4, v_toPure_1391_);
lean_closure_set(v___f_1403_, 5, v_toBind_1392_);
lean_closure_set(v___f_1403_, 6, v_inst_1393_);
lean_closure_set(v___f_1403_, 7, v_inst_1394_);
lean_closure_set(v___f_1403_, 8, v_inst_1395_);
lean_closure_set(v___f_1403_, 9, v___x_1402_);
lean_closure_set(v___f_1403_, 10, v_tok_1397_);
lean_closure_set(v___f_1403_, 11, v___x_1398_);
v___x_1404_ = lean_apply_4(v_toBind_1392_, lean_box(0), lean_box(0), v_getEnv_1400_, v___f_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v___x_1407_, lean_object* v_p_1408_, lean_object* v_toPure_1409_, lean_object* v_toBind_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v___y_1414_, lean_object* v_tok_1415_, lean_object* v___x_1416_, lean_object* v_text_1417_){
_start:
{
uint8_t v___x_1030__boxed_1418_; uint8_t v___y_1034__boxed_1419_; lean_object* v_res_1420_; 
v___x_1030__boxed_1418_ = lean_unbox(v___x_1407_);
v___y_1034__boxed_1419_ = lean_unbox(v___y_1414_);
v_res_1420_ = l_Lean_Doc_parseContent_x27___redArg___lam__5(v_inst_1405_, v_inst_1406_, v___x_1030__boxed_1418_, v_p_1408_, v_toPure_1409_, v_toBind_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v___y_1034__boxed_1419_, v_tok_1415_, v___x_1416_, v_text_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object* v_st_1421_, lean_object* v_toPure_1422_, uint8_t v_err_1423_){
_start:
{
lean_object* v_stxStack_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_stxStack_1424_ = lean_ctor_get(v_st_1421_, 0);
v___x_1425_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1424_);
v___x_1426_ = lean_box(v_err_1423_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_apply_2(v_toPure_1422_, lean_box(0), v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object* v_st_1429_, lean_object* v_toPure_1430_, lean_object* v_err_1431_){
_start:
{
uint8_t v_err_boxed_1432_; lean_object* v_res_1433_; 
v_err_boxed_1432_ = lean_unbox(v_err_1431_);
v_res_1433_ = l_Lean_Doc_parseContent_x27___redArg___lam__7(v_st_1429_, v_toPure_1430_, v_err_boxed_1432_);
lean_dec_ref(v_st_1429_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object* v_env_1434_, lean_object* v_contents_1435_, lean_object* v_p_1436_, lean_object* v_ictx_1437_, lean_object* v_toPure_1438_, uint8_t v___x_1439_, lean_object* v_toBind_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_____do__lift_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_st_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = lean_box(0);
lean_inc_ref(v_env_1434_);
v___x_1448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1448_, 0, v_env_1434_);
lean_ctor_set(v___x_1448_, 1, v_____do__lift_1445_);
lean_ctor_set(v___x_1448_, 2, v___x_1446_);
lean_ctor_set(v___x_1448_, 3, v___x_1447_);
v___x_1449_ = l_Lean_Parser_getTokenTable(v_env_1434_);
v___x_1450_ = l_Lean_Parser_mkParserState(v_contents_1435_);
lean_inc_ref(v_ictx_1437_);
v_st_1451_ = l_Lean_Parser_ParserFn_run(v_p_1436_, v_ictx_1437_, v___x_1448_, v___x_1449_, v___x_1450_);
lean_inc(v_toPure_1438_);
lean_inc_ref_n(v_st_1451_, 2);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1452_, 0, v_st_1451_);
lean_closure_set(v___f_1452_, 1, v_toPure_1438_);
v___x_1453_ = l_Lean_Parser_ParserState_allErrors(v_st_1451_);
v___x_1454_ = lean_array_get_size(v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_nat_dec_eq(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1457_, 0, v___f_1452_);
v___x_1458_ = lean_box(v___x_1439_);
lean_inc(v_toBind_1440_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1459_, 0, v_toPure_1438_);
lean_closure_set(v___f_1459_, 1, v___x_1458_);
lean_closure_set(v___f_1459_, 2, v_toBind_1440_);
lean_closure_set(v___f_1459_, 3, v___f_1457_);
v___x_1460_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1437_, v_st_1451_);
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = l_Lean_MessageData_ofFormat(v___x_1461_);
v___x_1463_ = l_Lean_logError___redArg(v_inst_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v___x_1462_);
v___x_1464_ = lean_apply_4(v_toBind_1440_, lean_box(0), lean_box(0), v___x_1463_, v___f_1459_);
return v___x_1464_;
}
else
{
lean_object* v_pos_1465_; uint8_t v___x_1466_; 
v_pos_1465_ = lean_ctor_get(v_st_1451_, 2);
lean_inc(v_pos_1465_);
v___x_1466_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1437_, v_pos_1465_);
lean_dec(v_pos_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1467_, 0, v___f_1452_);
v___x_1468_ = lean_box(v___x_1439_);
lean_inc(v_toBind_1440_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1469_, 0, v_toPure_1438_);
lean_closure_set(v___f_1469_, 1, v___x_1468_);
lean_closure_set(v___f_1469_, 2, v_toBind_1440_);
lean_closure_set(v___f_1469_, 3, v___f_1467_);
v___x_1470_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1471_ = l_Lean_Parser_ParserState_mkError(v_st_1451_, v___x_1470_);
v___x_1472_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1437_, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
v___x_1474_ = l_Lean_MessageData_ofFormat(v___x_1473_);
v___x_1475_ = l_Lean_logError___redArg(v_inst_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v___x_1474_);
v___x_1476_ = lean_apply_4(v_toBind_1440_, lean_box(0), lean_box(0), v___x_1475_, v___f_1469_);
return v___x_1476_;
}
else
{
lean_object* v___f_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref(v_st_1451_);
lean_dec(v_inst_1444_);
lean_dec(v_inst_1443_);
lean_dec_ref(v_inst_1442_);
lean_dec_ref(v_inst_1441_);
lean_dec_ref(v_ictx_1437_);
v___f_1477_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1477_, 0, v___f_1452_);
v___x_1478_ = 0;
v___x_1479_ = lean_box(v___x_1478_);
v___x_1480_ = lean_apply_2(v_toPure_1438_, lean_box(0), v___x_1479_);
v___x_1481_ = lean_apply_4(v_toBind_1440_, lean_box(0), lean_box(0), v___x_1480_, v___f_1477_);
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object* v_env_1482_, lean_object* v_contents_1483_, lean_object* v_p_1484_, lean_object* v_ictx_1485_, lean_object* v_toPure_1486_, lean_object* v___x_1487_, lean_object* v_toBind_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_____do__lift_1493_){
_start:
{
uint8_t v___x_1069__boxed_1494_; lean_object* v_res_1495_; 
v___x_1069__boxed_1494_ = lean_unbox(v___x_1487_);
v_res_1495_ = l_Lean_Doc_parseContent_x27___redArg___lam__13(v_env_1482_, v_contents_1483_, v_p_1484_, v_ictx_1485_, v_toPure_1486_, v___x_1069__boxed_1494_, v_toBind_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_____do__lift_1493_);
lean_dec_ref(v_contents_1483_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object* v_contents_1496_, uint8_t v___x_1497_, lean_object* v_env_1498_, lean_object* v_p_1499_, lean_object* v_toPure_1500_, lean_object* v_toBind_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_____do__lift_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v_ictx_1508_; lean_object* v___x_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; 
v___x_1507_ = lean_string_utf8_byte_size(v_contents_1496_);
lean_inc_ref(v_contents_1496_);
v_ictx_1508_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1496_, v_____do__lift_1506_, v___x_1497_, v___x_1507_);
v___x_1509_ = lean_box(v___x_1497_);
lean_inc(v_inst_1505_);
lean_inc(v_toBind_1501_);
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_1510_, 0, v_env_1498_);
lean_closure_set(v___f_1510_, 1, v_contents_1496_);
lean_closure_set(v___f_1510_, 2, v_p_1499_);
lean_closure_set(v___f_1510_, 3, v_ictx_1508_);
lean_closure_set(v___f_1510_, 4, v_toPure_1500_);
lean_closure_set(v___f_1510_, 5, v___x_1509_);
lean_closure_set(v___f_1510_, 6, v_toBind_1501_);
lean_closure_set(v___f_1510_, 7, v_inst_1502_);
lean_closure_set(v___f_1510_, 8, v_inst_1503_);
lean_closure_set(v___f_1510_, 9, v_inst_1504_);
lean_closure_set(v___f_1510_, 10, v_inst_1505_);
v___x_1511_ = lean_apply_4(v_toBind_1501_, lean_box(0), lean_box(0), v_inst_1505_, v___f_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object* v_contents_1512_, lean_object* v___x_1513_, lean_object* v_env_1514_, lean_object* v_p_1515_, lean_object* v_toPure_1516_, lean_object* v_toBind_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_____do__lift_1522_){
_start:
{
uint8_t v___x_1155__boxed_1523_; lean_object* v_res_1524_; 
v___x_1155__boxed_1523_ = lean_unbox(v___x_1513_);
v_res_1524_ = l_Lean_Doc_parseContent_x27___redArg___lam__8(v_contents_1512_, v___x_1155__boxed_1523_, v_env_1514_, v_p_1515_, v_toPure_1516_, v_toBind_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_____do__lift_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object* v_inst_1525_, lean_object* v_contents_1526_, uint8_t v___x_1527_, lean_object* v_p_1528_, lean_object* v_toPure_1529_, lean_object* v_toBind_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_env_1534_){
_start:
{
lean_object* v_getFileName_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; 
v_getFileName_1535_ = lean_ctor_get(v_inst_1525_, 2);
lean_inc(v_getFileName_1535_);
v___x_1536_ = lean_box(v___x_1527_);
lean_inc(v_toBind_1530_);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_1537_, 0, v_contents_1526_);
lean_closure_set(v___f_1537_, 1, v___x_1536_);
lean_closure_set(v___f_1537_, 2, v_env_1534_);
lean_closure_set(v___f_1537_, 3, v_p_1528_);
lean_closure_set(v___f_1537_, 4, v_toPure_1529_);
lean_closure_set(v___f_1537_, 5, v_toBind_1530_);
lean_closure_set(v___f_1537_, 6, v_inst_1531_);
lean_closure_set(v___f_1537_, 7, v_inst_1525_);
lean_closure_set(v___f_1537_, 8, v_inst_1532_);
lean_closure_set(v___f_1537_, 9, v_inst_1533_);
v___x_1538_ = lean_apply_4(v_toBind_1530_, lean_box(0), lean_box(0), v_getFileName_1535_, v___f_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object* v_inst_1539_, lean_object* v_contents_1540_, lean_object* v___x_1541_, lean_object* v_p_1542_, lean_object* v_toPure_1543_, lean_object* v_toBind_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_env_1548_){
_start:
{
uint8_t v___x_1182__boxed_1549_; lean_object* v_res_1550_; 
v___x_1182__boxed_1549_ = lean_unbox(v___x_1541_);
v_res_1550_ = l_Lean_Doc_parseContent_x27___redArg___lam__9(v_inst_1539_, v_contents_1540_, v___x_1182__boxed_1549_, v_p_1542_, v_toPure_1543_, v_toBind_1544_, v_inst_1545_, v_inst_1546_, v_inst_1547_, v_env_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_p_1557_, lean_object* v_tok_1558_, lean_object* v_contents_1559_){
_start:
{
lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___y_1563_; lean_object* v___x_1578_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = 1;
v___x_1578_ = l_Lean_Syntax_getPos_x3f(v_tok_1558_, v___x_1561_);
if (lean_obj_tag(v___x_1578_) == 0)
{
v___y_1563_ = v___x_1561_;
goto v___jp_1562_;
}
else
{
uint8_t v___x_1579_; 
lean_dec_ref_known(v___x_1578_, 1);
v___x_1579_ = 0;
v___y_1563_ = v___x_1579_;
goto v___jp_1562_;
}
v___jp_1562_:
{
if (v___y_1563_ == 0)
{
lean_object* v_toApplicative_1564_; lean_object* v_toBind_1565_; lean_object* v_toPure_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
v_toApplicative_1564_ = lean_ctor_get(v_inst_1551_, 0);
lean_dec_ref(v_contents_1559_);
v_toBind_1565_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc_n(v_toBind_1565_, 2);
v_toPure_1566_ = lean_ctor_get(v_toApplicative_1564_, 1);
lean_inc(v_toPure_1566_);
v___x_1567_ = lean_box(v___x_1561_);
v___x_1568_ = lean_box(v___y_1563_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1569_, 0, v_inst_1553_);
lean_closure_set(v___f_1569_, 1, v_inst_1555_);
lean_closure_set(v___f_1569_, 2, v___x_1567_);
lean_closure_set(v___f_1569_, 3, v_p_1557_);
lean_closure_set(v___f_1569_, 4, v_toPure_1566_);
lean_closure_set(v___f_1569_, 5, v_toBind_1565_);
lean_closure_set(v___f_1569_, 6, v_inst_1551_);
lean_closure_set(v___f_1569_, 7, v_inst_1554_);
lean_closure_set(v___f_1569_, 8, v_inst_1556_);
lean_closure_set(v___f_1569_, 9, v___x_1568_);
lean_closure_set(v___f_1569_, 10, v_tok_1558_);
lean_closure_set(v___f_1569_, 11, v___x_1560_);
v___x_1570_ = lean_apply_4(v_toBind_1565_, lean_box(0), lean_box(0), v_inst_1552_, v___f_1569_);
return v___x_1570_;
}
else
{
lean_object* v_toApplicative_1571_; lean_object* v_toBind_1572_; lean_object* v_toPure_1573_; lean_object* v_getEnv_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; 
v_toApplicative_1571_ = lean_ctor_get(v_inst_1551_, 0);
lean_dec(v_tok_1558_);
lean_dec(v_inst_1552_);
v_toBind_1572_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc_n(v_toBind_1572_, 2);
v_toPure_1573_ = lean_ctor_get(v_toApplicative_1571_, 1);
lean_inc(v_toPure_1573_);
v_getEnv_1574_ = lean_ctor_get(v_inst_1553_, 0);
lean_inc(v_getEnv_1574_);
lean_dec_ref(v_inst_1553_);
v___x_1575_ = lean_box(v___x_1561_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1576_, 0, v_inst_1555_);
lean_closure_set(v___f_1576_, 1, v_contents_1559_);
lean_closure_set(v___f_1576_, 2, v___x_1575_);
lean_closure_set(v___f_1576_, 3, v_p_1557_);
lean_closure_set(v___f_1576_, 4, v_toPure_1573_);
lean_closure_set(v___f_1576_, 5, v_toBind_1572_);
lean_closure_set(v___f_1576_, 6, v_inst_1551_);
lean_closure_set(v___f_1576_, 7, v_inst_1554_);
lean_closure_set(v___f_1576_, 8, v_inst_1556_);
v___x_1577_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v_getEnv_1574_, v___f_1576_);
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object* v_m_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_p_1587_, lean_object* v_tok_1588_, lean_object* v_contents_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1581_, v_inst_1582_, v_inst_1583_, v_inst_1584_, v_inst_1585_, v_inst_1586_, v_p_1587_, v_tok_1588_, v_contents_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_p_1597_, lean_object* v_c_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = l_Lean_TSyntax_getVersoCode(v_c_1598_);
v___x_1600_ = l_Lean_Doc_parseContent___redArg(v_inst_1591_, v_inst_1592_, v_inst_1593_, v_inst_1594_, v_inst_1595_, v_inst_1596_, v_p_1597_, v_c_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object* v_m_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_p_1608_, lean_object* v_c_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Doc_parseVersoCode___redArg(v_inst_1602_, v_inst_1603_, v_inst_1604_, v_inst_1605_, v_inst_1606_, v_inst_1607_, v_p_1608_, v_c_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_p_1617_, lean_object* v_c_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = l_Lean_TSyntax_getVersoCodeBlock(v_c_1618_);
v___x_1620_ = l_Lean_Doc_parseContent___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_inst_1616_, v_p_1617_, v_c_1618_, v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object* v_m_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_p_1628_, lean_object* v_c_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Doc_parseVersoCodeBlock___redArg(v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_p_1628_, v_c_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_p_1637_, lean_object* v_c_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l_Lean_TSyntax_getVersoCode(v_c_1638_);
v___x_1640_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_inst_1636_, v_p_1637_, v_c_1638_, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object* v_m_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_p_1648_, lean_object* v_c_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Doc_parseVersoCode_x27___redArg(v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v_inst_1647_, v_p_1648_, v_c_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_p_1657_, lean_object* v_s_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = l_Lean_TSyntax_getString(v_s_1658_);
v___x_1660_ = l_Lean_Doc_parseContent___redArg(v_inst_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_p_1657_, v_s_1658_, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_p_1668_, lean_object* v_s_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Doc_parseStrLit___redArg(v_inst_1662_, v_inst_1663_, v_inst_1664_, v_inst_1665_, v_inst_1666_, v_inst_1667_, v_p_1668_, v_s_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_p_1677_, lean_object* v_s_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = l_Lean_TSyntax_getString(v_s_1678_);
v___x_1680_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_p_1677_, v_s_1678_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_p_1688_, lean_object* v_s_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1682_, v_inst_1683_, v_inst_1684_, v_inst_1685_, v_inst_1686_, v_inst_1687_, v_p_1688_, v_s_1689_);
return v___x_1690_;
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
