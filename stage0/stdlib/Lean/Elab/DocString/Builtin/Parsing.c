// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Parsing
// Imports: public import Lean.Parser.Extension public import Init.While import Init.Data.Array.Attach import Init.Data.Array.Mem
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
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Not a quoted string literal"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2));
v___x_5_ = lean_unsigned_to_nat(14u);
v___x_6_ = lean_unsigned_to_nat(22u);
v___x_7_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1));
v___x_8_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0));
v___x_9_ = l_mkPanicMessageWithDecl(v___x_8_, v___x_7_, v___x_6_, v___x_5_, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object* v_inst_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___y_29_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = 1;
v___x_34_ = l_Lean_Syntax_getPos_x3f(v_s_11_, v___x_27_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_36_ = l_panic___redArg(v___x_26_, v___x_35_);
v___y_29_ = v___x_36_;
goto v___jp_28_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v___x_34_);
v___y_29_ = v_val_37_;
goto v___jp_28_;
}
v___jp_12_:
{
lean_object* v_toApplicative_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_toApplicative_15_ = lean_ctor_get(v_inst_10_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v_inst_10_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v_inst_10_, 1);
lean_dec(v_unused_25_);
v___x_17_ = v_inst_10_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_toApplicative_15_);
lean_dec(v_inst_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_toPure_19_; lean_object* v___x_21_; 
v_toPure_19_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_inc(v_toPure_19_);
lean_dec_ref(v_toApplicative_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___y_14_);
lean_ctor_set(v___x_17_, 0, v___y_13_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___y_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___y_14_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_2(v_toPure_19_, lean_box(0), v___x_21_);
return v___x_22_;
}
}
}
v___jp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Syntax_getTailPos_x3f(v_s_11_, v___x_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_32_ = l_panic___redArg(v___x_26_, v___x_31_);
v___y_13_ = v___y_29_;
v___y_14_ = v___x_32_;
goto v___jp_12_;
}
else
{
lean_object* v_val_33_; 
v_val_33_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_val_33_);
lean_dec_ref(v___x_30_);
v___y_13_ = v___y_29_;
v___y_14_ = v_val_33_;
goto v___jp_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object* v_inst_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_38_, v_s_39_);
lean_dec(v_s_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object* v_m_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_s_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_42_, v_s_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(v_m_46_, v_inst_47_, v_inst_48_, v_s_49_);
lean_dec(v_s_49_);
lean_dec(v_inst_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object* v_env_52_, lean_object* v_p_53_, lean_object* v_ictx_54_, lean_object* v_s_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_toApplicative_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_s_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_box(0);
lean_inc_ref(v_env_52_);
v___x_62_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_62_, 0, v_env_52_);
lean_ctor_set(v___x_62_, 1, v_____do__lift_59_);
lean_ctor_set(v___x_62_, 2, v___x_60_);
lean_ctor_set(v___x_62_, 3, v___x_61_);
v___x_63_ = l_Lean_Parser_getTokenTable(v_env_52_);
lean_inc_ref(v_ictx_54_);
v_s_64_ = l_Lean_Parser_ParserFn_run(v_p_53_, v_ictx_54_, v___x_62_, v___x_63_, v_s_55_);
lean_inc_ref(v_s_64_);
v___x_65_ = l_Lean_Parser_ParserState_allErrors(v_s_64_);
v___x_66_ = lean_array_get_size(v___x_65_);
lean_dec_ref(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec_ref(v_toApplicative_58_);
v___x_69_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_54_, v_s_64_);
v___x_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
v___x_71_ = l_Lean_MessageData_ofFormat(v___x_70_);
v___x_72_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_stxStack_73_; lean_object* v_pos_74_; uint8_t v___x_75_; 
v_stxStack_73_ = lean_ctor_get(v_s_64_, 0);
lean_inc_ref(v_stxStack_73_);
v_pos_74_ = lean_ctor_get(v_s_64_, 2);
lean_inc(v_pos_74_);
v___x_75_ = l_Lean_Parser_InputContext_atEnd(v_ictx_54_, v_pos_74_);
lean_dec(v_pos_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec_ref(v_stxStack_73_);
lean_dec_ref(v_toApplicative_58_);
v___x_76_ = ((lean_object*)(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0));
v___x_77_ = l_Lean_Parser_ParserState_mkError(v_s_64_, v___x_76_);
v___x_78_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_54_, v___x_77_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = l_Lean_MessageData_ofFormat(v___x_79_);
v___x_81_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_toPure_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_s_64_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_ictx_54_);
v_toPure_82_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_82_);
lean_dec_ref(v_toApplicative_58_);
v___x_83_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_73_);
lean_dec_ref(v_stxStack_73_);
v___x_84_ = lean_apply_2(v_toPure_82_, lean_box(0), v___x_83_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object* v_source_85_, lean_object* v___y_86_, lean_object* v_start_87_, lean_object* v_env_88_, lean_object* v_p_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_toApplicative_92_, lean_object* v_toBind_93_, lean_object* v_inst_94_, lean_object* v_____do__lift_95_){
_start:
{
uint8_t v___x_96_; lean_object* v_ictx_97_; lean_object* v___x_98_; lean_object* v_s_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v___x_96_ = 1;
lean_inc_ref(v_source_85_);
v_ictx_97_ = l_Lean_Parser_mkInputContext___redArg(v_source_85_, v_____do__lift_95_, v___x_96_, v___y_86_);
v___x_98_ = l_Lean_Parser_mkParserState(v_source_85_);
lean_dec_ref(v_source_85_);
v_s_99_ = l_Lean_Parser_ParserState_setPos(v___x_98_, v_start_87_);
v___f_100_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__0), 8, 7);
lean_closure_set(v___f_100_, 0, v_env_88_);
lean_closure_set(v___f_100_, 1, v_p_89_);
lean_closure_set(v___f_100_, 2, v_ictx_97_);
lean_closure_set(v___f_100_, 3, v_s_99_);
lean_closure_set(v___f_100_, 4, v_inst_90_);
lean_closure_set(v___f_100_, 5, v_inst_91_);
lean_closure_set(v___f_100_, 6, v_toApplicative_92_);
v___x_101_ = lean_apply_4(v_toBind_93_, lean_box(0), lean_box(0), v_inst_94_, v___f_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object* v_text_102_, lean_object* v_inst_103_, lean_object* v_env_104_, lean_object* v_p_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_toApplicative_108_, lean_object* v_toBind_109_, lean_object* v_inst_110_, lean_object* v_____x_111_){
_start:
{
lean_object* v_start_112_; lean_object* v_stop_113_; lean_object* v_source_114_; lean_object* v___y_116_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_start_112_ = lean_ctor_get(v_____x_111_, 0);
lean_inc(v_start_112_);
v_stop_113_ = lean_ctor_get(v_____x_111_, 1);
lean_inc(v_stop_113_);
lean_dec_ref(v_____x_111_);
v_source_114_ = lean_ctor_get(v_text_102_, 0);
lean_inc_ref(v_source_114_);
lean_dec_ref(v_text_102_);
v___x_120_ = lean_string_utf8_byte_size(v_source_114_);
v___x_121_ = lean_nat_dec_le(v_stop_113_, v___x_120_);
if (v___x_121_ == 0)
{
lean_dec(v_stop_113_);
v___y_116_ = v___x_120_;
goto v___jp_115_;
}
else
{
v___y_116_ = v_stop_113_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v_getFileName_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_getFileName_117_ = lean_ctor_get(v_inst_103_, 2);
lean_inc(v_getFileName_117_);
lean_dec_ref(v_inst_103_);
lean_inc(v_toBind_109_);
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__1), 11, 10);
lean_closure_set(v___f_118_, 0, v_source_114_);
lean_closure_set(v___f_118_, 1, v___y_116_);
lean_closure_set(v___f_118_, 2, v_start_112_);
lean_closure_set(v___f_118_, 3, v_env_104_);
lean_closure_set(v___f_118_, 4, v_p_105_);
lean_closure_set(v___f_118_, 5, v_inst_106_);
lean_closure_set(v___f_118_, 6, v_inst_107_);
lean_closure_set(v___f_118_, 7, v_toApplicative_108_);
lean_closure_set(v___f_118_, 8, v_toBind_109_);
lean_closure_set(v___f_118_, 9, v_inst_110_);
v___x_119_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v_getFileName_117_, v___f_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object* v_text_122_, lean_object* v_inst_123_, lean_object* v_p_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_toApplicative_127_, lean_object* v_toBind_128_, lean_object* v_inst_129_, lean_object* v_s_130_, lean_object* v_env_131_){
_start:
{
lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_inc(v_toBind_128_);
lean_inc_ref(v_inst_125_);
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__2), 10, 9);
lean_closure_set(v___f_132_, 0, v_text_122_);
lean_closure_set(v___f_132_, 1, v_inst_123_);
lean_closure_set(v___f_132_, 2, v_env_131_);
lean_closure_set(v___f_132_, 3, v_p_124_);
lean_closure_set(v___f_132_, 4, v_inst_125_);
lean_closure_set(v___f_132_, 5, v_inst_126_);
lean_closure_set(v___f_132_, 6, v_toApplicative_127_);
lean_closure_set(v___f_132_, 7, v_toBind_128_);
lean_closure_set(v___f_132_, 8, v_inst_129_);
v___x_133_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_125_, v_s_130_);
v___x_134_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_133_, v___f_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object* v_text_135_, lean_object* v_inst_136_, lean_object* v_p_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_toApplicative_140_, lean_object* v_toBind_141_, lean_object* v_inst_142_, lean_object* v_s_143_, lean_object* v_env_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Doc_parseStrLit___redArg___lam__3(v_text_135_, v_inst_136_, v_p_137_, v_inst_138_, v_inst_139_, v_toApplicative_140_, v_toBind_141_, v_inst_142_, v_s_143_, v_env_144_);
lean_dec(v_s_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_p_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_toApplicative_151_, lean_object* v_toBind_152_, lean_object* v_inst_153_, lean_object* v_s_154_, lean_object* v_text_155_){
_start:
{
lean_object* v_getEnv_156_; lean_object* v___f_157_; lean_object* v___x_158_; 
v_getEnv_156_ = lean_ctor_get(v_inst_146_, 0);
lean_inc(v_getEnv_156_);
lean_dec_ref(v_inst_146_);
lean_inc(v_toBind_152_);
v___f_157_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_157_, 0, v_text_155_);
lean_closure_set(v___f_157_, 1, v_inst_147_);
lean_closure_set(v___f_157_, 2, v_p_148_);
lean_closure_set(v___f_157_, 3, v_inst_149_);
lean_closure_set(v___f_157_, 4, v_inst_150_);
lean_closure_set(v___f_157_, 5, v_toApplicative_151_);
lean_closure_set(v___f_157_, 6, v_toBind_152_);
lean_closure_set(v___f_157_, 7, v_inst_153_);
lean_closure_set(v___f_157_, 8, v_s_154_);
v___x_158_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v_getEnv_156_, v___f_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_p_165_, lean_object* v_s_166_){
_start:
{
lean_object* v_toApplicative_167_; lean_object* v_toBind_168_; lean_object* v___f_169_; lean_object* v___x_170_; 
v_toApplicative_167_ = lean_ctor_get(v_inst_159_, 0);
lean_inc_ref(v_toApplicative_167_);
v_toBind_168_ = lean_ctor_get(v_inst_159_, 1);
lean_inc(v_toBind_168_);
lean_inc(v_toBind_168_);
v___f_169_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__4), 10, 9);
lean_closure_set(v___f_169_, 0, v_inst_161_);
lean_closure_set(v___f_169_, 1, v_inst_163_);
lean_closure_set(v___f_169_, 2, v_p_165_);
lean_closure_set(v___f_169_, 3, v_inst_159_);
lean_closure_set(v___f_169_, 4, v_inst_162_);
lean_closure_set(v___f_169_, 5, v_toApplicative_167_);
lean_closure_set(v___f_169_, 6, v_toBind_168_);
lean_closure_set(v___f_169_, 7, v_inst_164_);
lean_closure_set(v___f_169_, 8, v_s_166_);
v___x_170_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v_inst_160_, v___f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_p_178_, lean_object* v_s_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Doc_parseStrLit___redArg(v_inst_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_, v_inst_177_, v_p_178_, v_s_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_200_; 
v_fst_183_ = lean_ctor_get(v_b_182_, 0);
v_snd_184_ = lean_ctor_get(v_b_182_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_b_182_);
if (v_isSharedCheck_200_ == 0)
{
v___x_186_ = v_b_182_;
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snd_184_);
lean_inc(v_fst_183_);
lean_dec(v_b_182_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_nat_dec_lt(v___x_188_, v_fst_183_);
if (v___x_189_ == 0)
{
lean_object* v___x_191_; 
if (v_isShared_187_ == 0)
{
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_fst_183_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_snd_184_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v_p_193_; lean_object* v___x_194_; lean_object* v_n_195_; lean_object* v___x_197_; 
v_p_193_ = lean_string_utf8_prev(v_str_181_, v_fst_183_);
lean_dec(v_fst_183_);
v___x_194_ = lean_unsigned_to_nat(1u);
v_n_195_ = lean_nat_add(v_snd_184_, v___x_194_);
lean_dec(v_snd_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_n_195_);
lean_ctor_set(v___x_186_, 0, v_p_193_);
v___x_197_ = v___x_186_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_p_193_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_n_195_);
v___x_197_ = v_reuseFailAlloc_199_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v_b_182_ = v___x_197_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_201_, lean_object* v_b_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_201_, v_b_202_);
lean_dec_ref(v_str_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_204_, lean_object* v_p_205_){
_start:
{
lean_object* v_n_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_snd_209_; 
v_n_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_p_205_);
lean_ctor_set(v___x_207_, 1, v_n_206_);
v___x_208_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_204_, v___x_207_);
v_snd_209_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_snd_209_);
lean_dec_ref(v___x_208_);
return v_snd_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_210_, lean_object* v_p_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_210_, v_p_211_);
lean_dec_ref(v_str_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_213_, lean_object* v_p_214_, lean_object* v_j_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_zero_217_; uint8_t v_isZero_218_; 
v_zero_217_ = lean_unsigned_to_nat(0u);
v_isZero_218_ = lean_nat_dec_eq(v_j_215_, v_zero_217_);
if (v_isZero_218_ == 1)
{
lean_dec(v_j_215_);
return v_a_216_;
}
else
{
lean_object* v_one_219_; lean_object* v_n_220_; lean_object* v___x_221_; 
lean_dec(v_a_216_);
v_one_219_ = lean_unsigned_to_nat(1u);
v_n_220_ = lean_nat_sub(v_j_215_, v_one_219_);
lean_dec(v_j_215_);
v___x_221_ = lean_string_utf8_next(v_str_213_, v_p_214_);
v_j_215_ = v_n_220_;
v_a_216_ = v___x_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_223_, lean_object* v_p_224_, lean_object* v_j_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_223_, v_p_224_, v_j_225_, v_a_226_);
lean_dec(v_p_224_);
lean_dec_ref(v_str_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_228_, lean_object* v_n_229_, lean_object* v_p_230_){
_start:
{
lean_object* v___x_231_; 
lean_inc(v_p_230_);
v___x_231_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_228_, v_p_230_, v_n_229_, v_p_230_);
lean_dec(v_p_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_232_, lean_object* v_n_233_, lean_object* v_p_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_232_, v_n_233_, v_p_234_);
lean_dec_ref(v_str_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_236_, lean_object* v_p_237_, lean_object* v_n_238_, lean_object* v_j_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_236_, v_p_237_, v_j_239_, v_a_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_243_, lean_object* v_p_244_, lean_object* v_n_245_, lean_object* v_j_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_243_, v_p_244_, v_n_245_, v_j_246_, v_a_247_, v_a_248_);
lean_dec(v_n_245_);
lean_dec(v_p_244_);
lean_dec_ref(v_str_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_250_, lean_object* v_posOfStr_251_, lean_object* v_str_252_, lean_object* v_posInStr_253_){
_start:
{
lean_object* v_source_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_source_254_ = lean_ctor_get(v_text_250_, 0);
v___x_255_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_252_, v_posInStr_253_);
lean_inc(v_posOfStr_251_);
v___x_256_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_254_, v_posOfStr_251_, v___x_255_, v_posOfStr_251_);
lean_dec(v_posOfStr_251_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_257_, lean_object* v_posOfStr_258_, lean_object* v_str_259_, lean_object* v_posInStr_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_257_, v_posOfStr_258_, v_str_259_, v_posInStr_260_);
lean_dec_ref(v_str_259_);
lean_dec_ref(v_text_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_262_, lean_object* v_posOfStr_263_, lean_object* v_str_264_, lean_object* v_a_265_){
_start:
{
switch(lean_obj_tag(v_a_265_))
{
case 0:
{
lean_object* v_pos_266_; lean_object* v_endPos_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; 
v_pos_266_ = lean_ctor_get(v_a_265_, 1);
lean_inc(v_pos_266_);
v_endPos_267_ = lean_ctor_get(v_a_265_, 3);
lean_inc(v_endPos_267_);
lean_dec_ref(v_a_265_);
lean_inc(v_posOfStr_263_);
v___x_268_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_262_, v_posOfStr_263_, v_str_264_, v_pos_266_);
v___x_269_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_262_, v_posOfStr_263_, v_str_264_, v_endPos_267_);
v___x_270_ = 1;
v___x_271_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_271_, 0, v___x_268_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*2, v___x_270_);
return v___x_271_;
}
case 1:
{
lean_object* v_pos_272_; lean_object* v_endPos_273_; uint8_t v_canonical_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_283_; 
v_pos_272_ = lean_ctor_get(v_a_265_, 0);
v_endPos_273_ = lean_ctor_get(v_a_265_, 1);
v_canonical_274_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*2);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_283_ == 0)
{
v___x_276_ = v_a_265_;
v_isShared_277_ = v_isSharedCheck_283_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_endPos_273_);
lean_inc(v_pos_272_);
lean_dec(v_a_265_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_283_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_inc(v_posOfStr_263_);
v___x_278_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_262_, v_posOfStr_263_, v_str_264_, v_pos_272_);
v___x_279_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_262_, v_posOfStr_263_, v_str_264_, v_endPos_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_279_);
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*2, v_canonical_274_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
default: 
{
lean_dec(v_posOfStr_263_);
return v_a_265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_284_, lean_object* v_posOfStr_285_, lean_object* v_str_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_284_, v_posOfStr_285_, v_str_286_, v_a_287_);
lean_dec_ref(v_str_286_);
lean_dec_ref(v_text_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_289_, lean_object* v_posOfStr_290_, lean_object* v_str_291_, lean_object* v_a_292_){
_start:
{
switch(lean_obj_tag(v_a_292_))
{
case 0:
{
lean_dec(v_posOfStr_290_);
return v_a_292_;
}
case 1:
{
lean_object* v_info_293_; lean_object* v_kind_294_; lean_object* v_args_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_306_; 
v_info_293_ = lean_ctor_get(v_a_292_, 0);
v_kind_294_ = lean_ctor_get(v_a_292_, 1);
v_args_295_ = lean_ctor_get(v_a_292_, 2);
v_isSharedCheck_306_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_306_ == 0)
{
v___x_297_ = v_a_292_;
v_isShared_298_ = v_isSharedCheck_306_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_args_295_);
lean_inc(v_kind_294_);
lean_inc(v_info_293_);
lean_dec(v_a_292_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_306_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_posOfStr_290_);
v___x_299_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_289_, v_posOfStr_290_, v_str_291_, v_info_293_);
v_sz_300_ = lean_array_size(v_args_295_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_289_, v_posOfStr_290_, v_str_291_, v_sz_300_, v___x_301_, v_args_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_302_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_304_ = v___x_297_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_kind_294_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
case 2:
{
lean_object* v_info_307_; lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_info_307_ = lean_ctor_get(v_a_292_, 0);
v_val_308_ = lean_ctor_get(v_a_292_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v_a_292_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_inc(v_info_307_);
lean_dec(v_a_292_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_289_, v_posOfStr_290_, v_str_291_, v_info_307_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_val_308_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
default: 
{
lean_object* v_info_317_; lean_object* v_rawVal_318_; lean_object* v_val_319_; lean_object* v_preresolved_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_info_317_ = lean_ctor_get(v_a_292_, 0);
v_rawVal_318_ = lean_ctor_get(v_a_292_, 1);
v_val_319_ = lean_ctor_get(v_a_292_, 2);
v_preresolved_320_ = lean_ctor_get(v_a_292_, 3);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v_a_292_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_preresolved_320_);
lean_inc(v_val_319_);
lean_inc(v_rawVal_318_);
lean_inc(v_info_317_);
lean_dec(v_a_292_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_289_, v_posOfStr_290_, v_str_291_, v_info_317_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_rawVal_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_val_319_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_preresolved_320_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_329_, lean_object* v_posOfStr_330_, lean_object* v_str_331_, size_t v_sz_332_, size_t v_i_333_, lean_object* v_bs_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_lt(v_i_333_, v_sz_332_);
if (v___x_335_ == 0)
{
lean_dec(v_posOfStr_330_);
return v_bs_334_;
}
else
{
lean_object* v_v_336_; lean_object* v___x_337_; lean_object* v_bs_x27_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v_v_336_ = lean_array_uget(v_bs_334_, v_i_333_);
v___x_337_ = lean_unsigned_to_nat(0u);
v_bs_x27_338_ = lean_array_uset(v_bs_334_, v_i_333_, v___x_337_);
lean_inc(v_posOfStr_330_);
v___x_339_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_329_, v_posOfStr_330_, v_str_331_, v_v_336_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_333_, v___x_340_);
v___x_342_ = lean_array_uset(v_bs_x27_338_, v_i_333_, v___x_339_);
v_i_333_ = v___x_341_;
v_bs_334_ = v___x_342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_344_, lean_object* v_posOfStr_345_, lean_object* v_str_346_, lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_bs_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_344_, v_posOfStr_345_, v_str_346_, v_sz_boxed_350_, v_i_boxed_351_, v_bs_349_);
lean_dec_ref(v_str_346_);
lean_dec_ref(v_text_344_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_353_, lean_object* v_posOfStr_354_, lean_object* v_str_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_353_, v_posOfStr_354_, v_str_355_, v_a_356_);
lean_dec_ref(v_str_355_);
lean_dec_ref(v_text_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_, lean_object* v_h__3_361_, lean_object* v_h__4_362_){
_start:
{
switch(lean_obj_tag(v_x_358_))
{
case 0:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_h__3_361_);
lean_dec(v_h__2_360_);
lean_dec(v_h__1_359_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__4_362_, v___x_363_);
return v___x_364_;
}
case 1:
{
lean_object* v_info_365_; lean_object* v_kind_366_; lean_object* v_args_367_; lean_object* v___x_368_; 
lean_dec(v_h__4_362_);
lean_dec(v_h__3_361_);
lean_dec(v_h__2_360_);
v_info_365_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_info_365_);
v_kind_366_ = lean_ctor_get(v_x_358_, 1);
lean_inc(v_kind_366_);
v_args_367_ = lean_ctor_get(v_x_358_, 2);
lean_inc_ref(v_args_367_);
lean_dec_ref(v_x_358_);
v___x_368_ = lean_apply_3(v_h__1_359_, v_info_365_, v_kind_366_, v_args_367_);
return v___x_368_;
}
case 2:
{
lean_object* v_info_369_; lean_object* v_val_370_; lean_object* v___x_371_; 
lean_dec(v_h__4_362_);
lean_dec(v_h__2_360_);
lean_dec(v_h__1_359_);
v_info_369_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_info_369_);
v_val_370_ = lean_ctor_get(v_x_358_, 1);
lean_inc_ref(v_val_370_);
lean_dec_ref(v_x_358_);
v___x_371_ = lean_apply_2(v_h__3_361_, v_info_369_, v_val_370_);
return v___x_371_;
}
default: 
{
lean_object* v_info_372_; lean_object* v_rawVal_373_; lean_object* v_val_374_; lean_object* v_preresolved_375_; lean_object* v___x_376_; 
lean_dec(v_h__4_362_);
lean_dec(v_h__3_361_);
lean_dec(v_h__1_359_);
v_info_372_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_info_372_);
v_rawVal_373_ = lean_ctor_get(v_x_358_, 1);
lean_inc_ref(v_rawVal_373_);
v_val_374_ = lean_ctor_get(v_x_358_, 2);
lean_inc(v_val_374_);
v_preresolved_375_ = lean_ctor_get(v_x_358_, 3);
lean_inc(v_preresolved_375_);
lean_dec_ref(v_x_358_);
v___x_376_ = lean_apply_4(v_h__2_360_, v_info_372_, v_rawVal_373_, v_val_374_, v_preresolved_375_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_377_, lean_object* v_x_378_, lean_object* v_h__1_379_, lean_object* v_h__2_380_, lean_object* v_h__3_381_, lean_object* v_h__4_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(v_x_378_, v_h__1_379_, v_h__2_380_, v_h__3_381_, v_h__4_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_384_, lean_object* v_h__1_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_apply_2(v_h__1_385_, v_x_384_, lean_box(0));
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_387_, lean_object* v_P_388_, lean_object* v_motive_389_, lean_object* v_x_390_, lean_object* v_h__1_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_apply_2(v_h__1_391_, v_x_390_, lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_text_393_, lean_object* v_pos_394_, lean_object* v_str_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_fst_397_; lean_object* v_snd_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_fst_397_ = lean_ctor_get(v_x_396_, 0);
v_snd_398_ = lean_ctor_get(v_x_396_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_x_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snd_398_);
lean_inc(v_fst_397_);
lean_dec(v_x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_393_, v_pos_394_, v_str_395_, v_fst_397_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_snd_398_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(lean_object* v_text_407_, lean_object* v_pos_408_, lean_object* v_str_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(v_text_407_, v_pos_408_, v_str_409_, v_x_410_);
lean_dec_ref(v_str_409_);
lean_dec_ref(v_text_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_env_431_, lean_object* v_p_432_, lean_object* v_ictx_433_, lean_object* v_s_434_, lean_object* v_text_435_, lean_object* v_pos_436_, lean_object* v_str_437_, lean_object* v___f_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_toApplicative_441_, lean_object* v_____do__lift_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_s_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_box(0);
lean_inc_ref(v_env_431_);
v___x_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_445_, 0, v_env_431_);
lean_ctor_set(v___x_445_, 1, v_____do__lift_442_);
lean_ctor_set(v___x_445_, 2, v___x_443_);
lean_ctor_set(v___x_445_, 3, v___x_444_);
v___x_446_ = l_Lean_Parser_getTokenTable(v_env_431_);
lean_inc_ref(v_ictx_433_);
v_s_447_ = l_Lean_Parser_ParserFn_run(v_p_432_, v_ictx_433_, v___x_445_, v___x_446_, v_s_434_);
lean_inc_ref(v_s_447_);
v___x_448_ = l_Lean_Parser_ParserState_allErrors(v_s_447_);
v___x_449_ = lean_array_get_size(v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v_stxStack_452_; lean_object* v_lhsPrec_453_; lean_object* v_pos_454_; lean_object* v_cache_455_; lean_object* v_errorMsg_456_; lean_object* v_recoveredErrors_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v_toApplicative_441_);
v_stxStack_452_ = lean_ctor_get(v_s_447_, 0);
v_lhsPrec_453_ = lean_ctor_get(v_s_447_, 1);
v_pos_454_ = lean_ctor_get(v_s_447_, 2);
v_cache_455_ = lean_ctor_get(v_s_447_, 3);
v_errorMsg_456_ = lean_ctor_get(v_s_447_, 4);
v_recoveredErrors_457_ = lean_ctor_get(v_s_447_, 5);
v_isSharedCheck_494_ = !lean_is_exclusive(v_s_447_);
if (v_isSharedCheck_494_ == 0)
{
v___x_459_ = v_s_447_;
v_isShared_460_ = v_isSharedCheck_494_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_recoveredErrors_457_);
lean_inc(v_errorMsg_456_);
lean_inc(v_cache_455_);
lean_inc(v_pos_454_);
lean_inc(v_lhsPrec_453_);
lean_inc(v_stxStack_452_);
lean_dec(v_s_447_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_494_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___y_463_; 
lean_inc(v_pos_436_);
v___x_461_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_435_, v_pos_436_, v_str_437_, v_pos_454_);
if (lean_obj_tag(v_errorMsg_456_) == 0)
{
lean_dec(v_pos_436_);
v___y_463_ = v_errorMsg_456_;
goto v___jp_462_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_493_; 
v_val_475_ = lean_ctor_get(v_errorMsg_456_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_errorMsg_456_);
if (v_isSharedCheck_493_ == 0)
{
v___x_477_ = v_errorMsg_456_;
v_isShared_478_ = v_isSharedCheck_493_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_val_475_);
lean_dec(v_errorMsg_456_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_493_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_unexpectedTk_479_; lean_object* v_unexpected_480_; lean_object* v_expected_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_492_; 
v_unexpectedTk_479_ = lean_ctor_get(v_val_475_, 0);
v_unexpected_480_ = lean_ctor_get(v_val_475_, 1);
v_expected_481_ = lean_ctor_get(v_val_475_, 2);
v_isSharedCheck_492_ = !lean_is_exclusive(v_val_475_);
if (v_isSharedCheck_492_ == 0)
{
v___x_483_ = v_val_475_;
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_expected_481_);
lean_inc(v_unexpected_480_);
lean_inc(v_unexpectedTk_479_);
lean_dec(v_val_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_435_, v_pos_436_, v_str_437_, v_unexpectedTk_479_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_unexpected_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_expected_481_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_487_);
v___x_489_ = v___x_477_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v___y_463_ = v___x_489_;
goto v___jp_462_;
}
}
}
}
}
v___jp_462_:
{
lean_object* v___x_464_; size_t v_sz_465_; size_t v___x_466_; lean_object* v___x_467_; lean_object* v_s_469_; 
v___x_464_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9));
v_sz_465_ = lean_array_size(v_recoveredErrors_457_);
v___x_466_ = ((size_t)0ULL);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_464_, v___f_438_, v_sz_465_, v___x_466_, v_recoveredErrors_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 5, v___x_467_);
lean_ctor_set(v___x_459_, 4, v___y_463_);
lean_ctor_set(v___x_459_, 2, v___x_461_);
v_s_469_ = v___x_459_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_stxStack_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_lhsPrec_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_cache_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___y_463_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v___x_467_);
v_s_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_433_, v_s_469_);
v___x_471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
v___x_472_ = l_Lean_MessageData_ofFormat(v___x_471_);
v___x_473_ = l_Lean_throwError___redArg(v_inst_439_, v_inst_440_, v___x_472_);
return v___x_473_;
}
}
}
}
else
{
lean_object* v_stxStack_495_; lean_object* v_pos_496_; uint8_t v___x_497_; 
lean_dec_ref(v___f_438_);
v_stxStack_495_ = lean_ctor_get(v_s_447_, 0);
lean_inc_ref(v_stxStack_495_);
v_pos_496_ = lean_ctor_get(v_s_447_, 2);
lean_inc(v_pos_496_);
v___x_497_ = l_Lean_Parser_InputContext_atEnd(v_ictx_433_, v_pos_496_);
lean_dec(v_pos_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v_stxStack_495_);
lean_dec_ref(v_toApplicative_441_);
lean_dec(v_pos_436_);
v___x_498_ = ((lean_object*)(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0));
v___x_499_ = l_Lean_Parser_ParserState_mkError(v_s_447_, v___x_498_);
v___x_500_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_433_, v___x_499_);
v___x_501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
v___x_502_ = l_Lean_MessageData_ofFormat(v___x_501_);
v___x_503_ = l_Lean_throwError___redArg(v_inst_439_, v_inst_440_, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_toPure_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_s_447_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
lean_dec_ref(v_ictx_433_);
v_toPure_504_ = lean_ctor_get(v_toApplicative_441_, 1);
lean_inc(v_toPure_504_);
lean_dec_ref(v_toApplicative_441_);
v___x_505_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_495_);
lean_dec_ref(v_stxStack_495_);
v___x_506_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_435_, v_pos_436_, v_str_437_, v___x_505_);
v___x_507_ = lean_apply_2(v_toPure_504_, lean_box(0), v___x_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_env_508_, lean_object* v_p_509_, lean_object* v_ictx_510_, lean_object* v_s_511_, lean_object* v_text_512_, lean_object* v_pos_513_, lean_object* v_str_514_, lean_object* v___f_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_toApplicative_518_, lean_object* v_____do__lift_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_env_508_, v_p_509_, v_ictx_510_, v_s_511_, v_text_512_, v_pos_513_, v_str_514_, v___f_515_, v_inst_516_, v_inst_517_, v_toApplicative_518_, v_____do__lift_519_);
lean_dec_ref(v_str_514_);
lean_dec_ref(v_text_512_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_str_521_, lean_object* v_env_522_, lean_object* v_p_523_, lean_object* v_text_524_, lean_object* v_pos_525_, lean_object* v___f_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_toApplicative_529_, lean_object* v_toBind_530_, lean_object* v_inst_531_, lean_object* v_____do__lift_532_){
_start:
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v_ictx_535_; lean_object* v_s_536_; lean_object* v___f_537_; lean_object* v___x_538_; 
v___x_533_ = 1;
v___x_534_ = lean_string_utf8_byte_size(v_str_521_);
lean_inc_ref(v_str_521_);
v_ictx_535_ = l_Lean_Parser_mkInputContext___redArg(v_str_521_, v_____do__lift_532_, v___x_533_, v___x_534_);
v_s_536_ = l_Lean_Parser_mkParserState(v_str_521_);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_537_, 0, v_env_522_);
lean_closure_set(v___f_537_, 1, v_p_523_);
lean_closure_set(v___f_537_, 2, v_ictx_535_);
lean_closure_set(v___f_537_, 3, v_s_536_);
lean_closure_set(v___f_537_, 4, v_text_524_);
lean_closure_set(v___f_537_, 5, v_pos_525_);
lean_closure_set(v___f_537_, 6, v_str_521_);
lean_closure_set(v___f_537_, 7, v___f_526_);
lean_closure_set(v___f_537_, 8, v_inst_527_);
lean_closure_set(v___f_537_, 9, v_inst_528_);
lean_closure_set(v___f_537_, 10, v_toApplicative_529_);
v___x_538_ = lean_apply_4(v_toBind_530_, lean_box(0), lean_box(0), v_inst_531_, v___f_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_539_, lean_object* v_strLit_540_, lean_object* v_text_541_, lean_object* v_env_542_, lean_object* v_p_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_toApplicative_546_, lean_object* v_toBind_547_, lean_object* v_inst_548_, lean_object* v_pos_549_){
_start:
{
lean_object* v_getFileName_550_; lean_object* v_str_551_; lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___x_554_; 
v_getFileName_550_ = lean_ctor_get(v_inst_539_, 2);
lean_inc(v_getFileName_550_);
lean_dec_ref(v_inst_539_);
v_str_551_ = l_Lean_TSyntax_getString(v_strLit_540_);
lean_inc_ref(v_str_551_);
lean_inc(v_pos_549_);
lean_inc_ref(v_text_541_);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_552_, 0, v_text_541_);
lean_closure_set(v___f_552_, 1, v_pos_549_);
lean_closure_set(v___f_552_, 2, v_str_551_);
lean_inc(v_toBind_547_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2), 12, 11);
lean_closure_set(v___f_553_, 0, v_str_551_);
lean_closure_set(v___f_553_, 1, v_env_542_);
lean_closure_set(v___f_553_, 2, v_p_543_);
lean_closure_set(v___f_553_, 3, v_text_541_);
lean_closure_set(v___f_553_, 4, v_pos_549_);
lean_closure_set(v___f_553_, 5, v___f_552_);
lean_closure_set(v___f_553_, 6, v_inst_544_);
lean_closure_set(v___f_553_, 7, v_inst_545_);
lean_closure_set(v___f_553_, 8, v_toApplicative_546_);
lean_closure_set(v___f_553_, 9, v_toBind_547_);
lean_closure_set(v___f_553_, 10, v_inst_548_);
v___x_554_ = lean_apply_4(v_toBind_547_, lean_box(0), lean_box(0), v_getFileName_550_, v___f_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_555_, lean_object* v_strLit_556_, lean_object* v_text_557_, lean_object* v_env_558_, lean_object* v_p_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_toApplicative_562_, lean_object* v_toBind_563_, lean_object* v_inst_564_, lean_object* v_pos_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_555_, v_strLit_556_, v_text_557_, v_env_558_, v_p_559_, v_inst_560_, v_inst_561_, v_toApplicative_562_, v_toBind_563_, v_inst_564_, v_pos_565_);
lean_dec(v_strLit_556_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v___f_567_, lean_object* v_pos_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_apply_1(v___f_567_, v_pos_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v_text_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_strLit_576_, lean_object* v_toBind_577_, lean_object* v___f_578_, lean_object* v_toApplicative_579_, lean_object* v___f_580_, lean_object* v_____r_581_, lean_object* v_pos_582_){
_start:
{
lean_object* v_source_583_; uint32_t v___x_584_; uint32_t v___x_585_; uint8_t v___x_586_; 
v_source_583_ = lean_ctor_get(v_text_573_, 0);
v___x_584_ = lean_string_utf8_get(v_source_583_, v_pos_582_);
v___x_585_ = 34;
v___x_586_ = lean_uint32_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v___f_580_);
lean_dec_ref(v_toApplicative_579_);
v___x_587_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1);
v___x_588_ = l_Lean_throwErrorAt___redArg(v_inst_574_, v_inst_575_, v_strLit_576_, v___x_587_);
v___x_589_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v___x_588_, v___f_578_);
return v___x_589_;
}
else
{
lean_object* v_toPure_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v___f_578_);
lean_dec(v_strLit_576_);
lean_dec_ref(v_inst_575_);
lean_dec_ref(v_inst_574_);
v_toPure_590_ = lean_ctor_get(v_toApplicative_579_, 1);
lean_inc(v_toPure_590_);
lean_dec_ref(v_toApplicative_579_);
v___x_591_ = lean_string_utf8_next(v_source_583_, v_pos_582_);
v___x_592_ = lean_apply_2(v_toPure_590_, lean_box(0), v___x_591_);
v___x_593_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v___x_592_, v___f_580_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object* v_text_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_strLit_597_, lean_object* v_toBind_598_, lean_object* v___f_599_, lean_object* v_toApplicative_600_, lean_object* v___f_601_, lean_object* v_____r_602_, lean_object* v_pos_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(v_text_594_, v_inst_595_, v_inst_596_, v_strLit_597_, v_toBind_598_, v___f_599_, v_toApplicative_600_, v___f_601_, v_____r_602_, v_pos_603_);
lean_dec(v_pos_603_);
lean_dec_ref(v_text_594_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_605_, lean_object* v_____s_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_apply_2(v___f_605_, v___x_607_, v_____s_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_source_609_, lean_object* v_toApplicative_610_, lean_object* v_x_611_, lean_object* v_____s_612_){
_start:
{
uint32_t v___x_613_; uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_string_utf8_get(v_source_609_, v_____s_612_);
v___x_614_ = 35;
v___x_615_ = lean_uint32_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v_toPure_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_toPure_616_ = lean_ctor_get(v_toApplicative_610_, 1);
lean_inc(v_toPure_616_);
lean_dec_ref(v_toApplicative_610_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_____s_612_);
v___x_618_ = lean_apply_2(v_toPure_616_, lean_box(0), v___x_617_);
return v___x_618_;
}
else
{
lean_object* v_toPure_619_; lean_object* v_pos_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_toPure_619_ = lean_ctor_get(v_toApplicative_610_, 1);
lean_inc(v_toPure_619_);
lean_dec_ref(v_toApplicative_610_);
v_pos_620_ = lean_string_utf8_next(v_source_609_, v_____s_612_);
lean_dec(v_____s_612_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_pos_620_);
v___x_622_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_source_623_, lean_object* v_toApplicative_624_, lean_object* v_x_625_, lean_object* v_____s_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_source_623_, v_toApplicative_624_, v_x_625_, v_____s_626_);
lean_dec_ref(v_source_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_text_628_, lean_object* v___f_629_, lean_object* v_toApplicative_630_, lean_object* v_inst_631_, lean_object* v_toBind_632_, lean_object* v___f_633_, lean_object* v_____x_634_){
_start:
{
lean_object* v_start_635_; lean_object* v_source_636_; uint32_t v___x_637_; uint32_t v___x_638_; uint8_t v___x_639_; 
v_start_635_ = lean_ctor_get(v_____x_634_, 0);
lean_inc(v_start_635_);
lean_dec_ref(v_____x_634_);
v_source_636_ = lean_ctor_get(v_text_628_, 0);
lean_inc_ref(v_source_636_);
lean_dec_ref(v_text_628_);
v___x_637_ = lean_string_utf8_get(v_source_636_, v_start_635_);
v___x_638_ = 114;
v___x_639_ = lean_uint32_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_source_636_);
lean_dec(v___f_633_);
lean_dec(v_toBind_632_);
lean_dec_ref(v_inst_631_);
lean_dec_ref(v_toApplicative_630_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_apply_2(v___f_629_, v___x_640_, v_start_635_);
return v___x_641_;
}
else
{
lean_object* v___f_642_; lean_object* v_pos_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v___f_629_);
lean_inc_ref(v_source_636_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_642_, 0, v_source_636_);
lean_closure_set(v___f_642_, 1, v_toApplicative_630_);
v_pos_643_ = lean_string_utf8_next(v_source_636_, v_start_635_);
lean_dec(v_start_635_);
lean_dec_ref(v_source_636_);
v___x_644_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_631_, v___f_642_, v_pos_643_);
v___x_645_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_644_, v___f_633_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_inst_646_, lean_object* v_strLit_647_, lean_object* v_text_648_, lean_object* v_p_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_toApplicative_652_, lean_object* v_toBind_653_, lean_object* v_inst_654_, lean_object* v_env_655_){
_start:
{
lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_inc(v_toBind_653_);
lean_inc_ref(v_toApplicative_652_);
lean_inc_ref(v_inst_651_);
lean_inc_ref(v_inst_650_);
lean_inc_ref(v_text_648_);
lean_inc(v_strLit_647_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_656_, 0, v_inst_646_);
lean_closure_set(v___f_656_, 1, v_strLit_647_);
lean_closure_set(v___f_656_, 2, v_text_648_);
lean_closure_set(v___f_656_, 3, v_env_655_);
lean_closure_set(v___f_656_, 4, v_p_649_);
lean_closure_set(v___f_656_, 5, v_inst_650_);
lean_closure_set(v___f_656_, 6, v_inst_651_);
lean_closure_set(v___f_656_, 7, v_toApplicative_652_);
lean_closure_set(v___f_656_, 8, v_toBind_653_);
lean_closure_set(v___f_656_, 9, v_inst_654_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4), 2, 1);
lean_closure_set(v___f_657_, 0, v___f_656_);
lean_inc_ref(v_toApplicative_652_);
lean_inc_ref(v___f_657_);
lean_inc(v_toBind_653_);
lean_inc(v_strLit_647_);
lean_inc_ref(v_inst_650_);
lean_inc_ref(v_text_648_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_658_, 0, v_text_648_);
lean_closure_set(v___f_658_, 1, v_inst_650_);
lean_closure_set(v___f_658_, 2, v_inst_651_);
lean_closure_set(v___f_658_, 3, v_strLit_647_);
lean_closure_set(v___f_658_, 4, v_toBind_653_);
lean_closure_set(v___f_658_, 5, v___f_657_);
lean_closure_set(v___f_658_, 6, v_toApplicative_652_);
lean_closure_set(v___f_658_, 7, v___f_657_);
lean_inc_ref(v___f_658_);
v___f_659_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_659_, 0, v___f_658_);
lean_inc(v_toBind_653_);
lean_inc_ref(v_inst_650_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_660_, 0, v_text_648_);
lean_closure_set(v___f_660_, 1, v___f_658_);
lean_closure_set(v___f_660_, 2, v_toApplicative_652_);
lean_closure_set(v___f_660_, 3, v_inst_650_);
lean_closure_set(v___f_660_, 4, v_toBind_653_);
lean_closure_set(v___f_660_, 5, v___f_659_);
v___x_661_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_650_, v_strLit_647_);
lean_dec(v_strLit_647_);
v___x_662_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_661_, v___f_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_strLit_665_, lean_object* v_p_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_toApplicative_669_, lean_object* v_toBind_670_, lean_object* v_inst_671_, lean_object* v_text_672_){
_start:
{
lean_object* v_getEnv_673_; lean_object* v___f_674_; lean_object* v___x_675_; 
v_getEnv_673_ = lean_ctor_get(v_inst_663_, 0);
lean_inc(v_getEnv_673_);
lean_dec_ref(v_inst_663_);
lean_inc(v_toBind_670_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 10, 9);
lean_closure_set(v___f_674_, 0, v_inst_664_);
lean_closure_set(v___f_674_, 1, v_strLit_665_);
lean_closure_set(v___f_674_, 2, v_text_672_);
lean_closure_set(v___f_674_, 3, v_p_666_);
lean_closure_set(v___f_674_, 4, v_inst_667_);
lean_closure_set(v___f_674_, 5, v_inst_668_);
lean_closure_set(v___f_674_, 6, v_toApplicative_669_);
lean_closure_set(v___f_674_, 7, v_toBind_670_);
lean_closure_set(v___f_674_, 8, v_inst_671_);
v___x_675_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v_getEnv_673_, v___f_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_p_682_, lean_object* v_strLit_683_){
_start:
{
lean_object* v_toApplicative_684_; lean_object* v_toBind_685_; lean_object* v___f_686_; lean_object* v___x_687_; 
v_toApplicative_684_ = lean_ctor_get(v_inst_676_, 0);
lean_inc_ref(v_toApplicative_684_);
v_toBind_685_ = lean_ctor_get(v_inst_676_, 1);
lean_inc(v_toBind_685_);
lean_inc(v_toBind_685_);
v___f_686_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10), 10, 9);
lean_closure_set(v___f_686_, 0, v_inst_678_);
lean_closure_set(v___f_686_, 1, v_inst_680_);
lean_closure_set(v___f_686_, 2, v_strLit_683_);
lean_closure_set(v___f_686_, 3, v_p_682_);
lean_closure_set(v___f_686_, 4, v_inst_676_);
lean_closure_set(v___f_686_, 5, v_inst_679_);
lean_closure_set(v___f_686_, 6, v_toApplicative_684_);
lean_closure_set(v___f_686_, 7, v_toBind_685_);
lean_closure_set(v___f_686_, 8, v_inst_681_);
v___x_687_ = lean_apply_4(v_toBind_685_, lean_box(0), lean_box(0), v_inst_677_, v___f_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_p_695_, lean_object* v_strLit_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_689_, v_inst_690_, v_inst_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_p_695_, v_strLit_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object* v_s_698_, lean_object* v_toPure_699_, uint8_t v_err_700_){
_start:
{
lean_object* v_stxStack_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_stxStack_701_ = lean_ctor_get(v_s_698_, 0);
v___x_702_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_701_);
v___x_703_ = lean_box(v_err_700_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_apply_2(v_toPure_699_, lean_box(0), v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object* v_s_706_, lean_object* v_toPure_707_, lean_object* v_err_708_){
_start:
{
uint8_t v_err_boxed_709_; lean_object* v_res_710_; 
v_err_boxed_709_ = lean_unbox(v_err_708_);
v_res_710_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_706_, v_toPure_707_, v_err_boxed_709_);
lean_dec_ref(v_s_706_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object* v___f_711_, uint8_t v_err_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(v_err_712_);
v___x_714_ = lean_apply_1(v___f_711_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object* v___f_715_, lean_object* v_err_716_){
_start:
{
uint8_t v_err_boxed_717_; lean_object* v_res_718_; 
v_err_boxed_717_ = lean_unbox(v_err_716_);
v_res_718_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_715_, v_err_boxed_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object* v_toPure_719_, uint8_t v___x_720_, lean_object* v_toBind_721_, lean_object* v___f_722_, lean_object* v_____r_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_box(v___x_720_);
v___x_725_ = lean_apply_2(v_toPure_719_, lean_box(0), v___x_724_);
v___x_726_ = lean_apply_4(v_toBind_721_, lean_box(0), lean_box(0), v___x_725_, v___f_722_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object* v_toPure_727_, lean_object* v___x_728_, lean_object* v_toBind_729_, lean_object* v___f_730_, lean_object* v_____r_731_){
_start:
{
uint8_t v___x_558__boxed_732_; lean_object* v_res_733_; 
v___x_558__boxed_732_ = lean_unbox(v___x_728_);
v_res_733_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(v_toPure_727_, v___x_558__boxed_732_, v_toBind_729_, v___f_730_, v_____r_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object* v_env_734_, lean_object* v_p_735_, lean_object* v_ictx_736_, lean_object* v_s_737_, lean_object* v_toPure_738_, uint8_t v___x_739_, lean_object* v_toBind_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_____do__lift_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_s_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_746_ = lean_box(0);
v___x_747_ = lean_box(0);
lean_inc_ref(v_env_734_);
v___x_748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_748_, 0, v_env_734_);
lean_ctor_set(v___x_748_, 1, v_____do__lift_745_);
lean_ctor_set(v___x_748_, 2, v___x_746_);
lean_ctor_set(v___x_748_, 3, v___x_747_);
v___x_749_ = l_Lean_Parser_getTokenTable(v_env_734_);
lean_inc_ref(v_ictx_736_);
v_s_750_ = l_Lean_Parser_ParserFn_run(v_p_735_, v_ictx_736_, v___x_748_, v___x_749_, v_s_737_);
lean_inc(v_toPure_738_);
lean_inc_ref(v_s_750_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_751_, 0, v_s_750_);
lean_closure_set(v___f_751_, 1, v_toPure_738_);
lean_inc_ref(v_s_750_);
v___x_752_ = l_Lean_Parser_ParserState_allErrors(v_s_750_);
v___x_753_ = lean_array_get_size(v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_nat_dec_eq(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_756_, 0, v___f_751_);
v___x_757_ = lean_box(v___x_739_);
lean_inc(v_toBind_740_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_758_, 0, v_toPure_738_);
lean_closure_set(v___f_758_, 1, v___x_757_);
lean_closure_set(v___f_758_, 2, v_toBind_740_);
lean_closure_set(v___f_758_, 3, v___f_756_);
v___x_759_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_736_, v_s_750_);
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
v___x_762_ = l_Lean_logError___redArg(v_inst_741_, v_inst_742_, v_inst_743_, v_inst_744_, v___x_761_);
v___x_763_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_762_, v___f_758_);
return v___x_763_;
}
else
{
lean_object* v_pos_764_; uint8_t v___x_765_; 
v_pos_764_ = lean_ctor_get(v_s_750_, 2);
lean_inc(v_pos_764_);
v___x_765_ = l_Lean_Parser_InputContext_atEnd(v_ictx_736_, v_pos_764_);
lean_dec(v_pos_764_);
if (v___x_765_ == 0)
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_766_, 0, v___f_751_);
v___x_767_ = lean_box(v___x_739_);
lean_inc(v_toBind_740_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_768_, 0, v_toPure_738_);
lean_closure_set(v___f_768_, 1, v___x_767_);
lean_closure_set(v___f_768_, 2, v_toBind_740_);
lean_closure_set(v___f_768_, 3, v___f_766_);
v___x_769_ = ((lean_object*)(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0));
v___x_770_ = l_Lean_Parser_ParserState_mkError(v_s_750_, v___x_769_);
v___x_771_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_736_, v___x_770_);
v___x_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
v___x_773_ = l_Lean_MessageData_ofFormat(v___x_772_);
v___x_774_ = l_Lean_logError___redArg(v_inst_741_, v_inst_742_, v_inst_743_, v_inst_744_, v___x_773_);
v___x_775_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_774_, v___f_768_);
return v___x_775_;
}
else
{
lean_object* v___f_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_s_750_);
lean_dec(v_inst_744_);
lean_dec(v_inst_743_);
lean_dec_ref(v_inst_742_);
lean_dec_ref(v_inst_741_);
lean_dec_ref(v_ictx_736_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_776_, 0, v___f_751_);
v___x_777_ = 0;
v___x_778_ = lean_box(v___x_777_);
v___x_779_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_778_);
v___x_780_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_779_, v___f_776_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object* v_env_781_, lean_object* v_p_782_, lean_object* v_ictx_783_, lean_object* v_s_784_, lean_object* v_toPure_785_, lean_object* v___x_786_, lean_object* v_toBind_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_____do__lift_792_){
_start:
{
uint8_t v___x_574__boxed_793_; lean_object* v_res_794_; 
v___x_574__boxed_793_ = lean_unbox(v___x_786_);
v_res_794_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(v_env_781_, v_p_782_, v_ictx_783_, v_s_784_, v_toPure_785_, v___x_574__boxed_793_, v_toBind_787_, v_inst_788_, v_inst_789_, v_inst_790_, v_inst_791_, v_____do__lift_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object* v_source_795_, uint8_t v___x_796_, lean_object* v___y_797_, lean_object* v_env_798_, lean_object* v_p_799_, lean_object* v_toPure_800_, lean_object* v_toBind_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_s_806_, lean_object* v___x_807_, lean_object* v_____do__lift_808_){
_start:
{
lean_object* v_ictx_809_; lean_object* v___x_810_; lean_object* v___y_812_; lean_object* v___x_817_; 
lean_inc_ref(v_source_795_);
v_ictx_809_ = l_Lean_Parser_mkInputContext___redArg(v_source_795_, v_____do__lift_808_, v___x_796_, v___y_797_);
v___x_810_ = l_Lean_Parser_mkParserState(v_source_795_);
lean_dec_ref(v_source_795_);
v___x_817_ = l_Lean_Syntax_getPos_x3f(v_s_806_, v___x_796_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_819_ = l_panic___redArg(v___x_807_, v___x_818_);
v___y_812_ = v___x_819_;
goto v___jp_811_;
}
else
{
lean_object* v_val_820_; 
lean_dec(v___x_807_);
v_val_820_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v___x_817_);
v___y_812_ = v_val_820_;
goto v___jp_811_;
}
v___jp_811_:
{
lean_object* v_s_813_; lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; 
v_s_813_ = l_Lean_Parser_ParserState_setPos(v___x_810_, v___y_812_);
v___x_814_ = lean_box(v___x_796_);
lean_inc(v_inst_805_);
lean_inc(v_toBind_801_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_815_, 0, v_env_798_);
lean_closure_set(v___f_815_, 1, v_p_799_);
lean_closure_set(v___f_815_, 2, v_ictx_809_);
lean_closure_set(v___f_815_, 3, v_s_813_);
lean_closure_set(v___f_815_, 4, v_toPure_800_);
lean_closure_set(v___f_815_, 5, v___x_814_);
lean_closure_set(v___f_815_, 6, v_toBind_801_);
lean_closure_set(v___f_815_, 7, v_inst_802_);
lean_closure_set(v___f_815_, 8, v_inst_803_);
lean_closure_set(v___f_815_, 9, v_inst_804_);
lean_closure_set(v___f_815_, 10, v_inst_805_);
v___x_816_ = lean_apply_4(v_toBind_801_, lean_box(0), lean_box(0), v_inst_805_, v___f_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object* v_source_821_, lean_object* v___x_822_, lean_object* v___y_823_, lean_object* v_env_824_, lean_object* v_p_825_, lean_object* v_toPure_826_, lean_object* v_toBind_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_s_832_, lean_object* v___x_833_, lean_object* v_____do__lift_834_){
_start:
{
uint8_t v___x_667__boxed_835_; lean_object* v_res_836_; 
v___x_667__boxed_835_ = lean_unbox(v___x_822_);
v_res_836_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(v_source_821_, v___x_667__boxed_835_, v___y_823_, v_env_824_, v_p_825_, v_toPure_826_, v_toBind_827_, v_inst_828_, v_inst_829_, v_inst_830_, v_inst_831_, v_s_832_, v___x_833_, v_____do__lift_834_);
lean_dec(v_s_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object* v_text_837_, lean_object* v_inst_838_, lean_object* v_p_839_, lean_object* v_toPure_840_, lean_object* v_toBind_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_s_845_, lean_object* v___x_846_, lean_object* v_env_847_){
_start:
{
uint8_t v___x_848_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_857_; lean_object* v___x_861_; 
v___x_848_ = 1;
v___x_861_ = l_Lean_Syntax_getTailPos_x3f(v_s_845_, v___x_848_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
lean_inc(v___x_846_);
v___x_863_ = l_panic___redArg(v___x_846_, v___x_862_);
v___y_857_ = v___x_863_;
goto v___jp_856_;
}
else
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_val_864_);
lean_dec_ref(v___x_861_);
v___y_857_ = v_val_864_;
goto v___jp_856_;
}
v___jp_849_:
{
lean_object* v_getFileName_852_; lean_object* v___x_853_; lean_object* v___f_854_; lean_object* v___x_855_; 
v_getFileName_852_ = lean_ctor_get(v_inst_838_, 2);
lean_inc(v_getFileName_852_);
v___x_853_ = lean_box(v___x_848_);
lean_inc(v_toBind_841_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_854_, 0, v___y_850_);
lean_closure_set(v___f_854_, 1, v___x_853_);
lean_closure_set(v___f_854_, 2, v___y_851_);
lean_closure_set(v___f_854_, 3, v_env_847_);
lean_closure_set(v___f_854_, 4, v_p_839_);
lean_closure_set(v___f_854_, 5, v_toPure_840_);
lean_closure_set(v___f_854_, 6, v_toBind_841_);
lean_closure_set(v___f_854_, 7, v_inst_842_);
lean_closure_set(v___f_854_, 8, v_inst_838_);
lean_closure_set(v___f_854_, 9, v_inst_843_);
lean_closure_set(v___f_854_, 10, v_inst_844_);
lean_closure_set(v___f_854_, 11, v_s_845_);
lean_closure_set(v___f_854_, 12, v___x_846_);
v___x_855_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v_getFileName_852_, v___f_854_);
return v___x_855_;
}
v___jp_856_:
{
lean_object* v_source_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_source_858_ = lean_ctor_get(v_text_837_, 0);
lean_inc_ref(v_source_858_);
lean_dec_ref(v_text_837_);
v___x_859_ = lean_string_utf8_byte_size(v_source_858_);
v___x_860_ = lean_nat_dec_le(v___y_857_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v___y_857_);
v___y_850_ = v_source_858_;
v___y_851_ = v___x_859_;
goto v___jp_849_;
}
else
{
v___y_850_ = v_source_858_;
v___y_851_ = v___y_857_;
goto v___jp_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_p_867_, lean_object* v_toPure_868_, lean_object* v_toBind_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_s_873_, lean_object* v___x_874_, lean_object* v_text_875_){
_start:
{
lean_object* v_getEnv_876_; lean_object* v___f_877_; lean_object* v___x_878_; 
v_getEnv_876_ = lean_ctor_get(v_inst_865_, 0);
lean_inc(v_getEnv_876_);
lean_dec_ref(v_inst_865_);
lean_inc(v_toBind_869_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__4), 11, 10);
lean_closure_set(v___f_877_, 0, v_text_875_);
lean_closure_set(v___f_877_, 1, v_inst_866_);
lean_closure_set(v___f_877_, 2, v_p_867_);
lean_closure_set(v___f_877_, 3, v_toPure_868_);
lean_closure_set(v___f_877_, 4, v_toBind_869_);
lean_closure_set(v___f_877_, 5, v_inst_870_);
lean_closure_set(v___f_877_, 6, v_inst_871_);
lean_closure_set(v___f_877_, 7, v_inst_872_);
lean_closure_set(v___f_877_, 8, v_s_873_);
lean_closure_set(v___f_877_, 9, v___x_874_);
v___x_878_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v_getEnv_876_, v___f_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_p_885_, lean_object* v_s_886_){
_start:
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v_toPure_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_879_, 0);
v_toBind_888_ = lean_ctor_get(v_inst_879_, 1);
lean_inc(v_toBind_888_);
v_toPure_889_ = lean_ctor_get(v_toApplicative_887_, 1);
lean_inc(v_toPure_889_);
v___x_890_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_888_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__5), 11, 10);
lean_closure_set(v___f_891_, 0, v_inst_881_);
lean_closure_set(v___f_891_, 1, v_inst_883_);
lean_closure_set(v___f_891_, 2, v_p_885_);
lean_closure_set(v___f_891_, 3, v_toPure_889_);
lean_closure_set(v___f_891_, 4, v_toBind_888_);
lean_closure_set(v___f_891_, 5, v_inst_879_);
lean_closure_set(v___f_891_, 6, v_inst_882_);
lean_closure_set(v___f_891_, 7, v_inst_884_);
lean_closure_set(v___f_891_, 8, v_s_886_);
lean_closure_set(v___f_891_, 9, v___x_890_);
v___x_892_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v_inst_880_, v___f_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_p_900_, lean_object* v_s_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_894_, v_inst_895_, v_inst_896_, v_inst_897_, v_inst_898_, v_inst_899_, v_p_900_, v_s_901_);
return v___x_902_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Extension(builtin);
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
