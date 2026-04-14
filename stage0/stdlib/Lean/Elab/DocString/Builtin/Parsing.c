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
lean_inc_n(v_toBind_168_, 2);
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
switch(lean_obj_tag(v_x_378_))
{
case 0:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__3_381_);
lean_dec(v_h__2_380_);
lean_dec(v_h__1_379_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__4_382_, v___x_383_);
return v___x_384_;
}
case 1:
{
lean_object* v_info_385_; lean_object* v_kind_386_; lean_object* v_args_387_; lean_object* v___x_388_; 
lean_dec(v_h__4_382_);
lean_dec(v_h__3_381_);
lean_dec(v_h__2_380_);
v_info_385_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_info_385_);
v_kind_386_ = lean_ctor_get(v_x_378_, 1);
lean_inc(v_kind_386_);
v_args_387_ = lean_ctor_get(v_x_378_, 2);
lean_inc_ref(v_args_387_);
lean_dec_ref(v_x_378_);
v___x_388_ = lean_apply_3(v_h__1_379_, v_info_385_, v_kind_386_, v_args_387_);
return v___x_388_;
}
case 2:
{
lean_object* v_info_389_; lean_object* v_val_390_; lean_object* v___x_391_; 
lean_dec(v_h__4_382_);
lean_dec(v_h__2_380_);
lean_dec(v_h__1_379_);
v_info_389_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_info_389_);
v_val_390_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref(v_val_390_);
lean_dec_ref(v_x_378_);
v___x_391_ = lean_apply_2(v_h__3_381_, v_info_389_, v_val_390_);
return v___x_391_;
}
default: 
{
lean_object* v_info_392_; lean_object* v_rawVal_393_; lean_object* v_val_394_; lean_object* v_preresolved_395_; lean_object* v___x_396_; 
lean_dec(v_h__4_382_);
lean_dec(v_h__3_381_);
lean_dec(v_h__1_379_);
v_info_392_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_info_392_);
v_rawVal_393_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref(v_rawVal_393_);
v_val_394_ = lean_ctor_get(v_x_378_, 2);
lean_inc(v_val_394_);
v_preresolved_395_ = lean_ctor_get(v_x_378_, 3);
lean_inc(v_preresolved_395_);
lean_dec_ref(v_x_378_);
v___x_396_ = lean_apply_4(v_h__2_380_, v_info_392_, v_rawVal_393_, v_val_394_, v_preresolved_395_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_397_, lean_object* v_h__1_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_apply_2(v_h__1_398_, v_x_397_, lean_box(0));
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_400_, lean_object* v_P_401_, lean_object* v_motive_402_, lean_object* v_x_403_, lean_object* v_h__1_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_apply_2(v_h__1_404_, v_x_403_, lean_box(0));
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_text_406_, lean_object* v_pos_407_, lean_object* v_str_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_fst_410_ = lean_ctor_get(v_x_409_, 0);
v_snd_411_ = lean_ctor_get(v_x_409_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v_x_409_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_inc(v_fst_410_);
lean_dec(v_x_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_406_, v_pos_407_, v_str_408_, v_fst_410_);
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
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_411_);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(lean_object* v_text_420_, lean_object* v_pos_421_, lean_object* v_str_422_, lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(v_text_420_, v_pos_421_, v_str_422_, v_x_423_);
lean_dec_ref(v_str_422_);
lean_dec_ref(v_text_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_env_444_, lean_object* v_p_445_, lean_object* v_ictx_446_, lean_object* v_s_447_, lean_object* v_text_448_, lean_object* v_pos_449_, lean_object* v_str_450_, lean_object* v___f_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_toApplicative_454_, lean_object* v_____do__lift_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_s_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_box(0);
lean_inc_ref(v_env_444_);
v___x_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_458_, 0, v_env_444_);
lean_ctor_set(v___x_458_, 1, v_____do__lift_455_);
lean_ctor_set(v___x_458_, 2, v___x_456_);
lean_ctor_set(v___x_458_, 3, v___x_457_);
v___x_459_ = l_Lean_Parser_getTokenTable(v_env_444_);
lean_inc_ref(v_ictx_446_);
v_s_460_ = l_Lean_Parser_ParserFn_run(v_p_445_, v_ictx_446_, v___x_458_, v___x_459_, v_s_447_);
lean_inc_ref(v_s_460_);
v___x_461_ = l_Lean_Parser_ParserState_allErrors(v_s_460_);
v___x_462_ = lean_array_get_size(v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_nat_dec_eq(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v_stxStack_465_; lean_object* v_lhsPrec_466_; lean_object* v_pos_467_; lean_object* v_cache_468_; lean_object* v_errorMsg_469_; lean_object* v_recoveredErrors_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_toApplicative_454_);
v_stxStack_465_ = lean_ctor_get(v_s_460_, 0);
v_lhsPrec_466_ = lean_ctor_get(v_s_460_, 1);
v_pos_467_ = lean_ctor_get(v_s_460_, 2);
v_cache_468_ = lean_ctor_get(v_s_460_, 3);
v_errorMsg_469_ = lean_ctor_get(v_s_460_, 4);
v_recoveredErrors_470_ = lean_ctor_get(v_s_460_, 5);
v_isSharedCheck_507_ = !lean_is_exclusive(v_s_460_);
if (v_isSharedCheck_507_ == 0)
{
v___x_472_ = v_s_460_;
v_isShared_473_ = v_isSharedCheck_507_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_recoveredErrors_470_);
lean_inc(v_errorMsg_469_);
lean_inc(v_cache_468_);
lean_inc(v_pos_467_);
lean_inc(v_lhsPrec_466_);
lean_inc(v_stxStack_465_);
lean_dec(v_s_460_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_507_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___y_476_; 
lean_inc(v_pos_449_);
v___x_474_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_448_, v_pos_449_, v_str_450_, v_pos_467_);
if (lean_obj_tag(v_errorMsg_469_) == 0)
{
lean_dec(v_pos_449_);
v___y_476_ = v_errorMsg_469_;
goto v___jp_475_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_506_; 
v_val_488_ = lean_ctor_get(v_errorMsg_469_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_errorMsg_469_);
if (v_isSharedCheck_506_ == 0)
{
v___x_490_ = v_errorMsg_469_;
v_isShared_491_ = v_isSharedCheck_506_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_val_488_);
lean_dec(v_errorMsg_469_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_506_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_unexpectedTk_492_; lean_object* v_unexpected_493_; lean_object* v_expected_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_505_; 
v_unexpectedTk_492_ = lean_ctor_get(v_val_488_, 0);
v_unexpected_493_ = lean_ctor_get(v_val_488_, 1);
v_expected_494_ = lean_ctor_get(v_val_488_, 2);
v_isSharedCheck_505_ = !lean_is_exclusive(v_val_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_496_ = v_val_488_;
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_expected_494_);
lean_inc(v_unexpected_493_);
lean_inc(v_unexpectedTk_492_);
lean_dec(v_val_488_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_448_, v_pos_449_, v_str_450_, v_unexpectedTk_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_unexpected_493_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_expected_494_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_500_);
v___x_502_ = v___x_490_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v___y_476_ = v___x_502_;
goto v___jp_475_;
}
}
}
}
}
v___jp_475_:
{
lean_object* v___x_477_; size_t v_sz_478_; size_t v___x_479_; lean_object* v___x_480_; lean_object* v_s_482_; 
v___x_477_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9));
v_sz_478_ = lean_array_size(v_recoveredErrors_470_);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_477_, v___f_451_, v_sz_478_, v___x_479_, v_recoveredErrors_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 5, v___x_480_);
lean_ctor_set(v___x_472_, 4, v___y_476_);
lean_ctor_set(v___x_472_, 2, v___x_474_);
v_s_482_ = v___x_472_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_stxStack_465_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_lhsPrec_466_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_cache_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v___y_476_);
lean_ctor_set(v_reuseFailAlloc_487_, 5, v___x_480_);
v_s_482_ = v_reuseFailAlloc_487_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_446_, v_s_482_);
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
v___x_486_ = l_Lean_throwError___redArg(v_inst_452_, v_inst_453_, v___x_485_);
return v___x_486_;
}
}
}
}
else
{
lean_object* v_stxStack_508_; lean_object* v_pos_509_; uint8_t v___x_510_; 
lean_dec_ref(v___f_451_);
v_stxStack_508_ = lean_ctor_get(v_s_460_, 0);
lean_inc_ref(v_stxStack_508_);
v_pos_509_ = lean_ctor_get(v_s_460_, 2);
lean_inc(v_pos_509_);
v___x_510_ = l_Lean_Parser_InputContext_atEnd(v_ictx_446_, v_pos_509_);
lean_dec(v_pos_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v_stxStack_508_);
lean_dec_ref(v_toApplicative_454_);
lean_dec(v_pos_449_);
v___x_511_ = ((lean_object*)(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0));
v___x_512_ = l_Lean_Parser_ParserState_mkError(v_s_460_, v___x_511_);
v___x_513_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_446_, v___x_512_);
v___x_514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___x_515_ = l_Lean_MessageData_ofFormat(v___x_514_);
v___x_516_ = l_Lean_throwError___redArg(v_inst_452_, v_inst_453_, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v_toPure_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_s_460_);
lean_dec_ref(v_inst_453_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_ictx_446_);
v_toPure_517_ = lean_ctor_get(v_toApplicative_454_, 1);
lean_inc(v_toPure_517_);
lean_dec_ref(v_toApplicative_454_);
v___x_518_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_508_);
lean_dec_ref(v_stxStack_508_);
v___x_519_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_448_, v_pos_449_, v_str_450_, v___x_518_);
v___x_520_ = lean_apply_2(v_toPure_517_, lean_box(0), v___x_519_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_env_521_, lean_object* v_p_522_, lean_object* v_ictx_523_, lean_object* v_s_524_, lean_object* v_text_525_, lean_object* v_pos_526_, lean_object* v_str_527_, lean_object* v___f_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_toApplicative_531_, lean_object* v_____do__lift_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_env_521_, v_p_522_, v_ictx_523_, v_s_524_, v_text_525_, v_pos_526_, v_str_527_, v___f_528_, v_inst_529_, v_inst_530_, v_toApplicative_531_, v_____do__lift_532_);
lean_dec_ref(v_str_527_);
lean_dec_ref(v_text_525_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_str_534_, lean_object* v_env_535_, lean_object* v_p_536_, lean_object* v_text_537_, lean_object* v_pos_538_, lean_object* v___f_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_toApplicative_542_, lean_object* v_toBind_543_, lean_object* v_inst_544_, lean_object* v_____do__lift_545_){
_start:
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v_ictx_548_; lean_object* v_s_549_; lean_object* v___f_550_; lean_object* v___x_551_; 
v___x_546_ = 1;
v___x_547_ = lean_string_utf8_byte_size(v_str_534_);
lean_inc_ref(v_str_534_);
v_ictx_548_ = l_Lean_Parser_mkInputContext___redArg(v_str_534_, v_____do__lift_545_, v___x_546_, v___x_547_);
v_s_549_ = l_Lean_Parser_mkParserState(v_str_534_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_550_, 0, v_env_535_);
lean_closure_set(v___f_550_, 1, v_p_536_);
lean_closure_set(v___f_550_, 2, v_ictx_548_);
lean_closure_set(v___f_550_, 3, v_s_549_);
lean_closure_set(v___f_550_, 4, v_text_537_);
lean_closure_set(v___f_550_, 5, v_pos_538_);
lean_closure_set(v___f_550_, 6, v_str_534_);
lean_closure_set(v___f_550_, 7, v___f_539_);
lean_closure_set(v___f_550_, 8, v_inst_540_);
lean_closure_set(v___f_550_, 9, v_inst_541_);
lean_closure_set(v___f_550_, 10, v_toApplicative_542_);
v___x_551_ = lean_apply_4(v_toBind_543_, lean_box(0), lean_box(0), v_inst_544_, v___f_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_552_, lean_object* v_strLit_553_, lean_object* v_text_554_, lean_object* v_env_555_, lean_object* v_p_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_toApplicative_559_, lean_object* v_toBind_560_, lean_object* v_inst_561_, lean_object* v_pos_562_){
_start:
{
lean_object* v_getFileName_563_; lean_object* v_str_564_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; 
v_getFileName_563_ = lean_ctor_get(v_inst_552_, 2);
lean_inc(v_getFileName_563_);
lean_dec_ref(v_inst_552_);
v_str_564_ = l_Lean_TSyntax_getString(v_strLit_553_);
lean_inc_ref(v_str_564_);
lean_inc(v_pos_562_);
lean_inc_ref(v_text_554_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_565_, 0, v_text_554_);
lean_closure_set(v___f_565_, 1, v_pos_562_);
lean_closure_set(v___f_565_, 2, v_str_564_);
lean_inc(v_toBind_560_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2), 12, 11);
lean_closure_set(v___f_566_, 0, v_str_564_);
lean_closure_set(v___f_566_, 1, v_env_555_);
lean_closure_set(v___f_566_, 2, v_p_556_);
lean_closure_set(v___f_566_, 3, v_text_554_);
lean_closure_set(v___f_566_, 4, v_pos_562_);
lean_closure_set(v___f_566_, 5, v___f_565_);
lean_closure_set(v___f_566_, 6, v_inst_557_);
lean_closure_set(v___f_566_, 7, v_inst_558_);
lean_closure_set(v___f_566_, 8, v_toApplicative_559_);
lean_closure_set(v___f_566_, 9, v_toBind_560_);
lean_closure_set(v___f_566_, 10, v_inst_561_);
v___x_567_ = lean_apply_4(v_toBind_560_, lean_box(0), lean_box(0), v_getFileName_563_, v___f_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_568_, lean_object* v_strLit_569_, lean_object* v_text_570_, lean_object* v_env_571_, lean_object* v_p_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_toApplicative_575_, lean_object* v_toBind_576_, lean_object* v_inst_577_, lean_object* v_pos_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_568_, v_strLit_569_, v_text_570_, v_env_571_, v_p_572_, v_inst_573_, v_inst_574_, v_toApplicative_575_, v_toBind_576_, v_inst_577_, v_pos_578_);
lean_dec(v_strLit_569_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v___f_580_, lean_object* v_pos_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_apply_1(v___f_580_, v_pos_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v_text_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_strLit_589_, lean_object* v_toBind_590_, lean_object* v___f_591_, lean_object* v_toApplicative_592_, lean_object* v___f_593_, lean_object* v_____r_594_, lean_object* v_pos_595_){
_start:
{
lean_object* v_source_596_; uint32_t v___x_597_; uint32_t v___x_598_; uint8_t v___x_599_; 
v_source_596_ = lean_ctor_get(v_text_586_, 0);
v___x_597_ = lean_string_utf8_get(v_source_596_, v_pos_595_);
v___x_598_ = 34;
v___x_599_ = lean_uint32_dec_eq(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___f_593_);
lean_dec_ref(v_toApplicative_592_);
v___x_600_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1);
v___x_601_ = l_Lean_throwErrorAt___redArg(v_inst_587_, v_inst_588_, v_strLit_589_, v___x_600_);
v___x_602_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_601_, v___f_591_);
return v___x_602_;
}
else
{
lean_object* v_toPure_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v___f_591_);
lean_dec(v_strLit_589_);
lean_dec_ref(v_inst_588_);
lean_dec_ref(v_inst_587_);
v_toPure_603_ = lean_ctor_get(v_toApplicative_592_, 1);
lean_inc(v_toPure_603_);
lean_dec_ref(v_toApplicative_592_);
v___x_604_ = lean_string_utf8_next(v_source_596_, v_pos_595_);
v___x_605_ = lean_apply_2(v_toPure_603_, lean_box(0), v___x_604_);
v___x_606_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_605_, v___f_593_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object* v_text_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_strLit_610_, lean_object* v_toBind_611_, lean_object* v___f_612_, lean_object* v_toApplicative_613_, lean_object* v___f_614_, lean_object* v_____r_615_, lean_object* v_pos_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(v_text_607_, v_inst_608_, v_inst_609_, v_strLit_610_, v_toBind_611_, v___f_612_, v_toApplicative_613_, v___f_614_, v_____r_615_, v_pos_616_);
lean_dec(v_pos_616_);
lean_dec_ref(v_text_607_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_618_, lean_object* v_____s_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_2(v___f_618_, v___x_620_, v_____s_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_source_622_, lean_object* v_toApplicative_623_, lean_object* v_x_624_, lean_object* v_____s_625_){
_start:
{
uint32_t v___x_626_; uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_string_utf8_get(v_source_622_, v_____s_625_);
v___x_627_ = 35;
v___x_628_ = lean_uint32_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v_toPure_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_toPure_629_ = lean_ctor_get(v_toApplicative_623_, 1);
lean_inc(v_toPure_629_);
lean_dec_ref(v_toApplicative_623_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_____s_625_);
v___x_631_ = lean_apply_2(v_toPure_629_, lean_box(0), v___x_630_);
return v___x_631_;
}
else
{
lean_object* v_toPure_632_; lean_object* v_pos_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_toPure_632_ = lean_ctor_get(v_toApplicative_623_, 1);
lean_inc(v_toPure_632_);
lean_dec_ref(v_toApplicative_623_);
v_pos_633_ = lean_string_utf8_next(v_source_622_, v_____s_625_);
lean_dec(v_____s_625_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_pos_633_);
v___x_635_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_source_636_, lean_object* v_toApplicative_637_, lean_object* v_x_638_, lean_object* v_____s_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_source_636_, v_toApplicative_637_, v_x_638_, v_____s_639_);
lean_dec_ref(v_source_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_text_641_, lean_object* v___f_642_, lean_object* v_toApplicative_643_, lean_object* v_inst_644_, lean_object* v_toBind_645_, lean_object* v___f_646_, lean_object* v_____x_647_){
_start:
{
lean_object* v_start_648_; lean_object* v_source_649_; uint32_t v___x_650_; uint32_t v___x_651_; uint8_t v___x_652_; 
v_start_648_ = lean_ctor_get(v_____x_647_, 0);
lean_inc(v_start_648_);
lean_dec_ref(v_____x_647_);
v_source_649_ = lean_ctor_get(v_text_641_, 0);
lean_inc_ref(v_source_649_);
lean_dec_ref(v_text_641_);
v___x_650_ = lean_string_utf8_get(v_source_649_, v_start_648_);
v___x_651_ = 114;
v___x_652_ = lean_uint32_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref(v_source_649_);
lean_dec(v___f_646_);
lean_dec(v_toBind_645_);
lean_dec_ref(v_inst_644_);
lean_dec_ref(v_toApplicative_643_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_apply_2(v___f_642_, v___x_653_, v_start_648_);
return v___x_654_;
}
else
{
lean_object* v___f_655_; lean_object* v_pos_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v___f_642_);
lean_inc_ref(v_source_649_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_655_, 0, v_source_649_);
lean_closure_set(v___f_655_, 1, v_toApplicative_643_);
v_pos_656_ = lean_string_utf8_next(v_source_649_, v_start_648_);
lean_dec(v_start_648_);
lean_dec_ref(v_source_649_);
v___x_657_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_644_, v___f_655_, v_pos_656_);
v___x_658_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v___x_657_, v___f_646_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_inst_659_, lean_object* v_strLit_660_, lean_object* v_text_661_, lean_object* v_p_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_toApplicative_665_, lean_object* v_toBind_666_, lean_object* v_inst_667_, lean_object* v_env_668_){
_start:
{
lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc_n(v_toBind_666_, 3);
lean_inc_ref_n(v_toApplicative_665_, 2);
lean_inc_ref(v_inst_664_);
lean_inc_ref_n(v_inst_663_, 3);
lean_inc_ref_n(v_text_661_, 2);
lean_inc_n(v_strLit_660_, 2);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_669_, 0, v_inst_659_);
lean_closure_set(v___f_669_, 1, v_strLit_660_);
lean_closure_set(v___f_669_, 2, v_text_661_);
lean_closure_set(v___f_669_, 3, v_env_668_);
lean_closure_set(v___f_669_, 4, v_p_662_);
lean_closure_set(v___f_669_, 5, v_inst_663_);
lean_closure_set(v___f_669_, 6, v_inst_664_);
lean_closure_set(v___f_669_, 7, v_toApplicative_665_);
lean_closure_set(v___f_669_, 8, v_toBind_666_);
lean_closure_set(v___f_669_, 9, v_inst_667_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4), 2, 1);
lean_closure_set(v___f_670_, 0, v___f_669_);
lean_inc_ref(v___f_670_);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_671_, 0, v_text_661_);
lean_closure_set(v___f_671_, 1, v_inst_663_);
lean_closure_set(v___f_671_, 2, v_inst_664_);
lean_closure_set(v___f_671_, 3, v_strLit_660_);
lean_closure_set(v___f_671_, 4, v_toBind_666_);
lean_closure_set(v___f_671_, 5, v___f_670_);
lean_closure_set(v___f_671_, 6, v_toApplicative_665_);
lean_closure_set(v___f_671_, 7, v___f_670_);
lean_inc_ref(v___f_671_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_672_, 0, v___f_671_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_673_, 0, v_text_661_);
lean_closure_set(v___f_673_, 1, v___f_671_);
lean_closure_set(v___f_673_, 2, v_toApplicative_665_);
lean_closure_set(v___f_673_, 3, v_inst_663_);
lean_closure_set(v___f_673_, 4, v_toBind_666_);
lean_closure_set(v___f_673_, 5, v___f_672_);
v___x_674_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_663_, v_strLit_660_);
lean_dec(v_strLit_660_);
v___x_675_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v___x_674_, v___f_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_strLit_678_, lean_object* v_p_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_toApplicative_682_, lean_object* v_toBind_683_, lean_object* v_inst_684_, lean_object* v_text_685_){
_start:
{
lean_object* v_getEnv_686_; lean_object* v___f_687_; lean_object* v___x_688_; 
v_getEnv_686_ = lean_ctor_get(v_inst_676_, 0);
lean_inc(v_getEnv_686_);
lean_dec_ref(v_inst_676_);
lean_inc(v_toBind_683_);
v___f_687_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 10, 9);
lean_closure_set(v___f_687_, 0, v_inst_677_);
lean_closure_set(v___f_687_, 1, v_strLit_678_);
lean_closure_set(v___f_687_, 2, v_text_685_);
lean_closure_set(v___f_687_, 3, v_p_679_);
lean_closure_set(v___f_687_, 4, v_inst_680_);
lean_closure_set(v___f_687_, 5, v_inst_681_);
lean_closure_set(v___f_687_, 6, v_toApplicative_682_);
lean_closure_set(v___f_687_, 7, v_toBind_683_);
lean_closure_set(v___f_687_, 8, v_inst_684_);
v___x_688_ = lean_apply_4(v_toBind_683_, lean_box(0), lean_box(0), v_getEnv_686_, v___f_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_p_695_, lean_object* v_strLit_696_){
_start:
{
lean_object* v_toApplicative_697_; lean_object* v_toBind_698_; lean_object* v___f_699_; lean_object* v___x_700_; 
v_toApplicative_697_ = lean_ctor_get(v_inst_689_, 0);
lean_inc_ref(v_toApplicative_697_);
v_toBind_698_ = lean_ctor_get(v_inst_689_, 1);
lean_inc_n(v_toBind_698_, 2);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10), 10, 9);
lean_closure_set(v___f_699_, 0, v_inst_691_);
lean_closure_set(v___f_699_, 1, v_inst_693_);
lean_closure_set(v___f_699_, 2, v_strLit_696_);
lean_closure_set(v___f_699_, 3, v_p_695_);
lean_closure_set(v___f_699_, 4, v_inst_689_);
lean_closure_set(v___f_699_, 5, v_inst_692_);
lean_closure_set(v___f_699_, 6, v_toApplicative_697_);
lean_closure_set(v___f_699_, 7, v_toBind_698_);
lean_closure_set(v___f_699_, 8, v_inst_694_);
v___x_700_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v_inst_690_, v___f_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_p_708_, lean_object* v_strLit_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_inst_706_, v_inst_707_, v_p_708_, v_strLit_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object* v_s_711_, lean_object* v_toPure_712_, uint8_t v_err_713_){
_start:
{
lean_object* v_stxStack_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_stxStack_714_ = lean_ctor_get(v_s_711_, 0);
v___x_715_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_714_);
v___x_716_ = lean_box(v_err_713_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_apply_2(v_toPure_712_, lean_box(0), v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object* v_s_719_, lean_object* v_toPure_720_, lean_object* v_err_721_){
_start:
{
uint8_t v_err_boxed_722_; lean_object* v_res_723_; 
v_err_boxed_722_ = lean_unbox(v_err_721_);
v_res_723_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_719_, v_toPure_720_, v_err_boxed_722_);
lean_dec_ref(v_s_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object* v___f_724_, uint8_t v_err_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(v_err_725_);
v___x_727_ = lean_apply_1(v___f_724_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object* v___f_728_, lean_object* v_err_729_){
_start:
{
uint8_t v_err_boxed_730_; lean_object* v_res_731_; 
v_err_boxed_730_ = lean_unbox(v_err_729_);
v_res_731_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_728_, v_err_boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object* v_toPure_732_, uint8_t v___x_733_, lean_object* v_toBind_734_, lean_object* v___f_735_, lean_object* v_____r_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_box(v___x_733_);
v___x_738_ = lean_apply_2(v_toPure_732_, lean_box(0), v___x_737_);
v___x_739_ = lean_apply_4(v_toBind_734_, lean_box(0), lean_box(0), v___x_738_, v___f_735_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object* v_toPure_740_, lean_object* v___x_741_, lean_object* v_toBind_742_, lean_object* v___f_743_, lean_object* v_____r_744_){
_start:
{
uint8_t v___x_559__boxed_745_; lean_object* v_res_746_; 
v___x_559__boxed_745_ = lean_unbox(v___x_741_);
v_res_746_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(v_toPure_740_, v___x_559__boxed_745_, v_toBind_742_, v___f_743_, v_____r_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object* v_env_747_, lean_object* v_p_748_, lean_object* v_ictx_749_, lean_object* v_s_750_, lean_object* v_toPure_751_, uint8_t v___x_752_, lean_object* v_toBind_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_____do__lift_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_s_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_box(0);
lean_inc_ref(v_env_747_);
v___x_761_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_761_, 0, v_env_747_);
lean_ctor_set(v___x_761_, 1, v_____do__lift_758_);
lean_ctor_set(v___x_761_, 2, v___x_759_);
lean_ctor_set(v___x_761_, 3, v___x_760_);
v___x_762_ = l_Lean_Parser_getTokenTable(v_env_747_);
lean_inc_ref(v_ictx_749_);
v_s_763_ = l_Lean_Parser_ParserFn_run(v_p_748_, v_ictx_749_, v___x_761_, v___x_762_, v_s_750_);
lean_inc(v_toPure_751_);
lean_inc_ref_n(v_s_763_, 2);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_764_, 0, v_s_763_);
lean_closure_set(v___f_764_, 1, v_toPure_751_);
v___x_765_ = l_Lean_Parser_ParserState_allErrors(v_s_763_);
v___x_766_ = lean_array_get_size(v___x_765_);
lean_dec_ref(v___x_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_nat_dec_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_769_, 0, v___f_764_);
v___x_770_ = lean_box(v___x_752_);
lean_inc(v_toBind_753_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_771_, 0, v_toPure_751_);
lean_closure_set(v___f_771_, 1, v___x_770_);
lean_closure_set(v___f_771_, 2, v_toBind_753_);
lean_closure_set(v___f_771_, 3, v___f_769_);
v___x_772_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_749_, v_s_763_);
v___x_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = l_Lean_MessageData_ofFormat(v___x_773_);
v___x_775_ = l_Lean_logError___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v___x_774_);
v___x_776_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_775_, v___f_771_);
return v___x_776_;
}
else
{
lean_object* v_pos_777_; uint8_t v___x_778_; 
v_pos_777_ = lean_ctor_get(v_s_763_, 2);
lean_inc(v_pos_777_);
v___x_778_ = l_Lean_Parser_InputContext_atEnd(v_ictx_749_, v_pos_777_);
lean_dec(v_pos_777_);
if (v___x_778_ == 0)
{
lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_779_, 0, v___f_764_);
v___x_780_ = lean_box(v___x_752_);
lean_inc(v_toBind_753_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_781_, 0, v_toPure_751_);
lean_closure_set(v___f_781_, 1, v___x_780_);
lean_closure_set(v___f_781_, 2, v_toBind_753_);
lean_closure_set(v___f_781_, 3, v___f_779_);
v___x_782_ = ((lean_object*)(l_Lean_Doc_parseStrLit___redArg___lam__0___closed__0));
v___x_783_ = l_Lean_Parser_ParserState_mkError(v_s_763_, v___x_782_);
v___x_784_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_749_, v___x_783_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
v___x_786_ = l_Lean_MessageData_ofFormat(v___x_785_);
v___x_787_ = l_Lean_logError___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v___x_786_);
v___x_788_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_787_, v___f_781_);
return v___x_788_;
}
else
{
lean_object* v___f_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_s_763_);
lean_dec(v_inst_757_);
lean_dec(v_inst_756_);
lean_dec_ref(v_inst_755_);
lean_dec_ref(v_inst_754_);
lean_dec_ref(v_ictx_749_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_789_, 0, v___f_764_);
v___x_790_ = 0;
v___x_791_ = lean_box(v___x_790_);
v___x_792_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_791_);
v___x_793_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_792_, v___f_789_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object* v_env_794_, lean_object* v_p_795_, lean_object* v_ictx_796_, lean_object* v_s_797_, lean_object* v_toPure_798_, lean_object* v___x_799_, lean_object* v_toBind_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_____do__lift_805_){
_start:
{
uint8_t v___x_575__boxed_806_; lean_object* v_res_807_; 
v___x_575__boxed_806_ = lean_unbox(v___x_799_);
v_res_807_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(v_env_794_, v_p_795_, v_ictx_796_, v_s_797_, v_toPure_798_, v___x_575__boxed_806_, v_toBind_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_____do__lift_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object* v_source_808_, uint8_t v___x_809_, lean_object* v___y_810_, lean_object* v_env_811_, lean_object* v_p_812_, lean_object* v_toPure_813_, lean_object* v_toBind_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_s_819_, lean_object* v___x_820_, lean_object* v_____do__lift_821_){
_start:
{
lean_object* v_ictx_822_; lean_object* v___x_823_; lean_object* v___y_825_; lean_object* v___x_830_; 
lean_inc_ref(v_source_808_);
v_ictx_822_ = l_Lean_Parser_mkInputContext___redArg(v_source_808_, v_____do__lift_821_, v___x_809_, v___y_810_);
v___x_823_ = l_Lean_Parser_mkParserState(v_source_808_);
lean_dec_ref(v_source_808_);
v___x_830_ = l_Lean_Syntax_getPos_x3f(v_s_819_, v___x_809_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_832_ = l_panic___redArg(v___x_820_, v___x_831_);
v___y_825_ = v___x_832_;
goto v___jp_824_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v___x_830_);
v___y_825_ = v_val_833_;
goto v___jp_824_;
}
v___jp_824_:
{
lean_object* v_s_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; 
v_s_826_ = l_Lean_Parser_ParserState_setPos(v___x_823_, v___y_825_);
v___x_827_ = lean_box(v___x_809_);
lean_inc(v_inst_818_);
lean_inc(v_toBind_814_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_828_, 0, v_env_811_);
lean_closure_set(v___f_828_, 1, v_p_812_);
lean_closure_set(v___f_828_, 2, v_ictx_822_);
lean_closure_set(v___f_828_, 3, v_s_826_);
lean_closure_set(v___f_828_, 4, v_toPure_813_);
lean_closure_set(v___f_828_, 5, v___x_827_);
lean_closure_set(v___f_828_, 6, v_toBind_814_);
lean_closure_set(v___f_828_, 7, v_inst_815_);
lean_closure_set(v___f_828_, 8, v_inst_816_);
lean_closure_set(v___f_828_, 9, v_inst_817_);
lean_closure_set(v___f_828_, 10, v_inst_818_);
v___x_829_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v_inst_818_, v___f_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object* v_source_834_, lean_object* v___x_835_, lean_object* v___y_836_, lean_object* v_env_837_, lean_object* v_p_838_, lean_object* v_toPure_839_, lean_object* v_toBind_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_s_845_, lean_object* v___x_846_, lean_object* v_____do__lift_847_){
_start:
{
uint8_t v___x_668__boxed_848_; lean_object* v_res_849_; 
v___x_668__boxed_848_ = lean_unbox(v___x_835_);
v_res_849_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(v_source_834_, v___x_668__boxed_848_, v___y_836_, v_env_837_, v_p_838_, v_toPure_839_, v_toBind_840_, v_inst_841_, v_inst_842_, v_inst_843_, v_inst_844_, v_s_845_, v___x_846_, v_____do__lift_847_);
lean_dec(v___x_846_);
lean_dec(v_s_845_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object* v_text_850_, lean_object* v_inst_851_, lean_object* v_p_852_, lean_object* v_toPure_853_, lean_object* v_toBind_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_s_858_, lean_object* v___x_859_, lean_object* v_env_860_){
_start:
{
uint8_t v___x_861_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_870_; lean_object* v___x_874_; 
v___x_861_ = 1;
v___x_874_ = l_Lean_Syntax_getTailPos_x3f(v_s_858_, v___x_861_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_876_ = l_panic___redArg(v___x_859_, v___x_875_);
v___y_870_ = v___x_876_;
goto v___jp_869_;
}
else
{
lean_object* v_val_877_; 
v_val_877_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_877_);
lean_dec_ref(v___x_874_);
v___y_870_ = v_val_877_;
goto v___jp_869_;
}
v___jp_862_:
{
lean_object* v_getFileName_865_; lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___x_868_; 
v_getFileName_865_ = lean_ctor_get(v_inst_851_, 2);
lean_inc(v_getFileName_865_);
v___x_866_ = lean_box(v___x_861_);
lean_inc(v_toBind_854_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_867_, 0, v___y_863_);
lean_closure_set(v___f_867_, 1, v___x_866_);
lean_closure_set(v___f_867_, 2, v___y_864_);
lean_closure_set(v___f_867_, 3, v_env_860_);
lean_closure_set(v___f_867_, 4, v_p_852_);
lean_closure_set(v___f_867_, 5, v_toPure_853_);
lean_closure_set(v___f_867_, 6, v_toBind_854_);
lean_closure_set(v___f_867_, 7, v_inst_855_);
lean_closure_set(v___f_867_, 8, v_inst_851_);
lean_closure_set(v___f_867_, 9, v_inst_856_);
lean_closure_set(v___f_867_, 10, v_inst_857_);
lean_closure_set(v___f_867_, 11, v_s_858_);
lean_closure_set(v___f_867_, 12, v___x_859_);
v___x_868_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v_getFileName_865_, v___f_867_);
return v___x_868_;
}
v___jp_869_:
{
lean_object* v_source_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_source_871_ = lean_ctor_get(v_text_850_, 0);
lean_inc_ref(v_source_871_);
lean_dec_ref(v_text_850_);
v___x_872_ = lean_string_utf8_byte_size(v_source_871_);
v___x_873_ = lean_nat_dec_le(v___y_870_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec(v___y_870_);
v___y_863_ = v_source_871_;
v___y_864_ = v___x_872_;
goto v___jp_862_;
}
else
{
v___y_863_ = v_source_871_;
v___y_864_ = v___y_870_;
goto v___jp_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_p_880_, lean_object* v_toPure_881_, lean_object* v_toBind_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_s_886_, lean_object* v___x_887_, lean_object* v_text_888_){
_start:
{
lean_object* v_getEnv_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
v_getEnv_889_ = lean_ctor_get(v_inst_878_, 0);
lean_inc(v_getEnv_889_);
lean_dec_ref(v_inst_878_);
lean_inc(v_toBind_882_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__4), 11, 10);
lean_closure_set(v___f_890_, 0, v_text_888_);
lean_closure_set(v___f_890_, 1, v_inst_879_);
lean_closure_set(v___f_890_, 2, v_p_880_);
lean_closure_set(v___f_890_, 3, v_toPure_881_);
lean_closure_set(v___f_890_, 4, v_toBind_882_);
lean_closure_set(v___f_890_, 5, v_inst_883_);
lean_closure_set(v___f_890_, 6, v_inst_884_);
lean_closure_set(v___f_890_, 7, v_inst_885_);
lean_closure_set(v___f_890_, 8, v_s_886_);
lean_closure_set(v___f_890_, 9, v___x_887_);
v___x_891_ = lean_apply_4(v_toBind_882_, lean_box(0), lean_box(0), v_getEnv_889_, v___f_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_p_898_, lean_object* v_s_899_){
_start:
{
lean_object* v_toApplicative_900_; lean_object* v_toBind_901_; lean_object* v_toPure_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; 
v_toApplicative_900_ = lean_ctor_get(v_inst_892_, 0);
v_toBind_901_ = lean_ctor_get(v_inst_892_, 1);
lean_inc_n(v_toBind_901_, 2);
v_toPure_902_ = lean_ctor_get(v_toApplicative_900_, 1);
lean_inc(v_toPure_902_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__5), 11, 10);
lean_closure_set(v___f_904_, 0, v_inst_894_);
lean_closure_set(v___f_904_, 1, v_inst_896_);
lean_closure_set(v___f_904_, 2, v_p_898_);
lean_closure_set(v___f_904_, 3, v_toPure_902_);
lean_closure_set(v___f_904_, 4, v_toBind_901_);
lean_closure_set(v___f_904_, 5, v_inst_892_);
lean_closure_set(v___f_904_, 6, v_inst_895_);
lean_closure_set(v___f_904_, 7, v_inst_897_);
lean_closure_set(v___f_904_, 8, v_s_899_);
lean_closure_set(v___f_904_, 9, v___x_903_);
v___x_905_ = lean_apply_4(v_toBind_901_, lean_box(0), lean_box(0), v_inst_893_, v___f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_p_913_, lean_object* v_s_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_907_, v_inst_908_, v_inst_909_, v_inst_910_, v_inst_911_, v_inst_912_, v_p_913_, v_s_914_);
return v___x_915_;
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
