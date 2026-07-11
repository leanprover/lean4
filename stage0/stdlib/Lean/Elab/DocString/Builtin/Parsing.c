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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Not a quoted string literal"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_34_, 1);
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
lean_dec_ref_known(v___x_30_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object* v_env_52_, lean_object* v_contents_53_, lean_object* v_p_54_, lean_object* v_ictx_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_toApplicative_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_s_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; uint8_t v___x_70_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_box(0);
lean_inc_ref(v_env_52_);
v___x_62_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_62_, 0, v_env_52_);
lean_ctor_set(v___x_62_, 1, v_____do__lift_59_);
lean_ctor_set(v___x_62_, 2, v___x_60_);
lean_ctor_set(v___x_62_, 3, v___x_61_);
v___x_63_ = l_Lean_Parser_getTokenTable(v_env_52_);
v___x_64_ = l_Lean_Parser_mkParserState(v_contents_53_);
lean_inc_ref(v_ictx_55_);
v_s_65_ = l_Lean_Parser_ParserFn_run(v_p_54_, v_ictx_55_, v___x_62_, v___x_63_, v___x_64_);
lean_inc_ref(v_s_65_);
v___x_66_ = l_Lean_Parser_ParserState_allErrors(v_s_65_);
v___x_67_ = lean_array_get_size(v___x_66_);
lean_dec_ref(v___x_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
v___x_70_ = lean_bool_not(v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v_stxStack_71_; lean_object* v_pos_72_; uint8_t v___x_73_; 
v_stxStack_71_ = lean_ctor_get(v_s_65_, 0);
lean_inc_ref(v_stxStack_71_);
v_pos_72_ = lean_ctor_get(v_s_65_, 2);
lean_inc(v_pos_72_);
v___x_73_ = l_Lean_Parser_InputContext_atEnd(v_ictx_55_, v_pos_72_);
lean_dec(v_pos_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v_stxStack_71_);
lean_dec_ref(v_toApplicative_58_);
v___x_74_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_75_ = l_Lean_Parser_ParserState_mkError(v_s_65_, v___x_74_);
v___x_76_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v___x_75_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
v___x_79_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_toPure_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_s_65_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_ictx_55_);
v_toPure_80_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_80_);
lean_dec_ref(v_toApplicative_58_);
v___x_81_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_71_);
lean_dec_ref(v_stxStack_71_);
v___x_82_ = lean_apply_2(v_toPure_80_, lean_box(0), v___x_81_);
return v___x_82_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v_toApplicative_58_);
v___x_83_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v_s_65_);
v___x_84_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
v___x_85_ = l_Lean_MessageData_ofFormat(v___x_84_);
v___x_86_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_87_, lean_object* v_contents_88_, lean_object* v_p_89_, lean_object* v_ictx_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_toApplicative_93_, lean_object* v_____do__lift_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_87_, v_contents_88_, v_p_89_, v_ictx_90_, v_inst_91_, v_inst_92_, v_toApplicative_93_, v_____do__lift_94_);
lean_dec_ref(v_contents_88_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_contents_96_, lean_object* v_env_97_, lean_object* v_p_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_toApplicative_101_, lean_object* v_toBind_102_, lean_object* v_inst_103_, lean_object* v_____do__lift_104_){
_start:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v_ictx_107_; lean_object* v___f_108_; lean_object* v___x_109_; 
v___x_105_ = 1;
v___x_106_ = lean_string_utf8_byte_size(v_contents_96_);
lean_inc_ref(v_contents_96_);
v_ictx_107_ = l_Lean_Parser_mkInputContext___redArg(v_contents_96_, v_____do__lift_104_, v___x_105_, v___x_106_);
v___f_108_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_108_, 0, v_env_97_);
lean_closure_set(v___f_108_, 1, v_contents_96_);
lean_closure_set(v___f_108_, 2, v_p_98_);
lean_closure_set(v___f_108_, 3, v_ictx_107_);
lean_closure_set(v___f_108_, 4, v_inst_99_);
lean_closure_set(v___f_108_, 5, v_inst_100_);
lean_closure_set(v___f_108_, 6, v_toApplicative_101_);
v___x_109_ = lean_apply_4(v_toBind_102_, lean_box(0), lean_box(0), v_inst_103_, v___f_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_110_, lean_object* v_contents_111_, lean_object* v_p_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_toApplicative_115_, lean_object* v_toBind_116_, lean_object* v_inst_117_, lean_object* v_env_118_){
_start:
{
lean_object* v_getFileName_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_getFileName_119_ = lean_ctor_get(v_inst_110_, 2);
lean_inc(v_getFileName_119_);
lean_dec_ref(v_inst_110_);
lean_inc(v_toBind_116_);
v___f_120_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_120_, 0, v_contents_111_);
lean_closure_set(v___f_120_, 1, v_env_118_);
lean_closure_set(v___f_120_, 2, v_p_112_);
lean_closure_set(v___f_120_, 3, v_inst_113_);
lean_closure_set(v___f_120_, 4, v_inst_114_);
lean_closure_set(v___f_120_, 5, v_toApplicative_115_);
lean_closure_set(v___f_120_, 6, v_toBind_116_);
lean_closure_set(v___f_120_, 7, v_inst_117_);
v___x_121_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v_getFileName_119_, v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_p_127_, lean_object* v_contents_128_){
_start:
{
lean_object* v_toApplicative_129_; lean_object* v_toBind_130_; lean_object* v_getEnv_131_; lean_object* v___f_132_; lean_object* v___x_133_; 
v_toApplicative_129_ = lean_ctor_get(v_inst_122_, 0);
lean_inc_ref(v_toApplicative_129_);
v_toBind_130_ = lean_ctor_get(v_inst_122_, 1);
lean_inc_n(v_toBind_130_, 2);
v_getEnv_131_ = lean_ctor_get(v_inst_123_, 0);
lean_inc(v_getEnv_131_);
lean_dec_ref(v_inst_123_);
v___f_132_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_132_, 0, v_inst_125_);
lean_closure_set(v___f_132_, 1, v_contents_128_);
lean_closure_set(v___f_132_, 2, v_p_127_);
lean_closure_set(v___f_132_, 3, v_inst_122_);
lean_closure_set(v___f_132_, 4, v_inst_124_);
lean_closure_set(v___f_132_, 5, v_toApplicative_129_);
lean_closure_set(v___f_132_, 6, v_toBind_130_);
lean_closure_set(v___f_132_, 7, v_inst_126_);
v___x_133_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v_getEnv_131_, v___f_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_p_140_, lean_object* v_contents_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_p_140_, v_contents_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object* v_env_143_, lean_object* v_p_144_, lean_object* v_ictx_145_, lean_object* v_s_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_toApplicative_149_, lean_object* v_____do__lift_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_s_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; uint8_t v___x_160_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_box(0);
lean_inc_ref(v_env_143_);
v___x_153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_153_, 0, v_env_143_);
lean_ctor_set(v___x_153_, 1, v_____do__lift_150_);
lean_ctor_set(v___x_153_, 2, v___x_151_);
lean_ctor_set(v___x_153_, 3, v___x_152_);
v___x_154_ = l_Lean_Parser_getTokenTable(v_env_143_);
lean_inc_ref(v_ictx_145_);
v_s_155_ = l_Lean_Parser_ParserFn_run(v_p_144_, v_ictx_145_, v___x_153_, v___x_154_, v_s_146_);
lean_inc_ref(v_s_155_);
v___x_156_ = l_Lean_Parser_ParserState_allErrors(v_s_155_);
v___x_157_ = lean_array_get_size(v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v___x_157_, v___x_158_);
v___x_160_ = lean_bool_not(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v_stxStack_161_; lean_object* v_pos_162_; uint8_t v___x_163_; 
v_stxStack_161_ = lean_ctor_get(v_s_155_, 0);
lean_inc_ref(v_stxStack_161_);
v_pos_162_ = lean_ctor_get(v_s_155_, 2);
lean_inc(v_pos_162_);
v___x_163_ = l_Lean_Parser_InputContext_atEnd(v_ictx_145_, v_pos_162_);
lean_dec(v_pos_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v_stxStack_161_);
lean_dec_ref(v_toApplicative_149_);
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_165_ = l_Lean_Parser_ParserState_mkError(v_s_155_, v___x_164_);
v___x_166_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_145_, v___x_165_);
v___x_167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
v___x_168_ = l_Lean_MessageData_ofFormat(v___x_167_);
v___x_169_ = l_Lean_throwError___redArg(v_inst_147_, v_inst_148_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_toPure_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_s_155_);
lean_dec_ref(v_inst_148_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_ictx_145_);
v_toPure_170_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_toApplicative_149_);
v___x_171_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_161_);
lean_dec_ref(v_stxStack_161_);
v___x_172_ = lean_apply_2(v_toPure_170_, lean_box(0), v___x_171_);
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_toApplicative_149_);
v___x_173_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_145_, v_s_155_);
v___x_174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___x_175_ = l_Lean_MessageData_ofFormat(v___x_174_);
v___x_176_ = l_Lean_throwError___redArg(v_inst_147_, v_inst_148_, v___x_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object* v_source_177_, uint8_t v___x_178_, lean_object* v___y_179_, lean_object* v_start_180_, lean_object* v_env_181_, lean_object* v_p_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_toApplicative_185_, lean_object* v_toBind_186_, lean_object* v_inst_187_, lean_object* v_____do__lift_188_){
_start:
{
lean_object* v_ictx_189_; lean_object* v___x_190_; lean_object* v_s_191_; lean_object* v___f_192_; lean_object* v___x_193_; 
lean_inc_ref(v_source_177_);
v_ictx_189_ = l_Lean_Parser_mkInputContext___redArg(v_source_177_, v_____do__lift_188_, v___x_178_, v___y_179_);
v___x_190_ = l_Lean_Parser_mkParserState(v_source_177_);
lean_dec_ref(v_source_177_);
v_s_191_ = l_Lean_Parser_ParserState_setPos(v___x_190_, v_start_180_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__0), 8, 7);
lean_closure_set(v___f_192_, 0, v_env_181_);
lean_closure_set(v___f_192_, 1, v_p_182_);
lean_closure_set(v___f_192_, 2, v_ictx_189_);
lean_closure_set(v___f_192_, 3, v_s_191_);
lean_closure_set(v___f_192_, 4, v_inst_183_);
lean_closure_set(v___f_192_, 5, v_inst_184_);
lean_closure_set(v___f_192_, 6, v_toApplicative_185_);
v___x_193_ = lean_apply_4(v_toBind_186_, lean_box(0), lean_box(0), v_inst_187_, v___f_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1___boxed(lean_object* v_source_194_, lean_object* v___x_195_, lean_object* v___y_196_, lean_object* v_start_197_, lean_object* v_env_198_, lean_object* v_p_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_toApplicative_202_, lean_object* v_toBind_203_, lean_object* v_inst_204_, lean_object* v_____do__lift_205_){
_start:
{
uint8_t v___x_677__boxed_206_; lean_object* v_res_207_; 
v___x_677__boxed_206_ = lean_unbox(v___x_195_);
v_res_207_ = l_Lean_Doc_parseStrLit___redArg___lam__1(v_source_194_, v___x_677__boxed_206_, v___y_196_, v_start_197_, v_env_198_, v_p_199_, v_inst_200_, v_inst_201_, v_toApplicative_202_, v_toBind_203_, v_inst_204_, v_____do__lift_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object* v_text_208_, lean_object* v_inst_209_, uint8_t v___x_210_, lean_object* v_env_211_, lean_object* v_p_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_toApplicative_215_, lean_object* v_toBind_216_, lean_object* v_inst_217_, lean_object* v_____x_218_){
_start:
{
lean_object* v_start_219_; lean_object* v_stop_220_; lean_object* v_source_221_; lean_object* v___y_223_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_start_219_ = lean_ctor_get(v_____x_218_, 0);
lean_inc(v_start_219_);
v_stop_220_ = lean_ctor_get(v_____x_218_, 1);
lean_inc(v_stop_220_);
lean_dec_ref(v_____x_218_);
v_source_221_ = lean_ctor_get(v_text_208_, 0);
lean_inc_ref(v_source_221_);
lean_dec_ref(v_text_208_);
v___x_228_ = lean_string_utf8_byte_size(v_source_221_);
v___x_229_ = lean_nat_dec_le(v_stop_220_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_stop_220_);
v___y_223_ = v___x_228_;
goto v___jp_222_;
}
else
{
v___y_223_ = v_stop_220_;
goto v___jp_222_;
}
v___jp_222_:
{
lean_object* v_getFileName_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___x_227_; 
v_getFileName_224_ = lean_ctor_get(v_inst_209_, 2);
lean_inc(v_getFileName_224_);
lean_dec_ref(v_inst_209_);
v___x_225_ = lean_box(v___x_210_);
lean_inc(v_toBind_216_);
v___f_226_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_226_, 0, v_source_221_);
lean_closure_set(v___f_226_, 1, v___x_225_);
lean_closure_set(v___f_226_, 2, v___y_223_);
lean_closure_set(v___f_226_, 3, v_start_219_);
lean_closure_set(v___f_226_, 4, v_env_211_);
lean_closure_set(v___f_226_, 5, v_p_212_);
lean_closure_set(v___f_226_, 6, v_inst_213_);
lean_closure_set(v___f_226_, 7, v_inst_214_);
lean_closure_set(v___f_226_, 8, v_toApplicative_215_);
lean_closure_set(v___f_226_, 9, v_toBind_216_);
lean_closure_set(v___f_226_, 10, v_inst_217_);
v___x_227_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v_getFileName_224_, v___f_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2___boxed(lean_object* v_text_230_, lean_object* v_inst_231_, lean_object* v___x_232_, lean_object* v_env_233_, lean_object* v_p_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_toApplicative_237_, lean_object* v_toBind_238_, lean_object* v_inst_239_, lean_object* v_____x_240_){
_start:
{
uint8_t v___x_705__boxed_241_; lean_object* v_res_242_; 
v___x_705__boxed_241_ = lean_unbox(v___x_232_);
v_res_242_ = l_Lean_Doc_parseStrLit___redArg___lam__2(v_text_230_, v_inst_231_, v___x_705__boxed_241_, v_env_233_, v_p_234_, v_inst_235_, v_inst_236_, v_toApplicative_237_, v_toBind_238_, v_inst_239_, v_____x_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object* v_text_243_, lean_object* v_inst_244_, uint8_t v___x_245_, lean_object* v_p_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_toApplicative_249_, lean_object* v_toBind_250_, lean_object* v_inst_251_, lean_object* v_s_252_, lean_object* v_env_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_box(v___x_245_);
lean_inc(v_toBind_250_);
lean_inc_ref(v_inst_247_);
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_255_, 0, v_text_243_);
lean_closure_set(v___f_255_, 1, v_inst_244_);
lean_closure_set(v___f_255_, 2, v___x_254_);
lean_closure_set(v___f_255_, 3, v_env_253_);
lean_closure_set(v___f_255_, 4, v_p_246_);
lean_closure_set(v___f_255_, 5, v_inst_247_);
lean_closure_set(v___f_255_, 6, v_inst_248_);
lean_closure_set(v___f_255_, 7, v_toApplicative_249_);
lean_closure_set(v___f_255_, 8, v_toBind_250_);
lean_closure_set(v___f_255_, 9, v_inst_251_);
v___x_256_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_247_, v_s_252_);
v___x_257_ = lean_apply_4(v_toBind_250_, lean_box(0), lean_box(0), v___x_256_, v___f_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object* v_text_258_, lean_object* v_inst_259_, lean_object* v___x_260_, lean_object* v_p_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_toApplicative_264_, lean_object* v_toBind_265_, lean_object* v_inst_266_, lean_object* v_s_267_, lean_object* v_env_268_){
_start:
{
uint8_t v___x_741__boxed_269_; lean_object* v_res_270_; 
v___x_741__boxed_269_ = lean_unbox(v___x_260_);
v_res_270_ = l_Lean_Doc_parseStrLit___redArg___lam__3(v_text_258_, v_inst_259_, v___x_741__boxed_269_, v_p_261_, v_inst_262_, v_inst_263_, v_toApplicative_264_, v_toBind_265_, v_inst_266_, v_s_267_, v_env_268_);
lean_dec(v_s_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object* v_inst_271_, lean_object* v_inst_272_, uint8_t v___x_273_, lean_object* v_p_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_toApplicative_277_, lean_object* v_toBind_278_, lean_object* v_inst_279_, lean_object* v_s_280_, lean_object* v_text_281_){
_start:
{
lean_object* v_getEnv_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___x_285_; 
v_getEnv_282_ = lean_ctor_get(v_inst_271_, 0);
lean_inc(v_getEnv_282_);
lean_dec_ref(v_inst_271_);
v___x_283_ = lean_box(v___x_273_);
lean_inc(v_toBind_278_);
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_284_, 0, v_text_281_);
lean_closure_set(v___f_284_, 1, v_inst_272_);
lean_closure_set(v___f_284_, 2, v___x_283_);
lean_closure_set(v___f_284_, 3, v_p_274_);
lean_closure_set(v___f_284_, 4, v_inst_275_);
lean_closure_set(v___f_284_, 5, v_inst_276_);
lean_closure_set(v___f_284_, 6, v_toApplicative_277_);
lean_closure_set(v___f_284_, 7, v_toBind_278_);
lean_closure_set(v___f_284_, 8, v_inst_279_);
lean_closure_set(v___f_284_, 9, v_s_280_);
v___x_285_ = lean_apply_4(v_toBind_278_, lean_box(0), lean_box(0), v_getEnv_282_, v___f_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4___boxed(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v___x_288_, lean_object* v_p_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_toApplicative_292_, lean_object* v_toBind_293_, lean_object* v_inst_294_, lean_object* v_s_295_, lean_object* v_text_296_){
_start:
{
uint8_t v___x_765__boxed_297_; lean_object* v_res_298_; 
v___x_765__boxed_297_ = lean_unbox(v___x_288_);
v_res_298_ = l_Lean_Doc_parseStrLit___redArg___lam__4(v_inst_286_, v_inst_287_, v___x_765__boxed_297_, v_p_289_, v_inst_290_, v_inst_291_, v_toApplicative_292_, v_toBind_293_, v_inst_294_, v_s_295_, v_text_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_p_305_, lean_object* v_s_306_){
_start:
{
uint8_t v___x_307_; lean_object* v___x_308_; 
v___x_307_ = 1;
v___x_308_ = l_Lean_Syntax_getPos_x3f(v_s_306_, v___x_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_inst_300_);
v___x_309_ = l_Lean_TSyntax_getString(v_s_306_);
lean_dec(v_s_306_);
v___x_310_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_299_, v_inst_301_, v_inst_302_, v_inst_303_, v_inst_304_, v_p_305_, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v_toApplicative_311_; lean_object* v_toBind_312_; lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
lean_dec_ref_known(v___x_308_, 1);
v_toApplicative_311_ = lean_ctor_get(v_inst_299_, 0);
lean_inc_ref(v_toApplicative_311_);
v_toBind_312_ = lean_ctor_get(v_inst_299_, 1);
lean_inc_n(v_toBind_312_, 2);
v___x_313_ = lean_box(v___x_307_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_314_, 0, v_inst_301_);
lean_closure_set(v___f_314_, 1, v_inst_303_);
lean_closure_set(v___f_314_, 2, v___x_313_);
lean_closure_set(v___f_314_, 3, v_p_305_);
lean_closure_set(v___f_314_, 4, v_inst_299_);
lean_closure_set(v___f_314_, 5, v_inst_302_);
lean_closure_set(v___f_314_, 6, v_toApplicative_311_);
lean_closure_set(v___f_314_, 7, v_toBind_312_);
lean_closure_set(v___f_314_, 8, v_inst_304_);
lean_closure_set(v___f_314_, 9, v_s_306_);
v___x_315_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v_inst_300_, v___f_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_p_323_, lean_object* v_s_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Doc_parseStrLit___redArg(v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_inst_321_, v_inst_322_, v_p_323_, v_s_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_345_; 
v_fst_328_ = lean_ctor_get(v_a_327_, 0);
v_snd_329_ = lean_ctor_get(v_a_327_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_327_);
if (v_isSharedCheck_345_ == 0)
{
v___x_331_ = v_a_327_;
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snd_329_);
lean_inc(v_fst_328_);
lean_dec(v_a_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_nat_dec_lt(v___x_333_, v_fst_328_);
if (v___x_334_ == 0)
{
lean_object* v___x_336_; 
if (v_isShared_332_ == 0)
{
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_fst_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_snd_329_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_338_ = lean_string_utf8_prev(v_str_326_, v_fst_328_);
lean_dec(v_fst_328_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_snd_329_, v___x_339_);
lean_dec(v_snd_329_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_340_);
lean_ctor_set(v___x_331_, 0, v___x_338_);
v___x_342_ = v___x_331_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
v_a_327_ = v___x_342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_346_, v_a_347_);
lean_dec_ref(v_str_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_349_, lean_object* v_p_350_){
_start:
{
lean_object* v_n_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_snd_354_; 
v_n_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_p_350_);
lean_ctor_set(v___x_352_, 1, v_n_351_);
v___x_353_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_349_, v___x_352_);
v_snd_354_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_snd_354_);
lean_dec_ref(v___x_353_);
return v_snd_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_355_, lean_object* v_p_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_355_, v_p_356_);
lean_dec_ref(v_str_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_358_, lean_object* v_inst_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_358_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_362_, lean_object* v_inst_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_362_, v_inst_363_, v_a_364_);
lean_dec_ref(v_str_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_366_, lean_object* v_p_367_, lean_object* v_j_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_zero_370_; uint8_t v_isZero_371_; 
v_zero_370_ = lean_unsigned_to_nat(0u);
v_isZero_371_ = lean_nat_dec_eq(v_j_368_, v_zero_370_);
if (v_isZero_371_ == 1)
{
lean_dec(v_j_368_);
return v_a_369_;
}
else
{
lean_object* v_one_372_; lean_object* v_n_373_; lean_object* v___x_374_; 
lean_dec(v_a_369_);
v_one_372_ = lean_unsigned_to_nat(1u);
v_n_373_ = lean_nat_sub(v_j_368_, v_one_372_);
lean_dec(v_j_368_);
v___x_374_ = lean_string_utf8_next(v_str_366_, v_p_367_);
v_j_368_ = v_n_373_;
v_a_369_ = v___x_374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_376_, lean_object* v_p_377_, lean_object* v_j_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_376_, v_p_377_, v_j_378_, v_a_379_);
lean_dec(v_p_377_);
lean_dec_ref(v_str_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_381_, lean_object* v_n_382_, lean_object* v_p_383_){
_start:
{
lean_object* v___x_384_; 
lean_inc(v_p_383_);
v___x_384_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_381_, v_p_383_, v_n_382_, v_p_383_);
lean_dec(v_p_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_385_, lean_object* v_n_386_, lean_object* v_p_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_385_, v_n_386_, v_p_387_);
lean_dec_ref(v_str_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_389_, lean_object* v_p_390_, lean_object* v_n_391_, lean_object* v_j_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_389_, v_p_390_, v_j_392_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_396_, lean_object* v_p_397_, lean_object* v_n_398_, lean_object* v_j_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_396_, v_p_397_, v_n_398_, v_j_399_, v_a_400_, v_a_401_);
lean_dec(v_n_398_);
lean_dec(v_p_397_);
lean_dec_ref(v_str_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_403_, lean_object* v_posOfStr_404_, lean_object* v_str_405_, lean_object* v_posInStr_406_){
_start:
{
lean_object* v_source_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_source_407_ = lean_ctor_get(v_text_403_, 0);
v___x_408_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_405_, v_posInStr_406_);
lean_inc(v_posOfStr_404_);
v___x_409_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_407_, v_posOfStr_404_, v___x_408_, v_posOfStr_404_);
lean_dec(v_posOfStr_404_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_410_, lean_object* v_posOfStr_411_, lean_object* v_str_412_, lean_object* v_posInStr_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_410_, v_posOfStr_411_, v_str_412_, v_posInStr_413_);
lean_dec_ref(v_str_412_);
lean_dec_ref(v_text_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_415_, lean_object* v_posOfStr_416_, lean_object* v_str_417_, lean_object* v_a_418_){
_start:
{
switch(lean_obj_tag(v_a_418_))
{
case 0:
{
lean_object* v_pos_419_; lean_object* v_endPos_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; 
v_pos_419_ = lean_ctor_get(v_a_418_, 1);
lean_inc(v_pos_419_);
v_endPos_420_ = lean_ctor_get(v_a_418_, 3);
lean_inc(v_endPos_420_);
lean_dec_ref_known(v_a_418_, 4);
lean_inc(v_posOfStr_416_);
v___x_421_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_415_, v_posOfStr_416_, v_str_417_, v_pos_419_);
v___x_422_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_415_, v_posOfStr_416_, v_str_417_, v_endPos_420_);
v___x_423_ = 1;
v___x_424_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*2, v___x_423_);
return v___x_424_;
}
case 1:
{
lean_object* v_pos_425_; lean_object* v_endPos_426_; uint8_t v_canonical_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
v_pos_425_ = lean_ctor_get(v_a_418_, 0);
v_endPos_426_ = lean_ctor_get(v_a_418_, 1);
v_canonical_427_ = lean_ctor_get_uint8(v_a_418_, sizeof(void*)*2);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v_a_418_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_endPos_426_);
lean_inc(v_pos_425_);
lean_dec(v_a_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_posOfStr_416_);
v___x_431_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_415_, v_posOfStr_416_, v_str_417_, v_pos_425_);
v___x_432_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_415_, v_posOfStr_416_, v_str_417_, v_endPos_426_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_432_);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*2, v_canonical_427_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
default: 
{
lean_dec(v_posOfStr_416_);
return v_a_418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_437_, lean_object* v_posOfStr_438_, lean_object* v_str_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_437_, v_posOfStr_438_, v_str_439_, v_a_440_);
lean_dec_ref(v_str_439_);
lean_dec_ref(v_text_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_442_, lean_object* v_posOfStr_443_, lean_object* v_str_444_, lean_object* v_a_445_){
_start:
{
switch(lean_obj_tag(v_a_445_))
{
case 0:
{
lean_dec(v_posOfStr_443_);
return v_a_445_;
}
case 1:
{
lean_object* v_info_446_; lean_object* v_kind_447_; lean_object* v_args_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_459_; 
v_info_446_ = lean_ctor_get(v_a_445_, 0);
v_kind_447_ = lean_ctor_get(v_a_445_, 1);
v_args_448_ = lean_ctor_get(v_a_445_, 2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_450_ = v_a_445_;
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_args_448_);
lean_inc(v_kind_447_);
lean_inc(v_info_446_);
lean_dec(v_a_445_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_459_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; size_t v_sz_453_; size_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
lean_inc(v_posOfStr_443_);
v___x_452_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_442_, v_posOfStr_443_, v_str_444_, v_info_446_);
v_sz_453_ = lean_array_size(v_args_448_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_442_, v_posOfStr_443_, v_str_444_, v_sz_453_, v___x_454_, v_args_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 2, v___x_455_);
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_457_ = v___x_450_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_kind_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
case 2:
{
lean_object* v_info_460_; lean_object* v_val_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_info_460_ = lean_ctor_get(v_a_445_, 0);
v_val_461_ = lean_ctor_get(v_a_445_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v_a_445_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_val_461_);
lean_inc(v_info_460_);
lean_dec(v_a_445_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_442_, v_posOfStr_443_, v_str_444_, v_info_460_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_val_461_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
default: 
{
lean_object* v_info_470_; lean_object* v_rawVal_471_; lean_object* v_val_472_; lean_object* v_preresolved_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_info_470_ = lean_ctor_get(v_a_445_, 0);
v_rawVal_471_ = lean_ctor_get(v_a_445_, 1);
v_val_472_ = lean_ctor_get(v_a_445_, 2);
v_preresolved_473_ = lean_ctor_get(v_a_445_, 3);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v_a_445_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_preresolved_473_);
lean_inc(v_val_472_);
lean_inc(v_rawVal_471_);
lean_inc(v_info_470_);
lean_dec(v_a_445_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_442_, v_posOfStr_443_, v_str_444_, v_info_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_rawVal_471_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_val_472_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_preresolved_473_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_482_, lean_object* v_posOfStr_483_, lean_object* v_str_484_, size_t v_sz_485_, size_t v_i_486_, lean_object* v_bs_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_486_, v_sz_485_);
if (v___x_488_ == 0)
{
lean_dec(v_posOfStr_483_);
return v_bs_487_;
}
else
{
lean_object* v_v_489_; lean_object* v___x_490_; lean_object* v_bs_x27_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_v_489_ = lean_array_uget(v_bs_487_, v_i_486_);
v___x_490_ = lean_unsigned_to_nat(0u);
v_bs_x27_491_ = lean_array_uset(v_bs_487_, v_i_486_, v___x_490_);
lean_inc(v_posOfStr_483_);
v___x_492_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_482_, v_posOfStr_483_, v_str_484_, v_v_489_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_486_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_491_, v_i_486_, v___x_492_);
v_i_486_ = v___x_494_;
v_bs_487_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_497_, lean_object* v_posOfStr_498_, lean_object* v_str_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_bs_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_504_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_497_, v_posOfStr_498_, v_str_499_, v_sz_boxed_503_, v_i_boxed_504_, v_bs_502_);
lean_dec_ref(v_str_499_);
lean_dec_ref(v_text_497_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_506_, lean_object* v_posOfStr_507_, lean_object* v_str_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_506_, v_posOfStr_507_, v_str_508_, v_a_509_);
lean_dec_ref(v_str_508_);
lean_dec_ref(v_text_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_, lean_object* v_h__4_515_){
_start:
{
switch(lean_obj_tag(v_x_511_))
{
case 0:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_1(v_h__4_515_, v___x_516_);
return v___x_517_;
}
case 1:
{
lean_object* v_info_518_; lean_object* v_kind_519_; lean_object* v_args_520_; lean_object* v___x_521_; 
lean_dec(v_h__4_515_);
lean_dec(v_h__3_514_);
lean_dec(v_h__2_513_);
v_info_518_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_info_518_);
v_kind_519_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_kind_519_);
v_args_520_ = lean_ctor_get(v_x_511_, 2);
lean_inc_ref(v_args_520_);
lean_dec_ref_known(v_x_511_, 3);
v___x_521_ = lean_apply_3(v_h__1_512_, v_info_518_, v_kind_519_, v_args_520_);
return v___x_521_;
}
case 2:
{
lean_object* v_info_522_; lean_object* v_val_523_; lean_object* v___x_524_; 
lean_dec(v_h__4_515_);
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
v_info_522_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_info_522_);
v_val_523_ = lean_ctor_get(v_x_511_, 1);
lean_inc_ref(v_val_523_);
lean_dec_ref_known(v_x_511_, 2);
v___x_524_ = lean_apply_2(v_h__3_514_, v_info_522_, v_val_523_);
return v___x_524_;
}
default: 
{
lean_object* v_info_525_; lean_object* v_rawVal_526_; lean_object* v_val_527_; lean_object* v_preresolved_528_; lean_object* v___x_529_; 
lean_dec(v_h__4_515_);
lean_dec(v_h__3_514_);
lean_dec(v_h__1_512_);
v_info_525_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_info_525_);
v_rawVal_526_ = lean_ctor_get(v_x_511_, 1);
lean_inc_ref(v_rawVal_526_);
v_val_527_ = lean_ctor_get(v_x_511_, 2);
lean_inc(v_val_527_);
v_preresolved_528_ = lean_ctor_get(v_x_511_, 3);
lean_inc(v_preresolved_528_);
lean_dec_ref_known(v_x_511_, 4);
v___x_529_ = lean_apply_4(v_h__2_513_, v_info_525_, v_rawVal_526_, v_val_527_, v_preresolved_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_530_, lean_object* v_x_531_, lean_object* v_h__1_532_, lean_object* v_h__2_533_, lean_object* v_h__3_534_, lean_object* v_h__4_535_){
_start:
{
switch(lean_obj_tag(v_x_531_))
{
case 0:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_h__3_534_);
lean_dec(v_h__2_533_);
lean_dec(v_h__1_532_);
v___x_536_ = lean_box(0);
v___x_537_ = lean_apply_1(v_h__4_535_, v___x_536_);
return v___x_537_;
}
case 1:
{
lean_object* v_info_538_; lean_object* v_kind_539_; lean_object* v_args_540_; lean_object* v___x_541_; 
lean_dec(v_h__4_535_);
lean_dec(v_h__3_534_);
lean_dec(v_h__2_533_);
v_info_538_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_info_538_);
v_kind_539_ = lean_ctor_get(v_x_531_, 1);
lean_inc(v_kind_539_);
v_args_540_ = lean_ctor_get(v_x_531_, 2);
lean_inc_ref(v_args_540_);
lean_dec_ref_known(v_x_531_, 3);
v___x_541_ = lean_apply_3(v_h__1_532_, v_info_538_, v_kind_539_, v_args_540_);
return v___x_541_;
}
case 2:
{
lean_object* v_info_542_; lean_object* v_val_543_; lean_object* v___x_544_; 
lean_dec(v_h__4_535_);
lean_dec(v_h__2_533_);
lean_dec(v_h__1_532_);
v_info_542_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_info_542_);
v_val_543_ = lean_ctor_get(v_x_531_, 1);
lean_inc_ref(v_val_543_);
lean_dec_ref_known(v_x_531_, 2);
v___x_544_ = lean_apply_2(v_h__3_534_, v_info_542_, v_val_543_);
return v___x_544_;
}
default: 
{
lean_object* v_info_545_; lean_object* v_rawVal_546_; lean_object* v_val_547_; lean_object* v_preresolved_548_; lean_object* v___x_549_; 
lean_dec(v_h__4_535_);
lean_dec(v_h__3_534_);
lean_dec(v_h__1_532_);
v_info_545_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_info_545_);
v_rawVal_546_ = lean_ctor_get(v_x_531_, 1);
lean_inc_ref(v_rawVal_546_);
v_val_547_ = lean_ctor_get(v_x_531_, 2);
lean_inc(v_val_547_);
v_preresolved_548_ = lean_ctor_get(v_x_531_, 3);
lean_inc(v_preresolved_548_);
lean_dec_ref_known(v_x_531_, 4);
v___x_549_ = lean_apply_4(v_h__2_533_, v_info_545_, v_rawVal_546_, v_val_547_, v_preresolved_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_550_, lean_object* v_h__1_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_apply_2(v_h__1_551_, v_x_550_, lean_box(0));
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_553_, lean_object* v_P_554_, lean_object* v_motive_555_, lean_object* v_x_556_, lean_object* v_h__1_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_apply_2(v_h__1_557_, v_x_556_, lean_box(0));
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_text_559_, lean_object* v_pos_560_, lean_object* v_str_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_572_; 
v_fst_563_ = lean_ctor_get(v_x_562_, 0);
v_snd_564_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_572_ == 0)
{
v___x_566_ = v_x_562_;
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
lean_dec(v_x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_559_, v_pos_560_, v_str_561_, v_fst_563_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_564_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(lean_object* v_text_573_, lean_object* v_pos_574_, lean_object* v_str_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(v_text_573_, v_pos_574_, v_str_575_, v_x_576_);
lean_dec_ref(v_str_575_);
lean_dec_ref(v_text_573_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_env_597_, lean_object* v_p_598_, lean_object* v_ictx_599_, lean_object* v_s_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_toApplicative_603_, lean_object* v_text_604_, lean_object* v_pos_605_, lean_object* v_str_606_, lean_object* v___f_607_, lean_object* v_____do__lift_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_s_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_box(0);
lean_inc_ref(v_env_597_);
v___x_611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_611_, 0, v_env_597_);
lean_ctor_set(v___x_611_, 1, v_____do__lift_608_);
lean_ctor_set(v___x_611_, 2, v___x_609_);
lean_ctor_set(v___x_611_, 3, v___x_610_);
v___x_612_ = l_Lean_Parser_getTokenTable(v_env_597_);
lean_inc_ref(v_ictx_599_);
v_s_613_ = l_Lean_Parser_ParserFn_run(v_p_598_, v_ictx_599_, v___x_611_, v___x_612_, v_s_600_);
lean_inc_ref(v_s_613_);
v___x_614_ = l_Lean_Parser_ParserState_allErrors(v_s_613_);
v___x_615_ = lean_array_get_size(v___x_614_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_nat_dec_eq(v___x_615_, v___x_616_);
v___x_618_ = lean_bool_not(v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v_stxStack_619_; lean_object* v_pos_620_; uint8_t v___x_621_; 
lean_dec_ref(v___f_607_);
v_stxStack_619_ = lean_ctor_get(v_s_613_, 0);
lean_inc_ref(v_stxStack_619_);
v_pos_620_ = lean_ctor_get(v_s_613_, 2);
lean_inc(v_pos_620_);
v___x_621_ = l_Lean_Parser_InputContext_atEnd(v_ictx_599_, v_pos_620_);
lean_dec(v_pos_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_stxStack_619_);
lean_dec(v_pos_605_);
lean_dec_ref(v_toApplicative_603_);
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_623_ = l_Lean_Parser_ParserState_mkError(v_s_613_, v___x_622_);
v___x_624_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_599_, v___x_623_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = l_Lean_MessageData_ofFormat(v___x_625_);
v___x_627_ = l_Lean_throwError___redArg(v_inst_601_, v_inst_602_, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v_toPure_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_s_613_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_inst_601_);
lean_dec_ref(v_ictx_599_);
v_toPure_628_ = lean_ctor_get(v_toApplicative_603_, 1);
lean_inc(v_toPure_628_);
lean_dec_ref(v_toApplicative_603_);
v___x_629_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_619_);
lean_dec_ref(v_stxStack_619_);
v___x_630_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_604_, v_pos_605_, v_str_606_, v___x_629_);
v___x_631_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_630_);
return v___x_631_;
}
}
else
{
lean_object* v_stxStack_632_; lean_object* v_lhsPrec_633_; lean_object* v_pos_634_; lean_object* v_cache_635_; lean_object* v_errorMsg_636_; lean_object* v_recoveredErrors_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_toApplicative_603_);
v_stxStack_632_ = lean_ctor_get(v_s_613_, 0);
v_lhsPrec_633_ = lean_ctor_get(v_s_613_, 1);
v_pos_634_ = lean_ctor_get(v_s_613_, 2);
v_cache_635_ = lean_ctor_get(v_s_613_, 3);
v_errorMsg_636_ = lean_ctor_get(v_s_613_, 4);
v_recoveredErrors_637_ = lean_ctor_get(v_s_613_, 5);
v_isSharedCheck_674_ = !lean_is_exclusive(v_s_613_);
if (v_isSharedCheck_674_ == 0)
{
v___x_639_ = v_s_613_;
v_isShared_640_ = v_isSharedCheck_674_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_recoveredErrors_637_);
lean_inc(v_errorMsg_636_);
lean_inc(v_cache_635_);
lean_inc(v_pos_634_);
lean_inc(v_lhsPrec_633_);
lean_inc(v_stxStack_632_);
lean_dec(v_s_613_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_674_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___y_643_; 
lean_inc(v_pos_605_);
v___x_641_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_604_, v_pos_605_, v_str_606_, v_pos_634_);
if (lean_obj_tag(v_errorMsg_636_) == 0)
{
lean_dec(v_pos_605_);
v___y_643_ = v_errorMsg_636_;
goto v___jp_642_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_673_; 
v_val_655_ = lean_ctor_get(v_errorMsg_636_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_errorMsg_636_);
if (v_isSharedCheck_673_ == 0)
{
v___x_657_ = v_errorMsg_636_;
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v_errorMsg_636_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_unexpectedTk_659_; lean_object* v_unexpected_660_; lean_object* v_expected_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v_unexpectedTk_659_ = lean_ctor_get(v_val_655_, 0);
v_unexpected_660_ = lean_ctor_get(v_val_655_, 1);
v_expected_661_ = lean_ctor_get(v_val_655_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_val_655_);
if (v_isSharedCheck_672_ == 0)
{
v___x_663_ = v_val_655_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_expected_661_);
lean_inc(v_unexpected_660_);
lean_inc(v_unexpectedTk_659_);
lean_dec(v_val_655_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_604_, v_pos_605_, v_str_606_, v_unexpectedTk_659_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_unexpected_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_expected_661_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_667_);
v___x_669_ = v___x_657_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v___y_643_ = v___x_669_;
goto v___jp_642_;
}
}
}
}
}
v___jp_642_:
{
lean_object* v___x_644_; size_t v_sz_645_; size_t v___x_646_; lean_object* v___x_647_; lean_object* v_s_649_; 
v___x_644_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9));
v_sz_645_ = lean_array_size(v_recoveredErrors_637_);
v___x_646_ = ((size_t)0ULL);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_644_, v___f_607_, v_sz_645_, v___x_646_, v_recoveredErrors_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 5, v___x_647_);
lean_ctor_set(v___x_639_, 4, v___y_643_);
lean_ctor_set(v___x_639_, 2, v___x_641_);
v_s_649_ = v___x_639_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_stxStack_632_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_lhsPrec_633_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_cache_635_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v___y_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 5, v___x_647_);
v_s_649_ = v_reuseFailAlloc_654_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_599_, v_s_649_);
v___x_651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = l_Lean_MessageData_ofFormat(v___x_651_);
v___x_653_ = l_Lean_throwError___redArg(v_inst_601_, v_inst_602_, v___x_652_);
return v___x_653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_env_675_, lean_object* v_p_676_, lean_object* v_ictx_677_, lean_object* v_s_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_toApplicative_681_, lean_object* v_text_682_, lean_object* v_pos_683_, lean_object* v_str_684_, lean_object* v___f_685_, lean_object* v_____do__lift_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_env_675_, v_p_676_, v_ictx_677_, v_s_678_, v_inst_679_, v_inst_680_, v_toApplicative_681_, v_text_682_, v_pos_683_, v_str_684_, v___f_685_, v_____do__lift_686_);
lean_dec_ref(v_str_684_);
lean_dec_ref(v_text_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_str_688_, uint8_t v___x_689_, lean_object* v_env_690_, lean_object* v_p_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_toApplicative_694_, lean_object* v_text_695_, lean_object* v_pos_696_, lean_object* v___f_697_, lean_object* v_toBind_698_, lean_object* v_inst_699_, lean_object* v_____do__lift_700_){
_start:
{
lean_object* v___x_701_; lean_object* v_ictx_702_; lean_object* v_s_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
v___x_701_ = lean_string_utf8_byte_size(v_str_688_);
lean_inc_ref(v_str_688_);
v_ictx_702_ = l_Lean_Parser_mkInputContext___redArg(v_str_688_, v_____do__lift_700_, v___x_689_, v___x_701_);
v_s_703_ = l_Lean_Parser_mkParserState(v_str_688_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_704_, 0, v_env_690_);
lean_closure_set(v___f_704_, 1, v_p_691_);
lean_closure_set(v___f_704_, 2, v_ictx_702_);
lean_closure_set(v___f_704_, 3, v_s_703_);
lean_closure_set(v___f_704_, 4, v_inst_692_);
lean_closure_set(v___f_704_, 5, v_inst_693_);
lean_closure_set(v___f_704_, 6, v_toApplicative_694_);
lean_closure_set(v___f_704_, 7, v_text_695_);
lean_closure_set(v___f_704_, 8, v_pos_696_);
lean_closure_set(v___f_704_, 9, v_str_688_);
lean_closure_set(v___f_704_, 10, v___f_697_);
v___x_705_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v_inst_699_, v___f_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_str_706_, lean_object* v___x_707_, lean_object* v_env_708_, lean_object* v_p_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_toApplicative_712_, lean_object* v_text_713_, lean_object* v_pos_714_, lean_object* v___f_715_, lean_object* v_toBind_716_, lean_object* v_inst_717_, lean_object* v_____do__lift_718_){
_start:
{
uint8_t v___x_1885__boxed_719_; lean_object* v_res_720_; 
v___x_1885__boxed_719_ = lean_unbox(v___x_707_);
v_res_720_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_str_706_, v___x_1885__boxed_719_, v_env_708_, v_p_709_, v_inst_710_, v_inst_711_, v_toApplicative_712_, v_text_713_, v_pos_714_, v___f_715_, v_toBind_716_, v_inst_717_, v_____do__lift_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_721_, lean_object* v_strLit_722_, lean_object* v_text_723_, uint8_t v___x_724_, lean_object* v_env_725_, lean_object* v_p_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_toApplicative_729_, lean_object* v_toBind_730_, lean_object* v_inst_731_, lean_object* v_pos_732_){
_start:
{
lean_object* v_getFileName_733_; lean_object* v_str_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v_getFileName_733_ = lean_ctor_get(v_inst_721_, 2);
lean_inc(v_getFileName_733_);
lean_dec_ref(v_inst_721_);
v_str_734_ = l_Lean_TSyntax_getString(v_strLit_722_);
lean_inc_ref(v_str_734_);
lean_inc(v_pos_732_);
lean_inc_ref(v_text_723_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_735_, 0, v_text_723_);
lean_closure_set(v___f_735_, 1, v_pos_732_);
lean_closure_set(v___f_735_, 2, v_str_734_);
v___x_736_ = lean_box(v___x_724_);
lean_inc(v_toBind_730_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 13, 12);
lean_closure_set(v___f_737_, 0, v_str_734_);
lean_closure_set(v___f_737_, 1, v___x_736_);
lean_closure_set(v___f_737_, 2, v_env_725_);
lean_closure_set(v___f_737_, 3, v_p_726_);
lean_closure_set(v___f_737_, 4, v_inst_727_);
lean_closure_set(v___f_737_, 5, v_inst_728_);
lean_closure_set(v___f_737_, 6, v_toApplicative_729_);
lean_closure_set(v___f_737_, 7, v_text_723_);
lean_closure_set(v___f_737_, 8, v_pos_732_);
lean_closure_set(v___f_737_, 9, v___f_735_);
lean_closure_set(v___f_737_, 10, v_toBind_730_);
lean_closure_set(v___f_737_, 11, v_inst_731_);
v___x_738_ = lean_apply_4(v_toBind_730_, lean_box(0), lean_box(0), v_getFileName_733_, v___f_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_739_, lean_object* v_strLit_740_, lean_object* v_text_741_, lean_object* v___x_742_, lean_object* v_env_743_, lean_object* v_p_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_toApplicative_747_, lean_object* v_toBind_748_, lean_object* v_inst_749_, lean_object* v_pos_750_){
_start:
{
uint8_t v___x_1910__boxed_751_; lean_object* v_res_752_; 
v___x_1910__boxed_751_ = lean_unbox(v___x_742_);
v_res_752_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_739_, v_strLit_740_, v_text_741_, v___x_1910__boxed_751_, v_env_743_, v_p_744_, v_inst_745_, v_inst_746_, v_toApplicative_747_, v_toBind_748_, v_inst_749_, v_pos_750_);
lean_dec(v_strLit_740_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v___f_753_, lean_object* v_pos_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_1(v___f_753_, v_pos_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v_text_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_strLit_762_, lean_object* v_toBind_763_, lean_object* v___f_764_, lean_object* v_toApplicative_765_, lean_object* v___f_766_, lean_object* v_____r_767_, lean_object* v_pos_768_){
_start:
{
lean_object* v_source_769_; uint32_t v___x_770_; uint32_t v___x_771_; uint8_t v___x_772_; 
v_source_769_ = lean_ctor_get(v_text_759_, 0);
v___x_770_ = lean_string_utf8_get(v_source_769_, v_pos_768_);
v___x_771_ = 34;
v___x_772_ = lean_uint32_dec_eq(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v___f_766_);
lean_dec_ref(v_toApplicative_765_);
v___x_773_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1);
v___x_774_ = l_Lean_throwErrorAt___redArg(v_inst_760_, v_inst_761_, v_strLit_762_, v___x_773_);
v___x_775_ = lean_apply_4(v_toBind_763_, lean_box(0), lean_box(0), v___x_774_, v___f_764_);
return v___x_775_;
}
else
{
lean_object* v_toPure_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v___f_764_);
lean_dec(v_strLit_762_);
lean_dec_ref(v_inst_761_);
lean_dec_ref(v_inst_760_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_765_);
v___x_777_ = lean_string_utf8_next(v_source_769_, v_pos_768_);
v___x_778_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_777_);
v___x_779_ = lean_apply_4(v_toBind_763_, lean_box(0), lean_box(0), v___x_778_, v___f_766_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object* v_text_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_strLit_783_, lean_object* v_toBind_784_, lean_object* v___f_785_, lean_object* v_toApplicative_786_, lean_object* v___f_787_, lean_object* v_____r_788_, lean_object* v_pos_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(v_text_780_, v_inst_781_, v_inst_782_, v_strLit_783_, v_toBind_784_, v___f_785_, v_toApplicative_786_, v___f_787_, v_____r_788_, v_pos_789_);
lean_dec(v_pos_789_);
lean_dec_ref(v_text_780_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_791_, lean_object* v_____s_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_apply_2(v___f_791_, v___x_793_, v_____s_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_toPure_795_, lean_object* v_____do__lift_796_){
_start:
{
if (lean_obj_tag(v_____do__lift_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_a_797_ = lean_ctor_get(v_____do__lift_796_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_____do__lift_796_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v_____do__lift_796_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v_____do__lift_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 1);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; 
v___x_803_ = lean_apply_2(v_toPure_795_, lean_box(0), v___x_802_);
return v___x_803_;
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_a_806_ = lean_ctor_get(v_____do__lift_796_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_____do__lift_796_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v_____do__lift_796_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v_____do__lift_796_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_apply_2(v_toPure_795_, lean_box(0), v___x_811_);
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_815_, lean_object* v_toPure_816_, lean_object* v_toBind_817_, lean_object* v___f_818_, lean_object* v_b_819_){
_start:
{
uint32_t v___x_820_; uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_string_utf8_get(v_source_815_, v_b_819_);
v___x_821_ = 35;
v___x_822_ = lean_uint32_dec_eq(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v_b_819_);
v___x_824_ = lean_apply_2(v_toPure_816_, lean_box(0), v___x_823_);
v___x_825_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v___x_824_, v___f_818_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_string_utf8_next(v_source_815_, v_b_819_);
lean_dec(v_b_819_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_apply_2(v_toPure_816_, lean_box(0), v___x_827_);
v___x_829_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v___x_828_, v___f_818_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_830_, lean_object* v_toPure_831_, lean_object* v_toBind_832_, lean_object* v___f_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_830_, v_toPure_831_, v_toBind_832_, v___f_833_, v_b_834_);
lean_dec_ref(v_source_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_836_, lean_object* v___f_837_, lean_object* v_toApplicative_838_, lean_object* v_toBind_839_, lean_object* v_inst_840_, lean_object* v___f_841_, lean_object* v_____x_842_){
_start:
{
lean_object* v_start_843_; lean_object* v_source_844_; uint32_t v___x_845_; uint32_t v___x_846_; uint8_t v___x_847_; 
v_start_843_ = lean_ctor_get(v_____x_842_, 0);
lean_inc(v_start_843_);
lean_dec_ref(v_____x_842_);
v_source_844_ = lean_ctor_get(v_text_836_, 0);
lean_inc_ref(v_source_844_);
lean_dec_ref(v_text_836_);
v___x_845_ = lean_string_utf8_get(v_source_844_, v_start_843_);
v___x_846_ = 114;
v___x_847_ = lean_uint32_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_source_844_);
lean_dec(v___f_841_);
lean_dec_ref(v_inst_840_);
lean_dec(v_toBind_839_);
lean_dec_ref(v_toApplicative_838_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_apply_2(v___f_837_, v___x_848_, v_start_843_);
return v___x_849_;
}
else
{
lean_object* v_toPure_850_; lean_object* v_pos_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v___f_837_);
v_toPure_850_ = lean_ctor_get(v_toApplicative_838_, 1);
lean_inc_n(v_toPure_850_, 2);
lean_dec_ref(v_toApplicative_838_);
v_pos_851_ = lean_string_utf8_next(v_source_844_, v_start_843_);
lean_dec(v_start_843_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7), 2, 1);
lean_closure_set(v___f_852_, 0, v_toPure_850_);
lean_inc(v_toBind_839_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_853_, 0, v_source_844_);
lean_closure_set(v___f_853_, 1, v_toPure_850_);
lean_closure_set(v___f_853_, 2, v_toBind_839_);
lean_closure_set(v___f_853_, 3, v___f_852_);
v___x_854_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_840_, v___f_853_, v_pos_851_);
v___x_855_ = lean_apply_4(v_toBind_839_, lean_box(0), lean_box(0), v___x_854_, v___f_841_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_856_, lean_object* v_strLit_857_, lean_object* v_text_858_, uint8_t v___x_859_, lean_object* v_p_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_toApplicative_863_, lean_object* v_toBind_864_, lean_object* v_inst_865_, lean_object* v_env_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_867_ = lean_box(v___x_859_);
lean_inc_n(v_toBind_864_, 3);
lean_inc_ref_n(v_toApplicative_863_, 2);
lean_inc_ref(v_inst_862_);
lean_inc_ref_n(v_inst_861_, 3);
lean_inc_ref_n(v_text_858_, 2);
lean_inc_n(v_strLit_857_, 2);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_868_, 0, v_inst_856_);
lean_closure_set(v___f_868_, 1, v_strLit_857_);
lean_closure_set(v___f_868_, 2, v_text_858_);
lean_closure_set(v___f_868_, 3, v___x_867_);
lean_closure_set(v___f_868_, 4, v_env_866_);
lean_closure_set(v___f_868_, 5, v_p_860_);
lean_closure_set(v___f_868_, 6, v_inst_861_);
lean_closure_set(v___f_868_, 7, v_inst_862_);
lean_closure_set(v___f_868_, 8, v_toApplicative_863_);
lean_closure_set(v___f_868_, 9, v_toBind_864_);
lean_closure_set(v___f_868_, 10, v_inst_865_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4), 2, 1);
lean_closure_set(v___f_869_, 0, v___f_868_);
lean_inc_ref(v___f_869_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_870_, 0, v_text_858_);
lean_closure_set(v___f_870_, 1, v_inst_861_);
lean_closure_set(v___f_870_, 2, v_inst_862_);
lean_closure_set(v___f_870_, 3, v_strLit_857_);
lean_closure_set(v___f_870_, 4, v_toBind_864_);
lean_closure_set(v___f_870_, 5, v___f_869_);
lean_closure_set(v___f_870_, 6, v_toApplicative_863_);
lean_closure_set(v___f_870_, 7, v___f_869_);
lean_inc_ref(v___f_870_);
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_871_, 0, v___f_870_);
v___f_872_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 7, 6);
lean_closure_set(v___f_872_, 0, v_text_858_);
lean_closure_set(v___f_872_, 1, v___f_870_);
lean_closure_set(v___f_872_, 2, v_toApplicative_863_);
lean_closure_set(v___f_872_, 3, v_toBind_864_);
lean_closure_set(v___f_872_, 4, v_inst_861_);
lean_closure_set(v___f_872_, 5, v___f_871_);
v___x_873_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_861_, v_strLit_857_);
lean_dec(v_strLit_857_);
v___x_874_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v___x_873_, v___f_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_875_, lean_object* v_strLit_876_, lean_object* v_text_877_, lean_object* v___x_878_, lean_object* v_p_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_toApplicative_882_, lean_object* v_toBind_883_, lean_object* v_inst_884_, lean_object* v_env_885_){
_start:
{
uint8_t v___x_2076__boxed_886_; lean_object* v_res_887_; 
v___x_2076__boxed_886_ = lean_unbox(v___x_878_);
v_res_887_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_875_, v_strLit_876_, v_text_877_, v___x_2076__boxed_886_, v_p_879_, v_inst_880_, v_inst_881_, v_toApplicative_882_, v_toBind_883_, v_inst_884_, v_env_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_strLit_890_, uint8_t v___x_891_, lean_object* v_p_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_toApplicative_895_, lean_object* v_toBind_896_, lean_object* v_inst_897_, lean_object* v_text_898_){
_start:
{
lean_object* v_getEnv_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v_getEnv_899_ = lean_ctor_get(v_inst_888_, 0);
lean_inc(v_getEnv_899_);
lean_dec_ref(v_inst_888_);
v___x_900_ = lean_box(v___x_891_);
lean_inc(v_toBind_896_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_901_, 0, v_inst_889_);
lean_closure_set(v___f_901_, 1, v_strLit_890_);
lean_closure_set(v___f_901_, 2, v_text_898_);
lean_closure_set(v___f_901_, 3, v___x_900_);
lean_closure_set(v___f_901_, 4, v_p_892_);
lean_closure_set(v___f_901_, 5, v_inst_893_);
lean_closure_set(v___f_901_, 6, v_inst_894_);
lean_closure_set(v___f_901_, 7, v_toApplicative_895_);
lean_closure_set(v___f_901_, 8, v_toBind_896_);
lean_closure_set(v___f_901_, 9, v_inst_897_);
v___x_902_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v_getEnv_899_, v___f_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_strLit_905_, lean_object* v___x_906_, lean_object* v_p_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_toApplicative_910_, lean_object* v_toBind_911_, lean_object* v_inst_912_, lean_object* v_text_913_){
_start:
{
uint8_t v___x_2108__boxed_914_; lean_object* v_res_915_; 
v___x_2108__boxed_914_ = lean_unbox(v___x_906_);
v_res_915_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_903_, v_inst_904_, v_strLit_905_, v___x_2108__boxed_914_, v_p_907_, v_inst_908_, v_inst_909_, v_toApplicative_910_, v_toBind_911_, v_inst_912_, v_text_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_p_922_, lean_object* v_strLit_923_){
_start:
{
uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_924_ = 1;
v___x_925_ = l_Lean_Syntax_getPos_x3f(v_strLit_923_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_inst_917_);
v___x_926_ = l_Lean_TSyntax_getString(v_strLit_923_);
lean_dec(v_strLit_923_);
v___x_927_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_916_, v_inst_918_, v_inst_919_, v_inst_920_, v_inst_921_, v_p_922_, v___x_926_);
return v___x_927_;
}
else
{
lean_object* v_toApplicative_928_; lean_object* v_toBind_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; 
lean_dec_ref_known(v___x_925_, 1);
v_toApplicative_928_ = lean_ctor_get(v_inst_916_, 0);
lean_inc_ref(v_toApplicative_928_);
v_toBind_929_ = lean_ctor_get(v_inst_916_, 1);
lean_inc_n(v_toBind_929_, 2);
v___x_930_ = lean_box(v___x_924_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 11, 10);
lean_closure_set(v___f_931_, 0, v_inst_918_);
lean_closure_set(v___f_931_, 1, v_inst_920_);
lean_closure_set(v___f_931_, 2, v_strLit_923_);
lean_closure_set(v___f_931_, 3, v___x_930_);
lean_closure_set(v___f_931_, 4, v_p_922_);
lean_closure_set(v___f_931_, 5, v_inst_916_);
lean_closure_set(v___f_931_, 6, v_inst_919_);
lean_closure_set(v___f_931_, 7, v_toApplicative_928_);
lean_closure_set(v___f_931_, 8, v_toBind_929_);
lean_closure_set(v___f_931_, 9, v_inst_921_);
v___x_932_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v_inst_917_, v___f_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_p_940_, lean_object* v_strLit_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_934_, v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_inst_939_, v_p_940_, v_strLit_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object* v_toApplicative_943_, lean_object* v_st_944_, uint8_t v_err_945_){
_start:
{
lean_object* v_toPure_946_; lean_object* v_stxStack_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_toPure_946_ = lean_ctor_get(v_toApplicative_943_, 1);
lean_inc(v_toPure_946_);
lean_dec_ref(v_toApplicative_943_);
v_stxStack_947_ = lean_ctor_get(v_st_944_, 0);
v___x_948_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_947_);
v___x_949_ = lean_box(v_err_945_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_apply_2(v_toPure_946_, lean_box(0), v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_952_, lean_object* v_st_953_, lean_object* v_err_954_){
_start:
{
uint8_t v_err_boxed_955_; lean_object* v_res_956_; 
v_err_boxed_955_ = lean_unbox(v_err_954_);
v_res_956_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_toApplicative_952_, v_st_953_, v_err_boxed_955_);
lean_dec_ref(v_st_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object* v___f_957_, uint8_t v_err_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_box(v_err_958_);
v___x_960_ = lean_apply_1(v___f_957_, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object* v___f_961_, lean_object* v_err_962_){
_start:
{
uint8_t v_err_boxed_963_; lean_object* v_res_964_; 
v_err_boxed_963_ = lean_unbox(v_err_962_);
v_res_964_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_961_, v_err_boxed_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object* v_toApplicative_965_, uint8_t v___x_966_, lean_object* v_toBind_967_, lean_object* v___f_968_, lean_object* v_____r_969_){
_start:
{
lean_object* v_toPure_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_toPure_970_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_970_);
lean_dec_ref(v_toApplicative_965_);
v___x_971_ = lean_box(v___x_966_);
v___x_972_ = lean_apply_2(v_toPure_970_, lean_box(0), v___x_971_);
v___x_973_ = lean_apply_4(v_toBind_967_, lean_box(0), lean_box(0), v___x_972_, v___f_968_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_974_, lean_object* v___x_975_, lean_object* v_toBind_976_, lean_object* v___f_977_, lean_object* v_____r_978_){
_start:
{
uint8_t v___x_1581__boxed_979_; lean_object* v_res_980_; 
v___x_1581__boxed_979_ = lean_unbox(v___x_975_);
v_res_980_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(v_toApplicative_974_, v___x_1581__boxed_979_, v_toBind_976_, v___f_977_, v_____r_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object* v_env_981_, lean_object* v_contents_982_, lean_object* v_p_983_, lean_object* v_ictx_984_, lean_object* v_toApplicative_985_, lean_object* v_toBind_986_, uint8_t v___x_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_____do__lift_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_st_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; uint8_t v___x_1004_; 
v___x_993_ = lean_box(0);
v___x_994_ = lean_box(0);
lean_inc_ref(v_env_981_);
v___x_995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_995_, 0, v_env_981_);
lean_ctor_set(v___x_995_, 1, v_____do__lift_992_);
lean_ctor_set(v___x_995_, 2, v___x_993_);
lean_ctor_set(v___x_995_, 3, v___x_994_);
v___x_996_ = l_Lean_Parser_getTokenTable(v_env_981_);
v___x_997_ = l_Lean_Parser_mkParserState(v_contents_982_);
lean_inc_ref(v_ictx_984_);
v_st_998_ = l_Lean_Parser_ParserFn_run(v_p_983_, v_ictx_984_, v___x_995_, v___x_996_, v___x_997_);
lean_inc_ref_n(v_st_998_, 2);
lean_inc_ref(v_toApplicative_985_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_999_, 0, v_toApplicative_985_);
lean_closure_set(v___f_999_, 1, v_st_998_);
v___x_1000_ = l_Lean_Parser_ParserState_allErrors(v_st_998_);
v___x_1001_ = lean_array_get_size(v___x_1000_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_nat_dec_eq(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_bool_not(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v_pos_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; 
v_pos_1005_ = lean_ctor_get(v_st_998_, 2);
lean_inc(v_pos_1005_);
v___x_1006_ = l_Lean_Parser_InputContext_atEnd(v_ictx_984_, v_pos_1005_);
lean_dec(v_pos_1005_);
v___x_1007_ = lean_bool_not(v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v_toPure_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v_st_998_);
lean_dec(v_inst_991_);
lean_dec(v_inst_990_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
lean_dec_ref(v_ictx_984_);
v_toPure_1008_ = lean_ctor_get(v_toApplicative_985_, 1);
lean_inc(v_toPure_1008_);
lean_dec_ref(v_toApplicative_985_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1009_, 0, v___f_999_);
v___x_1010_ = lean_box(v___x_1007_);
v___x_1011_ = lean_apply_2(v_toPure_1008_, lean_box(0), v___x_1010_);
v___x_1012_ = lean_apply_4(v_toBind_986_, lean_box(0), lean_box(0), v___x_1011_, v___f_1009_);
return v___x_1012_;
}
else
{
lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1013_, 0, v___f_999_);
v___x_1014_ = lean_box(v___x_987_);
lean_inc(v_toBind_986_);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_1015_, 0, v_toApplicative_985_);
lean_closure_set(v___f_1015_, 1, v___x_1014_);
lean_closure_set(v___f_1015_, 2, v_toBind_986_);
lean_closure_set(v___f_1015_, 3, v___f_1013_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1017_ = l_Lean_Parser_ParserState_mkError(v_st_998_, v___x_1016_);
v___x_1018_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_984_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_ofFormat(v___x_1019_);
v___x_1021_ = l_Lean_logError___redArg(v_inst_988_, v_inst_989_, v_inst_990_, v_inst_991_, v___x_1020_);
v___x_1022_ = lean_apply_4(v_toBind_986_, lean_box(0), lean_box(0), v___x_1021_, v___f_1015_);
return v___x_1022_;
}
}
else
{
lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1023_, 0, v___f_999_);
v___x_1024_ = lean_box(v___x_987_);
lean_inc(v_toBind_986_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_1025_, 0, v_toApplicative_985_);
lean_closure_set(v___f_1025_, 1, v___x_1024_);
lean_closure_set(v___f_1025_, 2, v_toBind_986_);
lean_closure_set(v___f_1025_, 3, v___f_1023_);
v___x_1026_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_984_, v_st_998_);
v___x_1027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
v___x_1028_ = l_Lean_MessageData_ofFormat(v___x_1027_);
v___x_1029_ = l_Lean_logError___redArg(v_inst_988_, v_inst_989_, v_inst_990_, v_inst_991_, v___x_1028_);
v___x_1030_ = lean_apply_4(v_toBind_986_, lean_box(0), lean_box(0), v___x_1029_, v___f_1025_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object* v_env_1031_, lean_object* v_contents_1032_, lean_object* v_p_1033_, lean_object* v_ictx_1034_, lean_object* v_toApplicative_1035_, lean_object* v_toBind_1036_, lean_object* v___x_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_____do__lift_1042_){
_start:
{
uint8_t v___x_1597__boxed_1043_; lean_object* v_res_1044_; 
v___x_1597__boxed_1043_ = lean_unbox(v___x_1037_);
v_res_1044_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__5(v_env_1031_, v_contents_1032_, v_p_1033_, v_ictx_1034_, v_toApplicative_1035_, v_toBind_1036_, v___x_1597__boxed_1043_, v_inst_1038_, v_inst_1039_, v_inst_1040_, v_inst_1041_, v_____do__lift_1042_);
lean_dec_ref(v_contents_1032_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object* v_contents_1045_, uint8_t v___x_1046_, lean_object* v_env_1047_, lean_object* v_p_1048_, lean_object* v_toApplicative_1049_, lean_object* v_toBind_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_____do__lift_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v_ictx_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v___x_1056_ = lean_string_utf8_byte_size(v_contents_1045_);
lean_inc_ref(v_contents_1045_);
v_ictx_1057_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1045_, v_____do__lift_1055_, v___x_1046_, v___x_1056_);
v___x_1058_ = lean_box(v___x_1046_);
lean_inc(v_inst_1054_);
lean_inc(v_toBind_1050_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_1059_, 0, v_env_1047_);
lean_closure_set(v___f_1059_, 1, v_contents_1045_);
lean_closure_set(v___f_1059_, 2, v_p_1048_);
lean_closure_set(v___f_1059_, 3, v_ictx_1057_);
lean_closure_set(v___f_1059_, 4, v_toApplicative_1049_);
lean_closure_set(v___f_1059_, 5, v_toBind_1050_);
lean_closure_set(v___f_1059_, 6, v___x_1058_);
lean_closure_set(v___f_1059_, 7, v_inst_1051_);
lean_closure_set(v___f_1059_, 8, v_inst_1052_);
lean_closure_set(v___f_1059_, 9, v_inst_1053_);
lean_closure_set(v___f_1059_, 10, v_inst_1054_);
v___x_1060_ = lean_apply_4(v_toBind_1050_, lean_box(0), lean_box(0), v_inst_1054_, v___f_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object* v_contents_1061_, lean_object* v___x_1062_, lean_object* v_env_1063_, lean_object* v_p_1064_, lean_object* v_toApplicative_1065_, lean_object* v_toBind_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_____do__lift_1071_){
_start:
{
uint8_t v___x_1685__boxed_1072_; lean_object* v_res_1073_; 
v___x_1685__boxed_1072_ = lean_unbox(v___x_1062_);
v_res_1073_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(v_contents_1061_, v___x_1685__boxed_1072_, v_env_1063_, v_p_1064_, v_toApplicative_1065_, v_toBind_1066_, v_inst_1067_, v_inst_1068_, v_inst_1069_, v_inst_1070_, v_____do__lift_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object* v_inst_1074_, lean_object* v_contents_1075_, uint8_t v___x_1076_, lean_object* v_p_1077_, lean_object* v_toApplicative_1078_, lean_object* v_toBind_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_env_1083_){
_start:
{
lean_object* v_getFileName_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; 
v_getFileName_1084_ = lean_ctor_get(v_inst_1074_, 2);
lean_inc(v_getFileName_1084_);
v___x_1085_ = lean_box(v___x_1076_);
lean_inc(v_toBind_1079_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1086_, 0, v_contents_1075_);
lean_closure_set(v___f_1086_, 1, v___x_1085_);
lean_closure_set(v___f_1086_, 2, v_env_1083_);
lean_closure_set(v___f_1086_, 3, v_p_1077_);
lean_closure_set(v___f_1086_, 4, v_toApplicative_1078_);
lean_closure_set(v___f_1086_, 5, v_toBind_1079_);
lean_closure_set(v___f_1086_, 6, v_inst_1080_);
lean_closure_set(v___f_1086_, 7, v_inst_1074_);
lean_closure_set(v___f_1086_, 8, v_inst_1081_);
lean_closure_set(v___f_1086_, 9, v_inst_1082_);
v___x_1087_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v_getFileName_1084_, v___f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object* v_inst_1088_, lean_object* v_contents_1089_, lean_object* v___x_1090_, lean_object* v_p_1091_, lean_object* v_toApplicative_1092_, lean_object* v_toBind_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_env_1097_){
_start:
{
uint8_t v___x_1712__boxed_1098_; lean_object* v_res_1099_; 
v___x_1712__boxed_1098_ = lean_unbox(v___x_1090_);
v_res_1099_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__4(v_inst_1088_, v_contents_1089_, v___x_1712__boxed_1098_, v_p_1091_, v_toApplicative_1092_, v_toBind_1093_, v_inst_1094_, v_inst_1095_, v_inst_1096_, v_env_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object* v_toApplicative_1100_, lean_object* v_s_1101_, uint8_t v_err_1102_){
_start:
{
lean_object* v_toPure_1103_; lean_object* v_stxStack_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_toPure_1103_ = lean_ctor_get(v_toApplicative_1100_, 1);
lean_inc(v_toPure_1103_);
lean_dec_ref(v_toApplicative_1100_);
v_stxStack_1104_ = lean_ctor_get(v_s_1101_, 0);
v___x_1105_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1104_);
v___x_1106_ = lean_box(v_err_1102_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_apply_2(v_toPure_1103_, lean_box(0), v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object* v_toApplicative_1109_, lean_object* v_s_1110_, lean_object* v_err_1111_){
_start:
{
uint8_t v_err_boxed_1112_; lean_object* v_res_1113_; 
v_err_boxed_1112_ = lean_unbox(v_err_1111_);
v_res_1113_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(v_toApplicative_1109_, v_s_1110_, v_err_boxed_1112_);
lean_dec_ref(v_s_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12(lean_object* v_env_1114_, lean_object* v_p_1115_, lean_object* v_ictx_1116_, lean_object* v_s_1117_, lean_object* v_toApplicative_1118_, lean_object* v_toBind_1119_, uint8_t v___x_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_____do__lift_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_s_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_box(0);
lean_inc_ref(v_env_1114_);
v___x_1128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1128_, 0, v_env_1114_);
lean_ctor_set(v___x_1128_, 1, v_____do__lift_1125_);
lean_ctor_set(v___x_1128_, 2, v___x_1126_);
lean_ctor_set(v___x_1128_, 3, v___x_1127_);
v___x_1129_ = l_Lean_Parser_getTokenTable(v_env_1114_);
lean_inc_ref(v_ictx_1116_);
v_s_1130_ = l_Lean_Parser_ParserFn_run(v_p_1115_, v_ictx_1116_, v___x_1128_, v___x_1129_, v_s_1117_);
lean_inc_ref_n(v_s_1130_, 2);
lean_inc_ref(v_toApplicative_1118_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1131_, 0, v_toApplicative_1118_);
lean_closure_set(v___f_1131_, 1, v_s_1130_);
v___x_1132_ = l_Lean_Parser_ParserState_allErrors(v_s_1130_);
v___x_1133_ = lean_array_get_size(v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_nat_dec_eq(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_bool_not(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v_pos_1137_; uint8_t v___x_1138_; uint8_t v___x_1139_; 
v_pos_1137_ = lean_ctor_get(v_s_1130_, 2);
lean_inc(v_pos_1137_);
v___x_1138_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1116_, v_pos_1137_);
lean_dec(v_pos_1137_);
v___x_1139_ = lean_bool_not(v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v_toPure_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v_s_1130_);
lean_dec(v_inst_1124_);
lean_dec(v_inst_1123_);
lean_dec_ref(v_inst_1122_);
lean_dec_ref(v_inst_1121_);
lean_dec_ref(v_ictx_1116_);
v_toPure_1140_ = lean_ctor_get(v_toApplicative_1118_, 1);
lean_inc(v_toPure_1140_);
lean_dec_ref(v_toApplicative_1118_);
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1141_, 0, v___f_1131_);
v___x_1142_ = lean_box(v___x_1139_);
v___x_1143_ = lean_apply_2(v_toPure_1140_, lean_box(0), v___x_1142_);
v___x_1144_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1143_, v___f_1141_);
return v___x_1144_;
}
else
{
lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1145_, 0, v___f_1131_);
v___x_1146_ = lean_box(v___x_1120_);
lean_inc(v_toBind_1119_);
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_1147_, 0, v_toApplicative_1118_);
lean_closure_set(v___f_1147_, 1, v___x_1146_);
lean_closure_set(v___f_1147_, 2, v_toBind_1119_);
lean_closure_set(v___f_1147_, 3, v___f_1145_);
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1149_ = l_Lean_Parser_ParserState_mkError(v_s_1130_, v___x_1148_);
v___x_1150_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1116_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_ofFormat(v___x_1151_);
v___x_1153_ = l_Lean_logError___redArg(v_inst_1121_, v_inst_1122_, v_inst_1123_, v_inst_1124_, v___x_1152_);
v___x_1154_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1153_, v___f_1147_);
return v___x_1154_;
}
}
else
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1155_, 0, v___f_1131_);
v___x_1156_ = lean_box(v___x_1120_);
lean_inc(v_toBind_1119_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_1157_, 0, v_toApplicative_1118_);
lean_closure_set(v___f_1157_, 1, v___x_1156_);
lean_closure_set(v___f_1157_, 2, v_toBind_1119_);
lean_closure_set(v___f_1157_, 3, v___f_1155_);
v___x_1158_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1116_, v_s_1130_);
v___x_1159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofFormat(v___x_1159_);
v___x_1161_ = l_Lean_logError___redArg(v_inst_1121_, v_inst_1122_, v_inst_1123_, v_inst_1124_, v___x_1160_);
v___x_1162_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1161_, v___f_1157_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed(lean_object* v_env_1163_, lean_object* v_p_1164_, lean_object* v_ictx_1165_, lean_object* v_s_1166_, lean_object* v_toApplicative_1167_, lean_object* v_toBind_1168_, lean_object* v___x_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_____do__lift_1174_){
_start:
{
uint8_t v___x_1741__boxed_1175_; lean_object* v_res_1176_; 
v___x_1741__boxed_1175_ = lean_unbox(v___x_1169_);
v_res_1176_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__12(v_env_1163_, v_p_1164_, v_ictx_1165_, v_s_1166_, v_toApplicative_1167_, v_toBind_1168_, v___x_1741__boxed_1175_, v_inst_1170_, v_inst_1171_, v_inst_1172_, v_inst_1173_, v_____do__lift_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object* v_source_1177_, uint8_t v___x_1178_, lean_object* v___y_1179_, lean_object* v_env_1180_, lean_object* v_p_1181_, lean_object* v_toApplicative_1182_, lean_object* v_toBind_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v_____do__lift_1190_){
_start:
{
lean_object* v_ictx_1191_; lean_object* v___x_1192_; lean_object* v___y_1194_; 
lean_inc_ref(v_source_1177_);
v_ictx_1191_ = l_Lean_Parser_mkInputContext___redArg(v_source_1177_, v_____do__lift_1190_, v___x_1178_, v___y_1179_);
v___x_1192_ = l_Lean_Parser_mkParserState(v_source_1177_);
lean_dec_ref(v_source_1177_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1200_ = l_panic___redArg(v___x_1189_, v___x_1199_);
v___y_1194_ = v___x_1200_;
goto v___jp_1193_;
}
else
{
lean_object* v_val_1201_; 
v_val_1201_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v___x_1188_, 1);
v___y_1194_ = v_val_1201_;
goto v___jp_1193_;
}
v___jp_1193_:
{
lean_object* v_s_1195_; lean_object* v___x_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_s_1195_ = l_Lean_Parser_ParserState_setPos(v___x_1192_, v___y_1194_);
v___x_1196_ = lean_box(v___x_1178_);
lean_inc(v_inst_1187_);
lean_inc(v_toBind_1183_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed), 12, 11);
lean_closure_set(v___f_1197_, 0, v_env_1180_);
lean_closure_set(v___f_1197_, 1, v_p_1181_);
lean_closure_set(v___f_1197_, 2, v_ictx_1191_);
lean_closure_set(v___f_1197_, 3, v_s_1195_);
lean_closure_set(v___f_1197_, 4, v_toApplicative_1182_);
lean_closure_set(v___f_1197_, 5, v_toBind_1183_);
lean_closure_set(v___f_1197_, 6, v___x_1196_);
lean_closure_set(v___f_1197_, 7, v_inst_1184_);
lean_closure_set(v___f_1197_, 8, v_inst_1185_);
lean_closure_set(v___f_1197_, 9, v_inst_1186_);
lean_closure_set(v___f_1197_, 10, v_inst_1187_);
v___x_1198_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v_inst_1187_, v___f_1197_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object* v_source_1202_, lean_object* v___x_1203_, lean_object* v___y_1204_, lean_object* v_env_1205_, lean_object* v_p_1206_, lean_object* v_toApplicative_1207_, lean_object* v_toBind_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v_____do__lift_1215_){
_start:
{
uint8_t v___x_1836__boxed_1216_; lean_object* v_res_1217_; 
v___x_1836__boxed_1216_ = lean_unbox(v___x_1203_);
v_res_1217_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__7(v_source_1202_, v___x_1836__boxed_1216_, v___y_1204_, v_env_1205_, v_p_1206_, v_toApplicative_1207_, v_toBind_1208_, v_inst_1209_, v_inst_1210_, v_inst_1211_, v_inst_1212_, v___x_1213_, v___x_1214_, v_____do__lift_1215_);
lean_dec(v___x_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object* v_text_1218_, lean_object* v_inst_1219_, uint8_t v___x_1220_, lean_object* v_p_1221_, lean_object* v_toApplicative_1222_, lean_object* v_toBind_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v___x_1227_, lean_object* v_s_1228_, lean_object* v_env_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1239_; lean_object* v___x_1243_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Lean_Syntax_getTailPos_x3f(v_s_1228_, v___x_1220_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1245_ = l_panic___redArg(v___x_1230_, v___x_1244_);
v___y_1239_ = v___x_1245_;
goto v___jp_1238_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1243_, 1);
v___y_1239_ = v_val_1246_;
goto v___jp_1238_;
}
v___jp_1231_:
{
lean_object* v_getFileName_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; 
v_getFileName_1234_ = lean_ctor_get(v_inst_1219_, 2);
lean_inc(v_getFileName_1234_);
v___x_1235_ = lean_box(v___x_1220_);
lean_inc(v_toBind_1223_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1236_, 0, v___y_1232_);
lean_closure_set(v___f_1236_, 1, v___x_1235_);
lean_closure_set(v___f_1236_, 2, v___y_1233_);
lean_closure_set(v___f_1236_, 3, v_env_1229_);
lean_closure_set(v___f_1236_, 4, v_p_1221_);
lean_closure_set(v___f_1236_, 5, v_toApplicative_1222_);
lean_closure_set(v___f_1236_, 6, v_toBind_1223_);
lean_closure_set(v___f_1236_, 7, v_inst_1224_);
lean_closure_set(v___f_1236_, 8, v_inst_1219_);
lean_closure_set(v___f_1236_, 9, v_inst_1225_);
lean_closure_set(v___f_1236_, 10, v_inst_1226_);
lean_closure_set(v___f_1236_, 11, v___x_1227_);
lean_closure_set(v___f_1236_, 12, v___x_1230_);
v___x_1237_ = lean_apply_4(v_toBind_1223_, lean_box(0), lean_box(0), v_getFileName_1234_, v___f_1236_);
return v___x_1237_;
}
v___jp_1238_:
{
lean_object* v_source_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_source_1240_ = lean_ctor_get(v_text_1218_, 0);
lean_inc_ref(v_source_1240_);
lean_dec_ref(v_text_1218_);
v___x_1241_ = lean_string_utf8_byte_size(v_source_1240_);
v___x_1242_ = lean_nat_dec_le(v___y_1239_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v___y_1239_);
v___y_1232_ = v_source_1240_;
v___y_1233_ = v___x_1241_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v_source_1240_;
v___y_1233_ = v___y_1239_;
goto v___jp_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object* v_text_1247_, lean_object* v_inst_1248_, lean_object* v___x_1249_, lean_object* v_p_1250_, lean_object* v_toApplicative_1251_, lean_object* v_toBind_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v___x_1256_, lean_object* v_s_1257_, lean_object* v_env_1258_){
_start:
{
uint8_t v___x_1897__boxed_1259_; lean_object* v_res_1260_; 
v___x_1897__boxed_1259_ = lean_unbox(v___x_1249_);
v_res_1260_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__8(v_text_1247_, v_inst_1248_, v___x_1897__boxed_1259_, v_p_1250_, v_toApplicative_1251_, v_toBind_1252_, v_inst_1253_, v_inst_1254_, v_inst_1255_, v___x_1256_, v_s_1257_, v_env_1258_);
lean_dec(v_s_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object* v_inst_1261_, lean_object* v_inst_1262_, uint8_t v___x_1263_, lean_object* v_p_1264_, lean_object* v_toApplicative_1265_, lean_object* v_toBind_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v___x_1270_, lean_object* v_s_1271_, lean_object* v_text_1272_){
_start:
{
lean_object* v_getEnv_1273_; lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; 
v_getEnv_1273_ = lean_ctor_get(v_inst_1261_, 0);
lean_inc(v_getEnv_1273_);
lean_dec_ref(v_inst_1261_);
v___x_1274_ = lean_box(v___x_1263_);
lean_inc(v_toBind_1266_);
v___f_1275_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed), 12, 11);
lean_closure_set(v___f_1275_, 0, v_text_1272_);
lean_closure_set(v___f_1275_, 1, v_inst_1262_);
lean_closure_set(v___f_1275_, 2, v___x_1274_);
lean_closure_set(v___f_1275_, 3, v_p_1264_);
lean_closure_set(v___f_1275_, 4, v_toApplicative_1265_);
lean_closure_set(v___f_1275_, 5, v_toBind_1266_);
lean_closure_set(v___f_1275_, 6, v_inst_1267_);
lean_closure_set(v___f_1275_, 7, v_inst_1268_);
lean_closure_set(v___f_1275_, 8, v_inst_1269_);
lean_closure_set(v___f_1275_, 9, v___x_1270_);
lean_closure_set(v___f_1275_, 10, v_s_1271_);
v___x_1276_ = lean_apply_4(v_toBind_1266_, lean_box(0), lean_box(0), v_getEnv_1273_, v___f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v___x_1279_, lean_object* v_p_1280_, lean_object* v_toApplicative_1281_, lean_object* v_toBind_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v___x_1286_, lean_object* v_s_1287_, lean_object* v_text_1288_){
_start:
{
uint8_t v___x_1951__boxed_1289_; lean_object* v_res_1290_; 
v___x_1951__boxed_1289_ = lean_unbox(v___x_1279_);
v_res_1290_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__9(v_inst_1277_, v_inst_1278_, v___x_1951__boxed_1289_, v_p_1280_, v_toApplicative_1281_, v_toBind_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v___x_1286_, v_s_1287_, v_text_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_p_1297_, lean_object* v_s_1298_){
_start:
{
uint8_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = 1;
v___x_1300_ = l_Lean_Syntax_getPos_x3f(v_s_1298_, v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_toApplicative_1301_; lean_object* v_toBind_1302_; lean_object* v_getEnv_1303_; lean_object* v_contents_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; 
lean_dec(v_inst_1292_);
v_toApplicative_1301_ = lean_ctor_get(v_inst_1291_, 0);
lean_inc_ref(v_toApplicative_1301_);
v_toBind_1302_ = lean_ctor_get(v_inst_1291_, 1);
lean_inc_n(v_toBind_1302_, 2);
v_getEnv_1303_ = lean_ctor_get(v_inst_1293_, 0);
lean_inc(v_getEnv_1303_);
lean_dec_ref(v_inst_1293_);
v_contents_1304_ = l_Lean_TSyntax_getString(v_s_1298_);
lean_dec(v_s_1298_);
v___x_1305_ = lean_box(v___x_1299_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1306_, 0, v_inst_1295_);
lean_closure_set(v___f_1306_, 1, v_contents_1304_);
lean_closure_set(v___f_1306_, 2, v___x_1305_);
lean_closure_set(v___f_1306_, 3, v_p_1297_);
lean_closure_set(v___f_1306_, 4, v_toApplicative_1301_);
lean_closure_set(v___f_1306_, 5, v_toBind_1302_);
lean_closure_set(v___f_1306_, 6, v_inst_1291_);
lean_closure_set(v___f_1306_, 7, v_inst_1294_);
lean_closure_set(v___f_1306_, 8, v_inst_1296_);
v___x_1307_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v_getEnv_1303_, v___f_1306_);
return v___x_1307_;
}
else
{
lean_object* v_toApplicative_1308_; lean_object* v_toBind_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; 
v_toApplicative_1308_ = lean_ctor_get(v_inst_1291_, 0);
lean_inc_ref(v_toApplicative_1308_);
v_toBind_1309_ = lean_ctor_get(v_inst_1291_, 1);
lean_inc_n(v_toBind_1309_, 2);
v___x_1310_ = lean_box(v___x_1299_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed), 12, 11);
lean_closure_set(v___f_1311_, 0, v_inst_1293_);
lean_closure_set(v___f_1311_, 1, v_inst_1295_);
lean_closure_set(v___f_1311_, 2, v___x_1310_);
lean_closure_set(v___f_1311_, 3, v_p_1297_);
lean_closure_set(v___f_1311_, 4, v_toApplicative_1308_);
lean_closure_set(v___f_1311_, 5, v_toBind_1309_);
lean_closure_set(v___f_1311_, 6, v_inst_1291_);
lean_closure_set(v___f_1311_, 7, v_inst_1294_);
lean_closure_set(v___f_1311_, 8, v_inst_1296_);
lean_closure_set(v___f_1311_, 9, v___x_1300_);
lean_closure_set(v___f_1311_, 10, v_s_1298_);
v___x_1312_ = lean_apply_4(v_toBind_1309_, lean_box(0), lean_box(0), v_inst_1292_, v___f_1311_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_p_1320_, lean_object* v_s_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_p_1320_, v_s_1321_);
return v___x_1322_;
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
