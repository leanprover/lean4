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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9_value;
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object* v_env_52_, lean_object* v_contents_53_, lean_object* v_p_54_, lean_object* v_ictx_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_toPure_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_s_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
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
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_toPure_58_);
v___x_70_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v_s_65_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofFormat(v___x_71_);
v___x_73_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_stxStack_74_; lean_object* v_pos_75_; uint8_t v___x_76_; 
v_stxStack_74_ = lean_ctor_get(v_s_65_, 0);
lean_inc_ref(v_stxStack_74_);
v_pos_75_ = lean_ctor_get(v_s_65_, 2);
lean_inc(v_pos_75_);
v___x_76_ = l_Lean_Parser_InputContext_atEnd(v_ictx_55_, v_pos_75_);
lean_dec(v_pos_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_stxStack_74_);
lean_dec(v_toPure_58_);
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_78_ = l_Lean_Parser_ParserState_mkError(v_s_65_, v___x_77_);
v___x_79_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v___x_78_);
v___x_80_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___x_81_ = l_Lean_MessageData_ofFormat(v___x_80_);
v___x_82_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_s_65_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_ictx_55_);
v___x_83_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_74_);
lean_dec_ref(v_stxStack_74_);
v___x_84_ = lean_apply_2(v_toPure_58_, lean_box(0), v___x_83_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_85_, lean_object* v_contents_86_, lean_object* v_p_87_, lean_object* v_ictx_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_toPure_91_, lean_object* v_____do__lift_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_85_, v_contents_86_, v_p_87_, v_ictx_88_, v_inst_89_, v_inst_90_, v_toPure_91_, v_____do__lift_92_);
lean_dec_ref(v_contents_86_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_contents_94_, lean_object* v_env_95_, lean_object* v_p_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_toPure_99_, lean_object* v_toBind_100_, lean_object* v_inst_101_, lean_object* v_____do__lift_102_){
_start:
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v_ictx_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v___x_103_ = 1;
v___x_104_ = lean_string_utf8_byte_size(v_contents_94_);
lean_inc_ref(v_contents_94_);
v_ictx_105_ = l_Lean_Parser_mkInputContext___redArg(v_contents_94_, v_____do__lift_102_, v___x_103_, v___x_104_);
v___f_106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_106_, 0, v_env_95_);
lean_closure_set(v___f_106_, 1, v_contents_94_);
lean_closure_set(v___f_106_, 2, v_p_96_);
lean_closure_set(v___f_106_, 3, v_ictx_105_);
lean_closure_set(v___f_106_, 4, v_inst_97_);
lean_closure_set(v___f_106_, 5, v_inst_98_);
lean_closure_set(v___f_106_, 6, v_toPure_99_);
v___x_107_ = lean_apply_4(v_toBind_100_, lean_box(0), lean_box(0), v_inst_101_, v___f_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_108_, lean_object* v_contents_109_, lean_object* v_p_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_toPure_113_, lean_object* v_toBind_114_, lean_object* v_inst_115_, lean_object* v_env_116_){
_start:
{
lean_object* v_getFileName_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_getFileName_117_ = lean_ctor_get(v_inst_108_, 2);
lean_inc(v_getFileName_117_);
lean_dec_ref(v_inst_108_);
lean_inc(v_toBind_114_);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_118_, 0, v_contents_109_);
lean_closure_set(v___f_118_, 1, v_env_116_);
lean_closure_set(v___f_118_, 2, v_p_110_);
lean_closure_set(v___f_118_, 3, v_inst_111_);
lean_closure_set(v___f_118_, 4, v_inst_112_);
lean_closure_set(v___f_118_, 5, v_toPure_113_);
lean_closure_set(v___f_118_, 6, v_toBind_114_);
lean_closure_set(v___f_118_, 7, v_inst_115_);
v___x_119_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v_getFileName_117_, v___f_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_p_125_, lean_object* v_contents_126_){
_start:
{
lean_object* v_toApplicative_127_; lean_object* v_toBind_128_; lean_object* v_getEnv_129_; lean_object* v_toPure_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v_toApplicative_127_ = lean_ctor_get(v_inst_120_, 0);
v_toBind_128_ = lean_ctor_get(v_inst_120_, 1);
lean_inc_n(v_toBind_128_, 2);
v_getEnv_129_ = lean_ctor_get(v_inst_121_, 0);
lean_inc(v_getEnv_129_);
lean_dec_ref(v_inst_121_);
v_toPure_130_ = lean_ctor_get(v_toApplicative_127_, 1);
lean_inc(v_toPure_130_);
v___f_131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_131_, 0, v_inst_123_);
lean_closure_set(v___f_131_, 1, v_contents_126_);
lean_closure_set(v___f_131_, 2, v_p_125_);
lean_closure_set(v___f_131_, 3, v_inst_120_);
lean_closure_set(v___f_131_, 4, v_inst_122_);
lean_closure_set(v___f_131_, 5, v_toPure_130_);
lean_closure_set(v___f_131_, 6, v_toBind_128_);
lean_closure_set(v___f_131_, 7, v_inst_124_);
v___x_132_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v_getEnv_129_, v___f_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_p_139_, lean_object* v_contents_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_p_139_, v_contents_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object* v_env_142_, lean_object* v_p_143_, lean_object* v_ictx_144_, lean_object* v_s_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_toPure_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_s_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_box(0);
lean_inc_ref(v_env_142_);
v___x_152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_152_, 0, v_env_142_);
lean_ctor_set(v___x_152_, 1, v_____do__lift_149_);
lean_ctor_set(v___x_152_, 2, v___x_150_);
lean_ctor_set(v___x_152_, 3, v___x_151_);
v___x_153_ = l_Lean_Parser_getTokenTable(v_env_142_);
lean_inc_ref(v_ictx_144_);
v_s_154_ = l_Lean_Parser_ParserFn_run(v_p_143_, v_ictx_144_, v___x_152_, v___x_153_, v_s_145_);
lean_inc_ref(v_s_154_);
v___x_155_ = l_Lean_Parser_ParserState_allErrors(v_s_154_);
v___x_156_ = lean_array_get_size(v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_toPure_148_);
v___x_159_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_144_, v_s_154_);
v___x_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = l_Lean_MessageData_ofFormat(v___x_160_);
v___x_162_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v_stxStack_163_; lean_object* v_pos_164_; uint8_t v___x_165_; 
v_stxStack_163_ = lean_ctor_get(v_s_154_, 0);
lean_inc_ref(v_stxStack_163_);
v_pos_164_ = lean_ctor_get(v_s_154_, 2);
lean_inc(v_pos_164_);
v___x_165_ = l_Lean_Parser_InputContext_atEnd(v_ictx_144_, v_pos_164_);
lean_dec(v_pos_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec_ref(v_stxStack_163_);
lean_dec(v_toPure_148_);
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_167_ = l_Lean_Parser_ParserState_mkError(v_s_154_, v___x_166_);
v___x_168_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_144_, v___x_167_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = l_Lean_MessageData_ofFormat(v___x_169_);
v___x_171_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref(v_s_154_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_ictx_144_);
v___x_172_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_163_);
lean_dec_ref(v_stxStack_163_);
v___x_173_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_172_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object* v_source_174_, uint8_t v___x_175_, lean_object* v___y_176_, lean_object* v_start_177_, lean_object* v_env_178_, lean_object* v_p_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_toPure_182_, lean_object* v_toBind_183_, lean_object* v_inst_184_, lean_object* v_____do__lift_185_){
_start:
{
lean_object* v_ictx_186_; lean_object* v___x_187_; lean_object* v_s_188_; lean_object* v___f_189_; lean_object* v___x_190_; 
lean_inc_ref(v_source_174_);
v_ictx_186_ = l_Lean_Parser_mkInputContext___redArg(v_source_174_, v_____do__lift_185_, v___x_175_, v___y_176_);
v___x_187_ = l_Lean_Parser_mkParserState(v_source_174_);
lean_dec_ref(v_source_174_);
v_s_188_ = l_Lean_Parser_ParserState_setPos(v___x_187_, v_start_177_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__0), 8, 7);
lean_closure_set(v___f_189_, 0, v_env_178_);
lean_closure_set(v___f_189_, 1, v_p_179_);
lean_closure_set(v___f_189_, 2, v_ictx_186_);
lean_closure_set(v___f_189_, 3, v_s_188_);
lean_closure_set(v___f_189_, 4, v_inst_180_);
lean_closure_set(v___f_189_, 5, v_inst_181_);
lean_closure_set(v___f_189_, 6, v_toPure_182_);
v___x_190_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v_inst_184_, v___f_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1___boxed(lean_object* v_source_191_, lean_object* v___x_192_, lean_object* v___y_193_, lean_object* v_start_194_, lean_object* v_env_195_, lean_object* v_p_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_toPure_199_, lean_object* v_toBind_200_, lean_object* v_inst_201_, lean_object* v_____do__lift_202_){
_start:
{
uint8_t v___x_353__boxed_203_; lean_object* v_res_204_; 
v___x_353__boxed_203_ = lean_unbox(v___x_192_);
v_res_204_ = l_Lean_Doc_parseStrLit___redArg___lam__1(v_source_191_, v___x_353__boxed_203_, v___y_193_, v_start_194_, v_env_195_, v_p_196_, v_inst_197_, v_inst_198_, v_toPure_199_, v_toBind_200_, v_inst_201_, v_____do__lift_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object* v_text_205_, lean_object* v_inst_206_, uint8_t v___x_207_, lean_object* v_env_208_, lean_object* v_p_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_toPure_212_, lean_object* v_toBind_213_, lean_object* v_inst_214_, lean_object* v_____x_215_){
_start:
{
lean_object* v_start_216_; lean_object* v_stop_217_; lean_object* v_source_218_; lean_object* v___y_220_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_start_216_ = lean_ctor_get(v_____x_215_, 0);
lean_inc(v_start_216_);
v_stop_217_ = lean_ctor_get(v_____x_215_, 1);
lean_inc(v_stop_217_);
lean_dec_ref(v_____x_215_);
v_source_218_ = lean_ctor_get(v_text_205_, 0);
lean_inc_ref(v_source_218_);
lean_dec_ref(v_text_205_);
v___x_225_ = lean_string_utf8_byte_size(v_source_218_);
v___x_226_ = lean_nat_dec_le(v_stop_217_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v_stop_217_);
v___y_220_ = v___x_225_;
goto v___jp_219_;
}
else
{
v___y_220_ = v_stop_217_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v_getFileName_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; 
v_getFileName_221_ = lean_ctor_get(v_inst_206_, 2);
lean_inc(v_getFileName_221_);
lean_dec_ref(v_inst_206_);
v___x_222_ = lean_box(v___x_207_);
lean_inc(v_toBind_213_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_223_, 0, v_source_218_);
lean_closure_set(v___f_223_, 1, v___x_222_);
lean_closure_set(v___f_223_, 2, v___y_220_);
lean_closure_set(v___f_223_, 3, v_start_216_);
lean_closure_set(v___f_223_, 4, v_env_208_);
lean_closure_set(v___f_223_, 5, v_p_209_);
lean_closure_set(v___f_223_, 6, v_inst_210_);
lean_closure_set(v___f_223_, 7, v_inst_211_);
lean_closure_set(v___f_223_, 8, v_toPure_212_);
lean_closure_set(v___f_223_, 9, v_toBind_213_);
lean_closure_set(v___f_223_, 10, v_inst_214_);
v___x_224_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v_getFileName_221_, v___f_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2___boxed(lean_object* v_text_227_, lean_object* v_inst_228_, lean_object* v___x_229_, lean_object* v_env_230_, lean_object* v_p_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_toPure_234_, lean_object* v_toBind_235_, lean_object* v_inst_236_, lean_object* v_____x_237_){
_start:
{
uint8_t v___x_381__boxed_238_; lean_object* v_res_239_; 
v___x_381__boxed_238_ = lean_unbox(v___x_229_);
v_res_239_ = l_Lean_Doc_parseStrLit___redArg___lam__2(v_text_227_, v_inst_228_, v___x_381__boxed_238_, v_env_230_, v_p_231_, v_inst_232_, v_inst_233_, v_toPure_234_, v_toBind_235_, v_inst_236_, v_____x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object* v_text_240_, lean_object* v_inst_241_, uint8_t v___x_242_, lean_object* v_p_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_toPure_246_, lean_object* v_toBind_247_, lean_object* v_inst_248_, lean_object* v_s_249_, lean_object* v_env_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_box(v___x_242_);
lean_inc(v_toBind_247_);
lean_inc_ref(v_inst_244_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_252_, 0, v_text_240_);
lean_closure_set(v___f_252_, 1, v_inst_241_);
lean_closure_set(v___f_252_, 2, v___x_251_);
lean_closure_set(v___f_252_, 3, v_env_250_);
lean_closure_set(v___f_252_, 4, v_p_243_);
lean_closure_set(v___f_252_, 5, v_inst_244_);
lean_closure_set(v___f_252_, 6, v_inst_245_);
lean_closure_set(v___f_252_, 7, v_toPure_246_);
lean_closure_set(v___f_252_, 8, v_toBind_247_);
lean_closure_set(v___f_252_, 9, v_inst_248_);
v___x_253_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_244_, v_s_249_);
v___x_254_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_253_, v___f_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object* v_text_255_, lean_object* v_inst_256_, lean_object* v___x_257_, lean_object* v_p_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_toPure_261_, lean_object* v_toBind_262_, lean_object* v_inst_263_, lean_object* v_s_264_, lean_object* v_env_265_){
_start:
{
uint8_t v___x_417__boxed_266_; lean_object* v_res_267_; 
v___x_417__boxed_266_ = lean_unbox(v___x_257_);
v_res_267_ = l_Lean_Doc_parseStrLit___redArg___lam__3(v_text_255_, v_inst_256_, v___x_417__boxed_266_, v_p_258_, v_inst_259_, v_inst_260_, v_toPure_261_, v_toBind_262_, v_inst_263_, v_s_264_, v_env_265_);
lean_dec(v_s_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object* v_inst_268_, lean_object* v_inst_269_, uint8_t v___x_270_, lean_object* v_p_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_toPure_274_, lean_object* v_toBind_275_, lean_object* v_inst_276_, lean_object* v_s_277_, lean_object* v_text_278_){
_start:
{
lean_object* v_getEnv_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; 
v_getEnv_279_ = lean_ctor_get(v_inst_268_, 0);
lean_inc(v_getEnv_279_);
lean_dec_ref(v_inst_268_);
v___x_280_ = lean_box(v___x_270_);
lean_inc(v_toBind_275_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_281_, 0, v_text_278_);
lean_closure_set(v___f_281_, 1, v_inst_269_);
lean_closure_set(v___f_281_, 2, v___x_280_);
lean_closure_set(v___f_281_, 3, v_p_271_);
lean_closure_set(v___f_281_, 4, v_inst_272_);
lean_closure_set(v___f_281_, 5, v_inst_273_);
lean_closure_set(v___f_281_, 6, v_toPure_274_);
lean_closure_set(v___f_281_, 7, v_toBind_275_);
lean_closure_set(v___f_281_, 8, v_inst_276_);
lean_closure_set(v___f_281_, 9, v_s_277_);
v___x_282_ = lean_apply_4(v_toBind_275_, lean_box(0), lean_box(0), v_getEnv_279_, v___f_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4___boxed(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v___x_285_, lean_object* v_p_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_toPure_289_, lean_object* v_toBind_290_, lean_object* v_inst_291_, lean_object* v_s_292_, lean_object* v_text_293_){
_start:
{
uint8_t v___x_441__boxed_294_; lean_object* v_res_295_; 
v___x_441__boxed_294_ = lean_unbox(v___x_285_);
v_res_295_ = l_Lean_Doc_parseStrLit___redArg___lam__4(v_inst_283_, v_inst_284_, v___x_441__boxed_294_, v_p_286_, v_inst_287_, v_inst_288_, v_toPure_289_, v_toBind_290_, v_inst_291_, v_s_292_, v_text_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_p_302_, lean_object* v_s_303_){
_start:
{
uint8_t v___x_304_; uint8_t v___y_306_; lean_object* v___x_315_; 
v___x_304_ = 1;
v___x_315_ = l_Lean_Syntax_getPos_x3f(v_s_303_, v___x_304_);
if (lean_obj_tag(v___x_315_) == 0)
{
v___y_306_ = v___x_304_;
goto v___jp_305_;
}
else
{
uint8_t v___x_316_; 
lean_dec_ref_known(v___x_315_, 1);
v___x_316_ = 0;
v___y_306_ = v___x_316_;
goto v___jp_305_;
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
lean_object* v_toApplicative_307_; lean_object* v_toBind_308_; lean_object* v_toPure_309_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___x_312_; 
v_toApplicative_307_ = lean_ctor_get(v_inst_296_, 0);
v_toBind_308_ = lean_ctor_get(v_inst_296_, 1);
lean_inc_n(v_toBind_308_, 2);
v_toPure_309_ = lean_ctor_get(v_toApplicative_307_, 1);
lean_inc(v_toPure_309_);
v___x_310_ = lean_box(v___x_304_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_311_, 0, v_inst_298_);
lean_closure_set(v___f_311_, 1, v_inst_300_);
lean_closure_set(v___f_311_, 2, v___x_310_);
lean_closure_set(v___f_311_, 3, v_p_302_);
lean_closure_set(v___f_311_, 4, v_inst_296_);
lean_closure_set(v___f_311_, 5, v_inst_299_);
lean_closure_set(v___f_311_, 6, v_toPure_309_);
lean_closure_set(v___f_311_, 7, v_toBind_308_);
lean_closure_set(v___f_311_, 8, v_inst_301_);
lean_closure_set(v___f_311_, 9, v_s_303_);
v___x_312_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v_inst_297_, v___f_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_inst_297_);
v___x_313_ = l_Lean_TSyntax_getString(v_s_303_);
lean_dec(v_s_303_);
v___x_314_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_296_, v_inst_298_, v_inst_299_, v_inst_300_, v_inst_301_, v_p_302_, v___x_313_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_p_324_, lean_object* v_s_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Doc_parseStrLit___redArg(v_inst_318_, v_inst_319_, v_inst_320_, v_inst_321_, v_inst_322_, v_inst_323_, v_p_324_, v_s_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_345_; 
v_fst_329_ = lean_ctor_get(v_a_328_, 0);
v_snd_330_ = lean_ctor_get(v_a_328_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_345_ == 0)
{
v___x_332_ = v_a_328_;
v_isShared_333_ = v_isSharedCheck_345_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_snd_330_);
lean_inc(v_fst_329_);
lean_dec(v_a_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_345_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_dec_le(v___x_334_, v_fst_329_);
if (v___x_335_ == 0)
{
lean_object* v___x_337_; 
if (v_isShared_333_ == 0)
{
v___x_337_ = v___x_332_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_fst_329_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_snd_330_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_string_utf8_prev(v_str_327_, v_fst_329_);
lean_dec(v_fst_329_);
v___x_340_ = lean_nat_add(v_snd_330_, v___x_334_);
lean_dec(v_snd_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_340_);
lean_ctor_set(v___x_332_, 0, v___x_339_);
v___x_342_ = v___x_332_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
v_a_328_ = v___x_342_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_toPure_559_, lean_object* v_____do__lift_560_){
_start:
{
if (lean_obj_tag(v_____do__lift_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
v_a_561_ = lean_ctor_get(v_____do__lift_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_____do__lift_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_563_ = v_____do__lift_560_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v_____do__lift_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 1);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_apply_2(v_toPure_559_, lean_box(0), v___x_566_);
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v_a_570_ = lean_ctor_get(v_____do__lift_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_____do__lift_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_____do__lift_560_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_____do__lift_560_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_apply_2(v_toPure_559_, lean_box(0), v___x_575_);
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_text_579_, lean_object* v_pos_580_, lean_object* v_str_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_fst_583_ = lean_ctor_get(v_x_582_, 0);
v_snd_584_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_x_582_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_inc(v_fst_583_);
lean_dec(v_x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_579_, v_pos_580_, v_str_581_, v_fst_583_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_snd_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_text_593_, lean_object* v_pos_594_, lean_object* v_str_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_text_593_, v_pos_594_, v_str_595_, v_x_596_);
lean_dec_ref(v_str_595_);
lean_dec_ref(v_text_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_env_617_, lean_object* v_p_618_, lean_object* v_ictx_619_, lean_object* v_s_620_, lean_object* v_text_621_, lean_object* v_pos_622_, lean_object* v_str_623_, lean_object* v___f_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_toPure_627_, lean_object* v_____do__lift_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_s_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_629_ = lean_box(0);
v___x_630_ = lean_box(0);
lean_inc_ref(v_env_617_);
v___x_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_631_, 0, v_env_617_);
lean_ctor_set(v___x_631_, 1, v_____do__lift_628_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
lean_ctor_set(v___x_631_, 3, v___x_630_);
v___x_632_ = l_Lean_Parser_getTokenTable(v_env_617_);
lean_inc_ref(v_ictx_619_);
v_s_633_ = l_Lean_Parser_ParserFn_run(v_p_618_, v_ictx_619_, v___x_631_, v___x_632_, v_s_620_);
lean_inc_ref(v_s_633_);
v___x_634_ = l_Lean_Parser_ParserState_allErrors(v_s_633_);
v___x_635_ = lean_array_get_size(v___x_634_);
lean_dec_ref(v___x_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v_stxStack_638_; lean_object* v_lhsPrec_639_; lean_object* v_pos_640_; lean_object* v_cache_641_; lean_object* v_errorMsg_642_; lean_object* v_recoveredErrors_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_toPure_627_);
v_stxStack_638_ = lean_ctor_get(v_s_633_, 0);
v_lhsPrec_639_ = lean_ctor_get(v_s_633_, 1);
v_pos_640_ = lean_ctor_get(v_s_633_, 2);
v_cache_641_ = lean_ctor_get(v_s_633_, 3);
v_errorMsg_642_ = lean_ctor_get(v_s_633_, 4);
v_recoveredErrors_643_ = lean_ctor_get(v_s_633_, 5);
v_isSharedCheck_680_ = !lean_is_exclusive(v_s_633_);
if (v_isSharedCheck_680_ == 0)
{
v___x_645_ = v_s_633_;
v_isShared_646_ = v_isSharedCheck_680_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_recoveredErrors_643_);
lean_inc(v_errorMsg_642_);
lean_inc(v_cache_641_);
lean_inc(v_pos_640_);
lean_inc(v_lhsPrec_639_);
lean_inc(v_stxStack_638_);
lean_dec(v_s_633_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_680_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___y_649_; 
lean_inc(v_pos_622_);
v___x_647_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_621_, v_pos_622_, v_str_623_, v_pos_640_);
if (lean_obj_tag(v_errorMsg_642_) == 0)
{
lean_dec(v_pos_622_);
v___y_649_ = v_errorMsg_642_;
goto v___jp_648_;
}
else
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_679_; 
v_val_661_ = lean_ctor_get(v_errorMsg_642_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_errorMsg_642_);
if (v_isSharedCheck_679_ == 0)
{
v___x_663_ = v_errorMsg_642_;
v_isShared_664_ = v_isSharedCheck_679_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_errorMsg_642_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_679_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_unexpectedTk_665_; lean_object* v_unexpected_666_; lean_object* v_expected_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
v_unexpectedTk_665_ = lean_ctor_get(v_val_661_, 0);
v_unexpected_666_ = lean_ctor_get(v_val_661_, 1);
v_expected_667_ = lean_ctor_get(v_val_661_, 2);
v_isSharedCheck_678_ = !lean_is_exclusive(v_val_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_669_ = v_val_661_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_expected_667_);
lean_inc(v_unexpected_666_);
lean_inc(v_unexpectedTk_665_);
lean_dec(v_val_661_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_621_, v_pos_622_, v_str_623_, v_unexpectedTk_665_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_unexpected_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_expected_667_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_675_ = v___x_663_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
v___y_649_ = v___x_675_;
goto v___jp_648_;
}
}
}
}
}
v___jp_648_:
{
lean_object* v___x_650_; size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v_s_655_; 
v___x_650_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9));
v_sz_651_ = lean_array_size(v_recoveredErrors_643_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_650_, v___f_624_, v_sz_651_, v___x_652_, v_recoveredErrors_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 5, v___x_653_);
lean_ctor_set(v___x_645_, 4, v___y_649_);
lean_ctor_set(v___x_645_, 2, v___x_647_);
v_s_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_stxStack_638_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_lhsPrec_639_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_cache_641_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v___y_649_);
lean_ctor_set(v_reuseFailAlloc_660_, 5, v___x_653_);
v_s_655_ = v_reuseFailAlloc_660_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_619_, v_s_655_);
v___x_657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = l_Lean_MessageData_ofFormat(v___x_657_);
v___x_659_ = l_Lean_throwError___redArg(v_inst_625_, v_inst_626_, v___x_658_);
return v___x_659_;
}
}
}
}
else
{
lean_object* v_stxStack_681_; lean_object* v_pos_682_; uint8_t v___x_683_; 
lean_dec_ref(v___f_624_);
v_stxStack_681_ = lean_ctor_get(v_s_633_, 0);
lean_inc_ref(v_stxStack_681_);
v_pos_682_ = lean_ctor_get(v_s_633_, 2);
lean_inc(v_pos_682_);
v___x_683_ = l_Lean_Parser_InputContext_atEnd(v_ictx_619_, v_pos_682_);
lean_dec(v_pos_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v_stxStack_681_);
lean_dec(v_toPure_627_);
lean_dec(v_pos_622_);
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_685_ = l_Lean_Parser_ParserState_mkError(v_s_633_, v___x_684_);
v___x_686_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_619_, v___x_685_);
v___x_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = l_Lean_MessageData_ofFormat(v___x_687_);
v___x_689_ = l_Lean_throwError___redArg(v_inst_625_, v_inst_626_, v___x_688_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v_s_633_);
lean_dec_ref(v_inst_626_);
lean_dec_ref(v_inst_625_);
lean_dec_ref(v_ictx_619_);
v___x_690_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_681_);
lean_dec_ref(v_stxStack_681_);
v___x_691_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_621_, v_pos_622_, v_str_623_, v___x_690_);
v___x_692_ = lean_apply_2(v_toPure_627_, lean_box(0), v___x_691_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_env_693_, lean_object* v_p_694_, lean_object* v_ictx_695_, lean_object* v_s_696_, lean_object* v_text_697_, lean_object* v_pos_698_, lean_object* v_str_699_, lean_object* v___f_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_toPure_703_, lean_object* v_____do__lift_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_env_693_, v_p_694_, v_ictx_695_, v_s_696_, v_text_697_, v_pos_698_, v_str_699_, v___f_700_, v_inst_701_, v_inst_702_, v_toPure_703_, v_____do__lift_704_);
lean_dec_ref(v_str_699_);
lean_dec_ref(v_text_697_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_str_706_, uint8_t v___x_707_, lean_object* v_env_708_, lean_object* v_p_709_, lean_object* v_text_710_, lean_object* v_pos_711_, lean_object* v___f_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_toPure_715_, lean_object* v_toBind_716_, lean_object* v_inst_717_, lean_object* v_____do__lift_718_){
_start:
{
lean_object* v___x_719_; lean_object* v_ictx_720_; lean_object* v_s_721_; lean_object* v___f_722_; lean_object* v___x_723_; 
v___x_719_ = lean_string_utf8_byte_size(v_str_706_);
lean_inc_ref(v_str_706_);
v_ictx_720_ = l_Lean_Parser_mkInputContext___redArg(v_str_706_, v_____do__lift_718_, v___x_707_, v___x_719_);
v_s_721_ = l_Lean_Parser_mkParserState(v_str_706_);
v___f_722_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_722_, 0, v_env_708_);
lean_closure_set(v___f_722_, 1, v_p_709_);
lean_closure_set(v___f_722_, 2, v_ictx_720_);
lean_closure_set(v___f_722_, 3, v_s_721_);
lean_closure_set(v___f_722_, 4, v_text_710_);
lean_closure_set(v___f_722_, 5, v_pos_711_);
lean_closure_set(v___f_722_, 6, v_str_706_);
lean_closure_set(v___f_722_, 7, v___f_712_);
lean_closure_set(v___f_722_, 8, v_inst_713_);
lean_closure_set(v___f_722_, 9, v_inst_714_);
lean_closure_set(v___f_722_, 10, v_toPure_715_);
v___x_723_ = lean_apply_4(v_toBind_716_, lean_box(0), lean_box(0), v_inst_717_, v___f_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_str_724_, lean_object* v___x_725_, lean_object* v_env_726_, lean_object* v_p_727_, lean_object* v_text_728_, lean_object* v_pos_729_, lean_object* v___f_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_toPure_733_, lean_object* v_toBind_734_, lean_object* v_inst_735_, lean_object* v_____do__lift_736_){
_start:
{
uint8_t v___x_1044__boxed_737_; lean_object* v_res_738_; 
v___x_1044__boxed_737_ = lean_unbox(v___x_725_);
v_res_738_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_str_724_, v___x_1044__boxed_737_, v_env_726_, v_p_727_, v_text_728_, v_pos_729_, v___f_730_, v_inst_731_, v_inst_732_, v_toPure_733_, v_toBind_734_, v_inst_735_, v_____do__lift_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v_inst_739_, lean_object* v_strLit_740_, lean_object* v_text_741_, uint8_t v___x_742_, lean_object* v_env_743_, lean_object* v_p_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_toPure_747_, lean_object* v_toBind_748_, lean_object* v_inst_749_, lean_object* v_pos_750_){
_start:
{
lean_object* v_getFileName_751_; lean_object* v_str_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v_getFileName_751_ = lean_ctor_get(v_inst_739_, 2);
lean_inc(v_getFileName_751_);
lean_dec_ref(v_inst_739_);
v_str_752_ = l_Lean_TSyntax_getString(v_strLit_740_);
lean_inc_ref(v_str_752_);
lean_inc(v_pos_750_);
lean_inc_ref(v_text_741_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_753_, 0, v_text_741_);
lean_closure_set(v___f_753_, 1, v_pos_750_);
lean_closure_set(v___f_753_, 2, v_str_752_);
v___x_754_ = lean_box(v___x_742_);
lean_inc(v_toBind_748_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_755_, 0, v_str_752_);
lean_closure_set(v___f_755_, 1, v___x_754_);
lean_closure_set(v___f_755_, 2, v_env_743_);
lean_closure_set(v___f_755_, 3, v_p_744_);
lean_closure_set(v___f_755_, 4, v_text_741_);
lean_closure_set(v___f_755_, 5, v_pos_750_);
lean_closure_set(v___f_755_, 6, v___f_753_);
lean_closure_set(v___f_755_, 7, v_inst_745_);
lean_closure_set(v___f_755_, 8, v_inst_746_);
lean_closure_set(v___f_755_, 9, v_toPure_747_);
lean_closure_set(v___f_755_, 10, v_toBind_748_);
lean_closure_set(v___f_755_, 11, v_inst_749_);
v___x_756_ = lean_apply_4(v_toBind_748_, lean_box(0), lean_box(0), v_getFileName_751_, v___f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object* v_inst_757_, lean_object* v_strLit_758_, lean_object* v_text_759_, lean_object* v___x_760_, lean_object* v_env_761_, lean_object* v_p_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_toPure_765_, lean_object* v_toBind_766_, lean_object* v_inst_767_, lean_object* v_pos_768_){
_start:
{
uint8_t v___x_1069__boxed_769_; lean_object* v_res_770_; 
v___x_1069__boxed_769_ = lean_unbox(v___x_760_);
v_res_770_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_757_, v_strLit_758_, v_text_759_, v___x_1069__boxed_769_, v_env_761_, v_p_762_, v_inst_763_, v_inst_764_, v_toPure_765_, v_toBind_766_, v_inst_767_, v_pos_768_);
lean_dec(v_strLit_758_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_771_, lean_object* v_pos_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_apply_1(v___f_771_, v_pos_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_text_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_strLit_780_, lean_object* v_toBind_781_, lean_object* v___f_782_, lean_object* v_toPure_783_, lean_object* v___f_784_, lean_object* v_____r_785_, lean_object* v_pos_786_){
_start:
{
lean_object* v_source_787_; uint32_t v___x_788_; uint32_t v___x_789_; uint8_t v___x_790_; 
v_source_787_ = lean_ctor_get(v_text_777_, 0);
v___x_788_ = lean_string_utf8_get(v_source_787_, v_pos_786_);
v___x_789_ = 34;
v___x_790_ = lean_uint32_dec_eq(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v___f_784_);
lean_dec(v_toPure_783_);
v___x_791_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1);
v___x_792_ = l_Lean_throwErrorAt___redArg(v_inst_778_, v_inst_779_, v_strLit_780_, v___x_791_);
v___x_793_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_792_, v___f_782_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v___f_782_);
lean_dec(v_strLit_780_);
lean_dec_ref(v_inst_779_);
lean_dec_ref(v_inst_778_);
v___x_794_ = lean_string_utf8_next(v_source_787_, v_pos_786_);
v___x_795_ = lean_apply_2(v_toPure_783_, lean_box(0), v___x_794_);
v___x_796_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_795_, v___f_784_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_text_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_strLit_800_, lean_object* v_toBind_801_, lean_object* v___f_802_, lean_object* v_toPure_803_, lean_object* v___f_804_, lean_object* v_____r_805_, lean_object* v_pos_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_text_797_, v_inst_798_, v_inst_799_, v_strLit_800_, v_toBind_801_, v___f_802_, v_toPure_803_, v___f_804_, v_____r_805_, v_pos_806_);
lean_dec(v_pos_806_);
lean_dec_ref(v_text_797_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v___f_808_, lean_object* v_____s_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(0);
v___x_811_ = lean_apply_2(v___f_808_, v___x_810_, v_____s_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_812_, lean_object* v_toPure_813_, lean_object* v_toBind_814_, lean_object* v___f_815_, lean_object* v_b_816_){
_start:
{
uint32_t v___x_817_; uint32_t v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_string_utf8_get(v_source_812_, v_b_816_);
v___x_818_ = 35;
v___x_819_ = lean_uint32_dec_eq(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_816_);
v___x_821_ = lean_apply_2(v_toPure_813_, lean_box(0), v___x_820_);
v___x_822_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v___x_821_, v___f_815_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_823_ = lean_string_utf8_next(v_source_812_, v_b_816_);
lean_dec(v_b_816_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = lean_apply_2(v_toPure_813_, lean_box(0), v___x_824_);
v___x_826_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v___x_825_, v___f_815_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_827_, lean_object* v_toPure_828_, lean_object* v_toBind_829_, lean_object* v___f_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_827_, v_toPure_828_, v_toBind_829_, v___f_830_, v_b_831_);
lean_dec_ref(v_source_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_833_, lean_object* v___f_834_, lean_object* v_toPure_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v_inst_838_, lean_object* v___f_839_, lean_object* v_____x_840_){
_start:
{
lean_object* v_start_841_; lean_object* v_source_842_; uint32_t v___x_843_; uint32_t v___x_844_; uint8_t v___x_845_; 
v_start_841_ = lean_ctor_get(v_____x_840_, 0);
lean_inc(v_start_841_);
lean_dec_ref(v_____x_840_);
v_source_842_ = lean_ctor_get(v_text_833_, 0);
lean_inc_ref(v_source_842_);
lean_dec_ref(v_text_833_);
v___x_843_ = lean_string_utf8_get(v_source_842_, v_start_841_);
v___x_844_ = 114;
v___x_845_ = lean_uint32_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v_source_842_);
lean_dec(v___f_839_);
lean_dec_ref(v_inst_838_);
lean_dec(v___f_837_);
lean_dec(v_toBind_836_);
lean_dec(v_toPure_835_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_apply_2(v___f_834_, v___x_846_, v_start_841_);
return v___x_847_;
}
else
{
lean_object* v___f_848_; lean_object* v_pos_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v___f_834_);
lean_inc(v_toBind_836_);
lean_inc_ref(v_source_842_);
v___f_848_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_848_, 0, v_source_842_);
lean_closure_set(v___f_848_, 1, v_toPure_835_);
lean_closure_set(v___f_848_, 2, v_toBind_836_);
lean_closure_set(v___f_848_, 3, v___f_837_);
v_pos_849_ = lean_string_utf8_next(v_source_842_, v_start_841_);
lean_dec(v_start_841_);
lean_dec_ref(v_source_842_);
v___x_850_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_838_, v___f_848_, v_pos_849_);
v___x_851_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_850_, v___f_839_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_852_, lean_object* v_strLit_853_, lean_object* v_text_854_, uint8_t v___x_855_, lean_object* v_p_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_toPure_859_, lean_object* v_toBind_860_, lean_object* v_inst_861_, lean_object* v___f_862_, lean_object* v_env_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_864_ = lean_box(v___x_855_);
lean_inc_n(v_toBind_860_, 3);
lean_inc_n(v_toPure_859_, 2);
lean_inc_ref(v_inst_858_);
lean_inc_ref_n(v_inst_857_, 3);
lean_inc_ref_n(v_text_854_, 2);
lean_inc_n(v_strLit_853_, 2);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_865_, 0, v_inst_852_);
lean_closure_set(v___f_865_, 1, v_strLit_853_);
lean_closure_set(v___f_865_, 2, v_text_854_);
lean_closure_set(v___f_865_, 3, v___x_864_);
lean_closure_set(v___f_865_, 4, v_env_863_);
lean_closure_set(v___f_865_, 5, v_p_856_);
lean_closure_set(v___f_865_, 6, v_inst_857_);
lean_closure_set(v___f_865_, 7, v_inst_858_);
lean_closure_set(v___f_865_, 8, v_toPure_859_);
lean_closure_set(v___f_865_, 9, v_toBind_860_);
lean_closure_set(v___f_865_, 10, v_inst_861_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_866_, 0, v___f_865_);
lean_inc_ref(v___f_866_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_867_, 0, v_text_854_);
lean_closure_set(v___f_867_, 1, v_inst_857_);
lean_closure_set(v___f_867_, 2, v_inst_858_);
lean_closure_set(v___f_867_, 3, v_strLit_853_);
lean_closure_set(v___f_867_, 4, v_toBind_860_);
lean_closure_set(v___f_867_, 5, v___f_866_);
lean_closure_set(v___f_867_, 6, v_toPure_859_);
lean_closure_set(v___f_867_, 7, v___f_866_);
lean_inc_ref(v___f_867_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6), 2, 1);
lean_closure_set(v___f_868_, 0, v___f_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 8, 7);
lean_closure_set(v___f_869_, 0, v_text_854_);
lean_closure_set(v___f_869_, 1, v___f_867_);
lean_closure_set(v___f_869_, 2, v_toPure_859_);
lean_closure_set(v___f_869_, 3, v_toBind_860_);
lean_closure_set(v___f_869_, 4, v___f_862_);
lean_closure_set(v___f_869_, 5, v_inst_857_);
lean_closure_set(v___f_869_, 6, v___f_868_);
v___x_870_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_857_, v_strLit_853_);
lean_dec(v_strLit_853_);
v___x_871_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_870_, v___f_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_872_, lean_object* v_strLit_873_, lean_object* v_text_874_, lean_object* v___x_875_, lean_object* v_p_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_toPure_879_, lean_object* v_toBind_880_, lean_object* v_inst_881_, lean_object* v___f_882_, lean_object* v_env_883_){
_start:
{
uint8_t v___x_1197__boxed_884_; lean_object* v_res_885_; 
v___x_1197__boxed_884_ = lean_unbox(v___x_875_);
v_res_885_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_872_, v_strLit_873_, v_text_874_, v___x_1197__boxed_884_, v_p_876_, v_inst_877_, v_inst_878_, v_toPure_879_, v_toBind_880_, v_inst_881_, v___f_882_, v_env_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_strLit_888_, uint8_t v___x_889_, lean_object* v_p_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_toPure_893_, lean_object* v_toBind_894_, lean_object* v_inst_895_, lean_object* v___f_896_, lean_object* v_text_897_){
_start:
{
lean_object* v_getEnv_898_; lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_901_; 
v_getEnv_898_ = lean_ctor_get(v_inst_886_, 0);
lean_inc(v_getEnv_898_);
lean_dec_ref(v_inst_886_);
v___x_899_ = lean_box(v___x_889_);
lean_inc(v_toBind_894_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_900_, 0, v_inst_887_);
lean_closure_set(v___f_900_, 1, v_strLit_888_);
lean_closure_set(v___f_900_, 2, v_text_897_);
lean_closure_set(v___f_900_, 3, v___x_899_);
lean_closure_set(v___f_900_, 4, v_p_890_);
lean_closure_set(v___f_900_, 5, v_inst_891_);
lean_closure_set(v___f_900_, 6, v_inst_892_);
lean_closure_set(v___f_900_, 7, v_toPure_893_);
lean_closure_set(v___f_900_, 8, v_toBind_894_);
lean_closure_set(v___f_900_, 9, v_inst_895_);
lean_closure_set(v___f_900_, 10, v___f_896_);
v___x_901_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v_getEnv_898_, v___f_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_strLit_904_, lean_object* v___x_905_, lean_object* v_p_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_toPure_909_, lean_object* v_toBind_910_, lean_object* v_inst_911_, lean_object* v___f_912_, lean_object* v_text_913_){
_start:
{
uint8_t v___x_1232__boxed_914_; lean_object* v_res_915_; 
v___x_1232__boxed_914_ = lean_unbox(v___x_905_);
v_res_915_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_902_, v_inst_903_, v_strLit_904_, v___x_1232__boxed_914_, v_p_906_, v_inst_907_, v_inst_908_, v_toPure_909_, v_toBind_910_, v_inst_911_, v___f_912_, v_text_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_p_922_, lean_object* v_strLit_923_){
_start:
{
uint8_t v___x_924_; uint8_t v___y_926_; lean_object* v___x_936_; 
v___x_924_ = 1;
v___x_936_ = l_Lean_Syntax_getPos_x3f(v_strLit_923_, v___x_924_);
if (lean_obj_tag(v___x_936_) == 0)
{
v___y_926_ = v___x_924_;
goto v___jp_925_;
}
else
{
uint8_t v___x_937_; 
lean_dec_ref_known(v___x_936_, 1);
v___x_937_ = 0;
v___y_926_ = v___x_937_;
goto v___jp_925_;
}
v___jp_925_:
{
if (v___y_926_ == 0)
{
lean_object* v_toApplicative_927_; lean_object* v_toBind_928_; lean_object* v_toPure_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___x_933_; 
v_toApplicative_927_ = lean_ctor_get(v_inst_916_, 0);
v_toBind_928_ = lean_ctor_get(v_inst_916_, 1);
lean_inc_n(v_toBind_928_, 2);
v_toPure_929_ = lean_ctor_get(v_toApplicative_927_, 1);
lean_inc_n(v_toPure_929_, 2);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_930_, 0, v_toPure_929_);
v___x_931_ = lean_box(v___x_924_);
v___f_932_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 12, 11);
lean_closure_set(v___f_932_, 0, v_inst_918_);
lean_closure_set(v___f_932_, 1, v_inst_920_);
lean_closure_set(v___f_932_, 2, v_strLit_923_);
lean_closure_set(v___f_932_, 3, v___x_931_);
lean_closure_set(v___f_932_, 4, v_p_922_);
lean_closure_set(v___f_932_, 5, v_inst_916_);
lean_closure_set(v___f_932_, 6, v_inst_919_);
lean_closure_set(v___f_932_, 7, v_toPure_929_);
lean_closure_set(v___f_932_, 8, v_toBind_928_);
lean_closure_set(v___f_932_, 9, v_inst_921_);
lean_closure_set(v___f_932_, 10, v___f_930_);
v___x_933_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v_inst_917_, v___f_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec(v_inst_917_);
v___x_934_ = l_Lean_TSyntax_getString(v_strLit_923_);
lean_dec(v_strLit_923_);
v___x_935_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_916_, v_inst_918_, v_inst_919_, v_inst_920_, v_inst_921_, v_p_922_, v___x_934_);
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_p_945_, lean_object* v_strLit_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_939_, v_inst_940_, v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_p_945_, v_strLit_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object* v_s_948_, lean_object* v_toPure_949_, uint8_t v_err_950_){
_start:
{
lean_object* v_stxStack_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_stxStack_951_ = lean_ctor_get(v_s_948_, 0);
v___x_952_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_951_);
v___x_953_ = lean_box(v_err_950_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_apply_2(v_toPure_949_, lean_box(0), v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object* v_s_956_, lean_object* v_toPure_957_, lean_object* v_err_958_){
_start:
{
uint8_t v_err_boxed_959_; lean_object* v_res_960_; 
v_err_boxed_959_ = lean_unbox(v_err_958_);
v_res_960_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_s_956_, v_toPure_957_, v_err_boxed_959_);
lean_dec_ref(v_s_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object* v___f_961_, uint8_t v_err_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(v_err_962_);
v___x_964_ = lean_apply_1(v___f_961_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object* v___f_965_, lean_object* v_err_966_){
_start:
{
uint8_t v_err_boxed_967_; lean_object* v_res_968_; 
v_err_boxed_967_ = lean_unbox(v_err_966_);
v_res_968_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_965_, v_err_boxed_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object* v_toPure_969_, uint8_t v___x_970_, lean_object* v_toBind_971_, lean_object* v___f_972_, lean_object* v_____r_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(v___x_970_);
v___x_975_ = lean_apply_2(v_toPure_969_, lean_box(0), v___x_974_);
v___x_976_ = lean_apply_4(v_toBind_971_, lean_box(0), lean_box(0), v___x_975_, v___f_972_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object* v_toPure_977_, lean_object* v___x_978_, lean_object* v_toBind_979_, lean_object* v___f_980_, lean_object* v_____r_981_){
_start:
{
uint8_t v___x_786__boxed_982_; lean_object* v_res_983_; 
v___x_786__boxed_982_ = lean_unbox(v___x_978_);
v_res_983_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(v_toPure_977_, v___x_786__boxed_982_, v_toBind_979_, v___f_980_, v_____r_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object* v_env_984_, lean_object* v_p_985_, lean_object* v_ictx_986_, lean_object* v_s_987_, lean_object* v_toPure_988_, uint8_t v___x_989_, lean_object* v_toBind_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, uint8_t v___y_995_, lean_object* v_____do__lift_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_s_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_997_ = lean_box(0);
v___x_998_ = lean_box(0);
lean_inc_ref(v_env_984_);
v___x_999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_999_, 0, v_env_984_);
lean_ctor_set(v___x_999_, 1, v_____do__lift_996_);
lean_ctor_set(v___x_999_, 2, v___x_997_);
lean_ctor_set(v___x_999_, 3, v___x_998_);
v___x_1000_ = l_Lean_Parser_getTokenTable(v_env_984_);
lean_inc_ref(v_ictx_986_);
v_s_1001_ = l_Lean_Parser_ParserFn_run(v_p_985_, v_ictx_986_, v___x_999_, v___x_1000_, v_s_987_);
lean_inc(v_toPure_988_);
lean_inc_ref_n(v_s_1001_, 2);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1002_, 0, v_s_1001_);
lean_closure_set(v___f_1002_, 1, v_toPure_988_);
v___x_1003_ = l_Lean_Parser_ParserState_allErrors(v_s_1001_);
v___x_1004_ = lean_array_get_size(v___x_1003_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_nat_dec_eq(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1007_, 0, v___f_1002_);
v___x_1008_ = lean_box(v___x_989_);
lean_inc(v_toBind_990_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1009_, 0, v_toPure_988_);
lean_closure_set(v___f_1009_, 1, v___x_1008_);
lean_closure_set(v___f_1009_, 2, v_toBind_990_);
lean_closure_set(v___f_1009_, 3, v___f_1007_);
v___x_1010_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_986_, v_s_1001_);
v___x_1011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
v___x_1012_ = l_Lean_MessageData_ofFormat(v___x_1011_);
v___x_1013_ = l_Lean_logError___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_inst_994_, v___x_1012_);
v___x_1014_ = lean_apply_4(v_toBind_990_, lean_box(0), lean_box(0), v___x_1013_, v___f_1009_);
return v___x_1014_;
}
else
{
lean_object* v_pos_1015_; uint8_t v___x_1016_; 
v_pos_1015_ = lean_ctor_get(v_s_1001_, 2);
lean_inc(v_pos_1015_);
v___x_1016_ = l_Lean_Parser_InputContext_atEnd(v_ictx_986_, v_pos_1015_);
lean_dec(v_pos_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1017_, 0, v___f_1002_);
v___x_1018_ = lean_box(v___x_989_);
lean_inc(v_toBind_990_);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1019_, 0, v_toPure_988_);
lean_closure_set(v___f_1019_, 1, v___x_1018_);
lean_closure_set(v___f_1019_, 2, v_toBind_990_);
lean_closure_set(v___f_1019_, 3, v___f_1017_);
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1021_ = l_Lean_Parser_ParserState_mkError(v_s_1001_, v___x_1020_);
v___x_1022_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_986_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
v___x_1024_ = l_Lean_MessageData_ofFormat(v___x_1023_);
v___x_1025_ = l_Lean_logError___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_inst_994_, v___x_1024_);
v___x_1026_ = lean_apply_4(v_toBind_990_, lean_box(0), lean_box(0), v___x_1025_, v___f_1019_);
return v___x_1026_;
}
else
{
lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_s_1001_);
lean_dec(v_inst_994_);
lean_dec(v_inst_993_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_inst_991_);
lean_dec_ref(v_ictx_986_);
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1027_, 0, v___f_1002_);
v___x_1028_ = lean_box(v___y_995_);
v___x_1029_ = lean_apply_2(v_toPure_988_, lean_box(0), v___x_1028_);
v___x_1030_ = lean_apply_4(v_toBind_990_, lean_box(0), lean_box(0), v___x_1029_, v___f_1027_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object* v_env_1031_, lean_object* v_p_1032_, lean_object* v_ictx_1033_, lean_object* v_s_1034_, lean_object* v_toPure_1035_, lean_object* v___x_1036_, lean_object* v_toBind_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v___y_1042_, lean_object* v_____do__lift_1043_){
_start:
{
uint8_t v___x_802__boxed_1044_; uint8_t v___y_807__boxed_1045_; lean_object* v_res_1046_; 
v___x_802__boxed_1044_ = lean_unbox(v___x_1036_);
v___y_807__boxed_1045_ = lean_unbox(v___y_1042_);
v_res_1046_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(v_env_1031_, v_p_1032_, v_ictx_1033_, v_s_1034_, v_toPure_1035_, v___x_802__boxed_1044_, v_toBind_1037_, v_inst_1038_, v_inst_1039_, v_inst_1040_, v_inst_1041_, v___y_807__boxed_1045_, v_____do__lift_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object* v_source_1047_, uint8_t v___x_1048_, lean_object* v___y_1049_, lean_object* v_env_1050_, lean_object* v_p_1051_, lean_object* v_toPure_1052_, lean_object* v_toBind_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, uint8_t v___y_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v_____do__lift_1061_){
_start:
{
lean_object* v_ictx_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; 
lean_inc_ref(v_source_1047_);
v_ictx_1062_ = l_Lean_Parser_mkInputContext___redArg(v_source_1047_, v_____do__lift_1061_, v___x_1048_, v___y_1049_);
v___x_1063_ = l_Lean_Parser_mkParserState(v_source_1047_);
lean_dec_ref(v_source_1047_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1072_ = l_panic___redArg(v___x_1060_, v___x_1071_);
v___y_1065_ = v___x_1072_;
goto v___jp_1064_;
}
else
{
lean_object* v_val_1073_; 
v_val_1073_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v___x_1059_, 1);
v___y_1065_ = v_val_1073_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v_s_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v_s_1066_ = l_Lean_Parser_ParserState_setPos(v___x_1063_, v___y_1065_);
v___x_1067_ = lean_box(v___x_1048_);
v___x_1068_ = lean_box(v___y_1058_);
lean_inc(v_inst_1057_);
lean_inc(v_toBind_1053_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1069_, 0, v_env_1050_);
lean_closure_set(v___f_1069_, 1, v_p_1051_);
lean_closure_set(v___f_1069_, 2, v_ictx_1062_);
lean_closure_set(v___f_1069_, 3, v_s_1066_);
lean_closure_set(v___f_1069_, 4, v_toPure_1052_);
lean_closure_set(v___f_1069_, 5, v___x_1067_);
lean_closure_set(v___f_1069_, 6, v_toBind_1053_);
lean_closure_set(v___f_1069_, 7, v_inst_1054_);
lean_closure_set(v___f_1069_, 8, v_inst_1055_);
lean_closure_set(v___f_1069_, 9, v_inst_1056_);
lean_closure_set(v___f_1069_, 10, v_inst_1057_);
lean_closure_set(v___f_1069_, 11, v___x_1068_);
v___x_1070_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v_inst_1057_, v___f_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object* v_source_1074_, lean_object* v___x_1075_, lean_object* v___y_1076_, lean_object* v_env_1077_, lean_object* v_p_1078_, lean_object* v_toPure_1079_, lean_object* v_toBind_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v___y_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_____do__lift_1088_){
_start:
{
uint8_t v___x_896__boxed_1089_; uint8_t v___y_902__boxed_1090_; lean_object* v_res_1091_; 
v___x_896__boxed_1089_ = lean_unbox(v___x_1075_);
v___y_902__boxed_1090_ = lean_unbox(v___y_1085_);
v_res_1091_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(v_source_1074_, v___x_896__boxed_1089_, v___y_1076_, v_env_1077_, v_p_1078_, v_toPure_1079_, v_toBind_1080_, v_inst_1081_, v_inst_1082_, v_inst_1083_, v_inst_1084_, v___y_902__boxed_1090_, v___x_1086_, v___x_1087_, v_____do__lift_1088_);
lean_dec(v___x_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object* v_text_1092_, lean_object* v_inst_1093_, uint8_t v___x_1094_, lean_object* v_p_1095_, lean_object* v_toPure_1096_, lean_object* v_toBind_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, uint8_t v___y_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_s_1104_, lean_object* v_env_1105_){
_start:
{
lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1115_; lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Syntax_getTailPos_x3f(v_s_1104_, v___x_1094_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1121_ = l_panic___redArg(v___x_1103_, v___x_1120_);
v___y_1115_ = v___x_1121_;
goto v___jp_1114_;
}
else
{
lean_object* v_val_1122_; 
v_val_1122_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_val_1122_);
lean_dec_ref_known(v___x_1119_, 1);
v___y_1115_ = v_val_1122_;
goto v___jp_1114_;
}
v___jp_1106_:
{
lean_object* v_getFileName_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; 
v_getFileName_1109_ = lean_ctor_get(v_inst_1093_, 2);
lean_inc(v_getFileName_1109_);
v___x_1110_ = lean_box(v___x_1094_);
v___x_1111_ = lean_box(v___y_1101_);
lean_inc(v_toBind_1097_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1112_, 0, v___y_1107_);
lean_closure_set(v___f_1112_, 1, v___x_1110_);
lean_closure_set(v___f_1112_, 2, v___y_1108_);
lean_closure_set(v___f_1112_, 3, v_env_1105_);
lean_closure_set(v___f_1112_, 4, v_p_1095_);
lean_closure_set(v___f_1112_, 5, v_toPure_1096_);
lean_closure_set(v___f_1112_, 6, v_toBind_1097_);
lean_closure_set(v___f_1112_, 7, v_inst_1098_);
lean_closure_set(v___f_1112_, 8, v_inst_1093_);
lean_closure_set(v___f_1112_, 9, v_inst_1099_);
lean_closure_set(v___f_1112_, 10, v_inst_1100_);
lean_closure_set(v___f_1112_, 11, v___x_1111_);
lean_closure_set(v___f_1112_, 12, v___x_1102_);
lean_closure_set(v___f_1112_, 13, v___x_1103_);
v___x_1113_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v_getFileName_1109_, v___f_1112_);
return v___x_1113_;
}
v___jp_1114_:
{
lean_object* v_source_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_source_1116_ = lean_ctor_get(v_text_1092_, 0);
lean_inc_ref(v_source_1116_);
lean_dec_ref(v_text_1092_);
v___x_1117_ = lean_string_utf8_byte_size(v_source_1116_);
v___x_1118_ = lean_nat_dec_le(v___y_1115_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec(v___y_1115_);
v___y_1107_ = v_source_1116_;
v___y_1108_ = v___x_1117_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v_source_1116_;
v___y_1108_ = v___y_1115_;
goto v___jp_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object* v_text_1123_, lean_object* v_inst_1124_, lean_object* v___x_1125_, lean_object* v_p_1126_, lean_object* v_toPure_1127_, lean_object* v_toBind_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v___y_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v_s_1135_, lean_object* v_env_1136_){
_start:
{
uint8_t v___x_962__boxed_1137_; uint8_t v___y_966__boxed_1138_; lean_object* v_res_1139_; 
v___x_962__boxed_1137_ = lean_unbox(v___x_1125_);
v___y_966__boxed_1138_ = lean_unbox(v___y_1132_);
v_res_1139_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__4(v_text_1123_, v_inst_1124_, v___x_962__boxed_1137_, v_p_1126_, v_toPure_1127_, v_toBind_1128_, v_inst_1129_, v_inst_1130_, v_inst_1131_, v___y_966__boxed_1138_, v___x_1133_, v___x_1134_, v_s_1135_, v_env_1136_);
lean_dec(v_s_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object* v_inst_1140_, lean_object* v_inst_1141_, uint8_t v___x_1142_, lean_object* v_p_1143_, lean_object* v_toPure_1144_, lean_object* v_toBind_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, uint8_t v___y_1149_, lean_object* v___x_1150_, lean_object* v___x_1151_, lean_object* v_s_1152_, lean_object* v_text_1153_){
_start:
{
lean_object* v_getEnv_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v_getEnv_1154_ = lean_ctor_get(v_inst_1140_, 0);
lean_inc(v_getEnv_1154_);
lean_dec_ref(v_inst_1140_);
v___x_1155_ = lean_box(v___x_1142_);
v___x_1156_ = lean_box(v___y_1149_);
lean_inc(v_toBind_1145_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_1157_, 0, v_text_1153_);
lean_closure_set(v___f_1157_, 1, v_inst_1141_);
lean_closure_set(v___f_1157_, 2, v___x_1155_);
lean_closure_set(v___f_1157_, 3, v_p_1143_);
lean_closure_set(v___f_1157_, 4, v_toPure_1144_);
lean_closure_set(v___f_1157_, 5, v_toBind_1145_);
lean_closure_set(v___f_1157_, 6, v_inst_1146_);
lean_closure_set(v___f_1157_, 7, v_inst_1147_);
lean_closure_set(v___f_1157_, 8, v_inst_1148_);
lean_closure_set(v___f_1157_, 9, v___x_1156_);
lean_closure_set(v___f_1157_, 10, v___x_1150_);
lean_closure_set(v___f_1157_, 11, v___x_1151_);
lean_closure_set(v___f_1157_, 12, v_s_1152_);
v___x_1158_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v_getEnv_1154_, v___f_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v___x_1161_, lean_object* v_p_1162_, lean_object* v_toPure_1163_, lean_object* v_toBind_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v___y_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_s_1171_, lean_object* v_text_1172_){
_start:
{
uint8_t v___x_1022__boxed_1173_; uint8_t v___y_1026__boxed_1174_; lean_object* v_res_1175_; 
v___x_1022__boxed_1173_ = lean_unbox(v___x_1161_);
v___y_1026__boxed_1174_ = lean_unbox(v___y_1168_);
v_res_1175_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__5(v_inst_1159_, v_inst_1160_, v___x_1022__boxed_1173_, v_p_1162_, v_toPure_1163_, v_toBind_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_, v___y_1026__boxed_1174_, v___x_1169_, v___x_1170_, v_s_1171_, v_text_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object* v_st_1176_, lean_object* v_toPure_1177_, uint8_t v_err_1178_){
_start:
{
lean_object* v_stxStack_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_stxStack_1179_ = lean_ctor_get(v_st_1176_, 0);
v___x_1180_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1179_);
v___x_1181_ = lean_box(v_err_1178_);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_apply_2(v_toPure_1177_, lean_box(0), v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object* v_st_1184_, lean_object* v_toPure_1185_, lean_object* v_err_1186_){
_start:
{
uint8_t v_err_boxed_1187_; lean_object* v_res_1188_; 
v_err_boxed_1187_ = lean_unbox(v_err_1186_);
v_res_1188_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__7(v_st_1184_, v_toPure_1185_, v_err_boxed_1187_);
lean_dec_ref(v_st_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__13(lean_object* v_env_1189_, lean_object* v_contents_1190_, lean_object* v_p_1191_, lean_object* v_ictx_1192_, lean_object* v_toPure_1193_, uint8_t v___x_1194_, lean_object* v_toBind_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_____do__lift_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_st_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_box(0);
lean_inc_ref(v_env_1189_);
v___x_1203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1203_, 0, v_env_1189_);
lean_ctor_set(v___x_1203_, 1, v_____do__lift_1200_);
lean_ctor_set(v___x_1203_, 2, v___x_1201_);
lean_ctor_set(v___x_1203_, 3, v___x_1202_);
v___x_1204_ = l_Lean_Parser_getTokenTable(v_env_1189_);
v___x_1205_ = l_Lean_Parser_mkParserState(v_contents_1190_);
lean_inc_ref(v_ictx_1192_);
v_st_1206_ = l_Lean_Parser_ParserFn_run(v_p_1191_, v_ictx_1192_, v___x_1203_, v___x_1204_, v___x_1205_);
lean_inc(v_toPure_1193_);
lean_inc_ref_n(v_st_1206_, 2);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1207_, 0, v_st_1206_);
lean_closure_set(v___f_1207_, 1, v_toPure_1193_);
v___x_1208_ = l_Lean_Parser_ParserState_allErrors(v_st_1206_);
v___x_1209_ = lean_array_get_size(v___x_1208_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_nat_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1212_, 0, v___f_1207_);
v___x_1213_ = lean_box(v___x_1194_);
lean_inc(v_toBind_1195_);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1214_, 0, v_toPure_1193_);
lean_closure_set(v___f_1214_, 1, v___x_1213_);
lean_closure_set(v___f_1214_, 2, v_toBind_1195_);
lean_closure_set(v___f_1214_, 3, v___f_1212_);
v___x_1215_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1192_, v_st_1206_);
v___x_1216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
v___x_1217_ = l_Lean_MessageData_ofFormat(v___x_1216_);
v___x_1218_ = l_Lean_logError___redArg(v_inst_1196_, v_inst_1197_, v_inst_1198_, v_inst_1199_, v___x_1217_);
v___x_1219_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v___x_1218_, v___f_1214_);
return v___x_1219_;
}
else
{
lean_object* v_pos_1220_; uint8_t v___x_1221_; 
v_pos_1220_ = lean_ctor_get(v_st_1206_, 2);
lean_inc(v_pos_1220_);
v___x_1221_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1192_, v_pos_1220_);
lean_dec(v_pos_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1222_, 0, v___f_1207_);
v___x_1223_ = lean_box(v___x_1194_);
lean_inc(v_toBind_1195_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1224_, 0, v_toPure_1193_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v_toBind_1195_);
lean_closure_set(v___f_1224_, 3, v___f_1222_);
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1226_ = l_Lean_Parser_ParserState_mkError(v_st_1206_, v___x_1225_);
v___x_1227_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1192_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
v___x_1229_ = l_Lean_MessageData_ofFormat(v___x_1228_);
v___x_1230_ = l_Lean_logError___redArg(v_inst_1196_, v_inst_1197_, v_inst_1198_, v_inst_1199_, v___x_1229_);
v___x_1231_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v___x_1230_, v___f_1224_);
return v___x_1231_;
}
else
{
lean_object* v___f_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v_st_1206_);
lean_dec(v_inst_1199_);
lean_dec(v_inst_1198_);
lean_dec_ref(v_inst_1197_);
lean_dec_ref(v_inst_1196_);
lean_dec_ref(v_ictx_1192_);
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1232_, 0, v___f_1207_);
v___x_1233_ = 0;
v___x_1234_ = lean_box(v___x_1233_);
v___x_1235_ = lean_apply_2(v_toPure_1193_, lean_box(0), v___x_1234_);
v___x_1236_ = lean_apply_4(v_toBind_1195_, lean_box(0), lean_box(0), v___x_1235_, v___f_1232_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__13___boxed(lean_object* v_env_1237_, lean_object* v_contents_1238_, lean_object* v_p_1239_, lean_object* v_ictx_1240_, lean_object* v_toPure_1241_, lean_object* v___x_1242_, lean_object* v_toBind_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_____do__lift_1248_){
_start:
{
uint8_t v___x_1064__boxed_1249_; lean_object* v_res_1250_; 
v___x_1064__boxed_1249_ = lean_unbox(v___x_1242_);
v_res_1250_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__13(v_env_1237_, v_contents_1238_, v_p_1239_, v_ictx_1240_, v_toPure_1241_, v___x_1064__boxed_1249_, v_toBind_1243_, v_inst_1244_, v_inst_1245_, v_inst_1246_, v_inst_1247_, v_____do__lift_1248_);
lean_dec_ref(v_contents_1238_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object* v_contents_1251_, uint8_t v___x_1252_, lean_object* v_env_1253_, lean_object* v_p_1254_, lean_object* v_toPure_1255_, lean_object* v_toBind_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_____do__lift_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v_ictx_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
v___x_1262_ = lean_string_utf8_byte_size(v_contents_1251_);
lean_inc_ref(v_contents_1251_);
v_ictx_1263_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1251_, v_____do__lift_1261_, v___x_1252_, v___x_1262_);
v___x_1264_ = lean_box(v___x_1252_);
lean_inc(v_inst_1260_);
lean_inc(v_toBind_1256_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_1265_, 0, v_env_1253_);
lean_closure_set(v___f_1265_, 1, v_contents_1251_);
lean_closure_set(v___f_1265_, 2, v_p_1254_);
lean_closure_set(v___f_1265_, 3, v_ictx_1263_);
lean_closure_set(v___f_1265_, 4, v_toPure_1255_);
lean_closure_set(v___f_1265_, 5, v___x_1264_);
lean_closure_set(v___f_1265_, 6, v_toBind_1256_);
lean_closure_set(v___f_1265_, 7, v_inst_1257_);
lean_closure_set(v___f_1265_, 8, v_inst_1258_);
lean_closure_set(v___f_1265_, 9, v_inst_1259_);
lean_closure_set(v___f_1265_, 10, v_inst_1260_);
v___x_1266_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v_inst_1260_, v___f_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object* v_contents_1267_, lean_object* v___x_1268_, lean_object* v_env_1269_, lean_object* v_p_1270_, lean_object* v_toPure_1271_, lean_object* v_toBind_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_____do__lift_1277_){
_start:
{
uint8_t v___x_1150__boxed_1278_; lean_object* v_res_1279_; 
v___x_1150__boxed_1278_ = lean_unbox(v___x_1268_);
v_res_1279_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__8(v_contents_1267_, v___x_1150__boxed_1278_, v_env_1269_, v_p_1270_, v_toPure_1271_, v_toBind_1272_, v_inst_1273_, v_inst_1274_, v_inst_1275_, v_inst_1276_, v_____do__lift_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object* v_inst_1280_, lean_object* v_contents_1281_, uint8_t v___x_1282_, lean_object* v_p_1283_, lean_object* v_toPure_1284_, lean_object* v_toBind_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_env_1289_){
_start:
{
lean_object* v_getFileName_1290_; lean_object* v___x_1291_; lean_object* v___f_1292_; lean_object* v___x_1293_; 
v_getFileName_1290_ = lean_ctor_get(v_inst_1280_, 2);
lean_inc(v_getFileName_1290_);
v___x_1291_ = lean_box(v___x_1282_);
lean_inc(v_toBind_1285_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_1292_, 0, v_contents_1281_);
lean_closure_set(v___f_1292_, 1, v___x_1291_);
lean_closure_set(v___f_1292_, 2, v_env_1289_);
lean_closure_set(v___f_1292_, 3, v_p_1283_);
lean_closure_set(v___f_1292_, 4, v_toPure_1284_);
lean_closure_set(v___f_1292_, 5, v_toBind_1285_);
lean_closure_set(v___f_1292_, 6, v_inst_1286_);
lean_closure_set(v___f_1292_, 7, v_inst_1280_);
lean_closure_set(v___f_1292_, 8, v_inst_1287_);
lean_closure_set(v___f_1292_, 9, v_inst_1288_);
v___x_1293_ = lean_apply_4(v_toBind_1285_, lean_box(0), lean_box(0), v_getFileName_1290_, v___f_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object* v_inst_1294_, lean_object* v_contents_1295_, lean_object* v___x_1296_, lean_object* v_p_1297_, lean_object* v_toPure_1298_, lean_object* v_toBind_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_env_1303_){
_start:
{
uint8_t v___x_1177__boxed_1304_; lean_object* v_res_1305_; 
v___x_1177__boxed_1304_ = lean_unbox(v___x_1296_);
v_res_1305_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__9(v_inst_1294_, v_contents_1295_, v___x_1177__boxed_1304_, v_p_1297_, v_toPure_1298_, v_toBind_1299_, v_inst_1300_, v_inst_1301_, v_inst_1302_, v_env_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_p_1312_, lean_object* v_s_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; uint8_t v___y_1318_; 
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = 1;
v___x_1316_ = l_Lean_Syntax_getPos_x3f(v_s_1313_, v___x_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
v___y_1318_ = v___x_1315_;
goto v___jp_1317_;
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
v___y_1318_ = v___x_1334_;
goto v___jp_1317_;
}
v___jp_1317_:
{
if (v___y_1318_ == 0)
{
lean_object* v_toApplicative_1319_; lean_object* v_toBind_1320_; lean_object* v_toPure_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; 
v_toApplicative_1319_ = lean_ctor_get(v_inst_1306_, 0);
v_toBind_1320_ = lean_ctor_get(v_inst_1306_, 1);
lean_inc_n(v_toBind_1320_, 2);
v_toPure_1321_ = lean_ctor_get(v_toApplicative_1319_, 1);
lean_inc(v_toPure_1321_);
v___x_1322_ = lean_box(v___x_1315_);
v___x_1323_ = lean_box(v___y_1318_);
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1324_, 0, v_inst_1308_);
lean_closure_set(v___f_1324_, 1, v_inst_1310_);
lean_closure_set(v___f_1324_, 2, v___x_1322_);
lean_closure_set(v___f_1324_, 3, v_p_1312_);
lean_closure_set(v___f_1324_, 4, v_toPure_1321_);
lean_closure_set(v___f_1324_, 5, v_toBind_1320_);
lean_closure_set(v___f_1324_, 6, v_inst_1306_);
lean_closure_set(v___f_1324_, 7, v_inst_1309_);
lean_closure_set(v___f_1324_, 8, v_inst_1311_);
lean_closure_set(v___f_1324_, 9, v___x_1323_);
lean_closure_set(v___f_1324_, 10, v___x_1316_);
lean_closure_set(v___f_1324_, 11, v___x_1314_);
lean_closure_set(v___f_1324_, 12, v_s_1313_);
v___x_1325_ = lean_apply_4(v_toBind_1320_, lean_box(0), lean_box(0), v_inst_1307_, v___f_1324_);
return v___x_1325_;
}
else
{
lean_object* v_toApplicative_1326_; lean_object* v_toBind_1327_; lean_object* v_toPure_1328_; lean_object* v_getEnv_1329_; lean_object* v_contents_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; 
v_toApplicative_1326_ = lean_ctor_get(v_inst_1306_, 0);
lean_dec(v___x_1316_);
lean_dec(v_inst_1307_);
v_toBind_1327_ = lean_ctor_get(v_inst_1306_, 1);
lean_inc_n(v_toBind_1327_, 2);
v_toPure_1328_ = lean_ctor_get(v_toApplicative_1326_, 1);
lean_inc(v_toPure_1328_);
v_getEnv_1329_ = lean_ctor_get(v_inst_1308_, 0);
lean_inc(v_getEnv_1329_);
lean_dec_ref(v_inst_1308_);
v_contents_1330_ = l_Lean_TSyntax_getString(v_s_1313_);
lean_dec(v_s_1313_);
v___x_1331_ = lean_box(v___x_1315_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1332_, 0, v_inst_1310_);
lean_closure_set(v___f_1332_, 1, v_contents_1330_);
lean_closure_set(v___f_1332_, 2, v___x_1331_);
lean_closure_set(v___f_1332_, 3, v_p_1312_);
lean_closure_set(v___f_1332_, 4, v_toPure_1328_);
lean_closure_set(v___f_1332_, 5, v_toBind_1327_);
lean_closure_set(v___f_1332_, 6, v_inst_1306_);
lean_closure_set(v___f_1332_, 7, v_inst_1309_);
lean_closure_set(v___f_1332_, 8, v_inst_1311_);
v___x_1333_ = lean_apply_4(v_toBind_1327_, lean_box(0), lean_box(0), v_getEnv_1329_, v___f_1332_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_p_1342_, lean_object* v_s_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_inst_1341_, v_p_1342_, v_s_1343_);
return v___x_1344_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
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
