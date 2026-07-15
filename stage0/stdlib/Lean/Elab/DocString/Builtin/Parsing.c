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
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_toApplicative_58_);
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
lean_dec_ref(v_toApplicative_58_);
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
lean_object* v_toPure_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec_ref(v_s_65_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_ictx_55_);
v_toPure_83_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_83_);
lean_dec_ref(v_toApplicative_58_);
v___x_84_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_74_);
lean_dec_ref(v_stxStack_74_);
v___x_85_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_84_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_86_, lean_object* v_contents_87_, lean_object* v_p_88_, lean_object* v_ictx_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_toApplicative_92_, lean_object* v_____do__lift_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_86_, v_contents_87_, v_p_88_, v_ictx_89_, v_inst_90_, v_inst_91_, v_toApplicative_92_, v_____do__lift_93_);
lean_dec_ref(v_contents_87_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_contents_95_, lean_object* v_env_96_, lean_object* v_p_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_toApplicative_100_, lean_object* v_toBind_101_, lean_object* v_inst_102_, lean_object* v_____do__lift_103_){
_start:
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v_ictx_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___x_104_ = 1;
v___x_105_ = lean_string_utf8_byte_size(v_contents_95_);
lean_inc_ref(v_contents_95_);
v_ictx_106_ = l_Lean_Parser_mkInputContext___redArg(v_contents_95_, v_____do__lift_103_, v___x_104_, v___x_105_);
v___f_107_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_107_, 0, v_env_96_);
lean_closure_set(v___f_107_, 1, v_contents_95_);
lean_closure_set(v___f_107_, 2, v_p_97_);
lean_closure_set(v___f_107_, 3, v_ictx_106_);
lean_closure_set(v___f_107_, 4, v_inst_98_);
lean_closure_set(v___f_107_, 5, v_inst_99_);
lean_closure_set(v___f_107_, 6, v_toApplicative_100_);
v___x_108_ = lean_apply_4(v_toBind_101_, lean_box(0), lean_box(0), v_inst_102_, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_109_, lean_object* v_contents_110_, lean_object* v_p_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_toApplicative_114_, lean_object* v_toBind_115_, lean_object* v_inst_116_, lean_object* v_env_117_){
_start:
{
lean_object* v_getFileName_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_getFileName_118_ = lean_ctor_get(v_inst_109_, 2);
lean_inc(v_getFileName_118_);
lean_dec_ref(v_inst_109_);
lean_inc(v_toBind_115_);
v___f_119_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_119_, 0, v_contents_110_);
lean_closure_set(v___f_119_, 1, v_env_117_);
lean_closure_set(v___f_119_, 2, v_p_111_);
lean_closure_set(v___f_119_, 3, v_inst_112_);
lean_closure_set(v___f_119_, 4, v_inst_113_);
lean_closure_set(v___f_119_, 5, v_toApplicative_114_);
lean_closure_set(v___f_119_, 6, v_toBind_115_);
lean_closure_set(v___f_119_, 7, v_inst_116_);
v___x_120_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v_getFileName_118_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_p_126_, lean_object* v_contents_127_){
_start:
{
lean_object* v_toApplicative_128_; lean_object* v_toBind_129_; lean_object* v_getEnv_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v_toApplicative_128_ = lean_ctor_get(v_inst_121_, 0);
lean_inc_ref(v_toApplicative_128_);
v_toBind_129_ = lean_ctor_get(v_inst_121_, 1);
lean_inc_n(v_toBind_129_, 2);
v_getEnv_130_ = lean_ctor_get(v_inst_122_, 0);
lean_inc(v_getEnv_130_);
lean_dec_ref(v_inst_122_);
v___f_131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_131_, 0, v_inst_124_);
lean_closure_set(v___f_131_, 1, v_contents_127_);
lean_closure_set(v___f_131_, 2, v_p_126_);
lean_closure_set(v___f_131_, 3, v_inst_121_);
lean_closure_set(v___f_131_, 4, v_inst_123_);
lean_closure_set(v___f_131_, 5, v_toApplicative_128_);
lean_closure_set(v___f_131_, 6, v_toBind_129_);
lean_closure_set(v___f_131_, 7, v_inst_125_);
v___x_132_ = lean_apply_4(v_toBind_129_, lean_box(0), lean_box(0), v_getEnv_130_, v___f_131_);
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__0(lean_object* v_env_142_, lean_object* v_p_143_, lean_object* v_ictx_144_, lean_object* v_s_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_toApplicative_148_, lean_object* v_____do__lift_149_){
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
lean_dec_ref(v_toApplicative_148_);
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
lean_dec_ref(v_toApplicative_148_);
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
lean_object* v_toPure_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref(v_s_154_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_ictx_144_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_148_);
v___x_173_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_163_);
lean_dec_ref(v_stxStack_163_);
v___x_174_ = lean_apply_2(v_toPure_172_, lean_box(0), v___x_173_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1(lean_object* v_source_175_, uint8_t v___x_176_, lean_object* v___y_177_, lean_object* v_start_178_, lean_object* v_env_179_, lean_object* v_p_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_toApplicative_183_, lean_object* v_toBind_184_, lean_object* v_inst_185_, lean_object* v_____do__lift_186_){
_start:
{
lean_object* v_ictx_187_; lean_object* v___x_188_; lean_object* v_s_189_; lean_object* v___f_190_; lean_object* v___x_191_; 
lean_inc_ref(v_source_175_);
v_ictx_187_ = l_Lean_Parser_mkInputContext___redArg(v_source_175_, v_____do__lift_186_, v___x_176_, v___y_177_);
v___x_188_ = l_Lean_Parser_mkParserState(v_source_175_);
lean_dec_ref(v_source_175_);
v_s_189_ = l_Lean_Parser_ParserState_setPos(v___x_188_, v_start_178_);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__0), 8, 7);
lean_closure_set(v___f_190_, 0, v_env_179_);
lean_closure_set(v___f_190_, 1, v_p_180_);
lean_closure_set(v___f_190_, 2, v_ictx_187_);
lean_closure_set(v___f_190_, 3, v_s_189_);
lean_closure_set(v___f_190_, 4, v_inst_181_);
lean_closure_set(v___f_190_, 5, v_inst_182_);
lean_closure_set(v___f_190_, 6, v_toApplicative_183_);
v___x_191_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v_inst_185_, v___f_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__1___boxed(lean_object* v_source_192_, lean_object* v___x_193_, lean_object* v___y_194_, lean_object* v_start_195_, lean_object* v_env_196_, lean_object* v_p_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_toApplicative_200_, lean_object* v_toBind_201_, lean_object* v_inst_202_, lean_object* v_____do__lift_203_){
_start:
{
uint8_t v___x_730__boxed_204_; lean_object* v_res_205_; 
v___x_730__boxed_204_ = lean_unbox(v___x_193_);
v_res_205_ = l_Lean_Doc_parseStrLit___redArg___lam__1(v_source_192_, v___x_730__boxed_204_, v___y_194_, v_start_195_, v_env_196_, v_p_197_, v_inst_198_, v_inst_199_, v_toApplicative_200_, v_toBind_201_, v_inst_202_, v_____do__lift_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2(lean_object* v_text_206_, lean_object* v_inst_207_, uint8_t v___x_208_, lean_object* v_env_209_, lean_object* v_p_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_toApplicative_213_, lean_object* v_toBind_214_, lean_object* v_inst_215_, lean_object* v_____x_216_){
_start:
{
lean_object* v_start_217_; lean_object* v_stop_218_; lean_object* v_source_219_; lean_object* v___y_221_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_start_217_ = lean_ctor_get(v_____x_216_, 0);
lean_inc(v_start_217_);
v_stop_218_ = lean_ctor_get(v_____x_216_, 1);
lean_inc(v_stop_218_);
lean_dec_ref(v_____x_216_);
v_source_219_ = lean_ctor_get(v_text_206_, 0);
lean_inc_ref(v_source_219_);
lean_dec_ref(v_text_206_);
v___x_226_ = lean_string_utf8_byte_size(v_source_219_);
v___x_227_ = lean_nat_dec_le(v_stop_218_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_stop_218_);
v___y_221_ = v___x_226_;
goto v___jp_220_;
}
else
{
v___y_221_ = v_stop_218_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v_getFileName_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; 
v_getFileName_222_ = lean_ctor_get(v_inst_207_, 2);
lean_inc(v_getFileName_222_);
lean_dec_ref(v_inst_207_);
v___x_223_ = lean_box(v___x_208_);
lean_inc(v_toBind_214_);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_224_, 0, v_source_219_);
lean_closure_set(v___f_224_, 1, v___x_223_);
lean_closure_set(v___f_224_, 2, v___y_221_);
lean_closure_set(v___f_224_, 3, v_start_217_);
lean_closure_set(v___f_224_, 4, v_env_209_);
lean_closure_set(v___f_224_, 5, v_p_210_);
lean_closure_set(v___f_224_, 6, v_inst_211_);
lean_closure_set(v___f_224_, 7, v_inst_212_);
lean_closure_set(v___f_224_, 8, v_toApplicative_213_);
lean_closure_set(v___f_224_, 9, v_toBind_214_);
lean_closure_set(v___f_224_, 10, v_inst_215_);
v___x_225_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v_getFileName_222_, v___f_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__2___boxed(lean_object* v_text_228_, lean_object* v_inst_229_, lean_object* v___x_230_, lean_object* v_env_231_, lean_object* v_p_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_toApplicative_235_, lean_object* v_toBind_236_, lean_object* v_inst_237_, lean_object* v_____x_238_){
_start:
{
uint8_t v___x_758__boxed_239_; lean_object* v_res_240_; 
v___x_758__boxed_239_ = lean_unbox(v___x_230_);
v_res_240_ = l_Lean_Doc_parseStrLit___redArg___lam__2(v_text_228_, v_inst_229_, v___x_758__boxed_239_, v_env_231_, v_p_232_, v_inst_233_, v_inst_234_, v_toApplicative_235_, v_toBind_236_, v_inst_237_, v_____x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3(lean_object* v_text_241_, lean_object* v_inst_242_, uint8_t v___x_243_, lean_object* v_p_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_toApplicative_247_, lean_object* v_toBind_248_, lean_object* v_inst_249_, lean_object* v_s_250_, lean_object* v_env_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_box(v___x_243_);
lean_inc(v_toBind_248_);
lean_inc_ref(v_inst_245_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_253_, 0, v_text_241_);
lean_closure_set(v___f_253_, 1, v_inst_242_);
lean_closure_set(v___f_253_, 2, v___x_252_);
lean_closure_set(v___f_253_, 3, v_env_251_);
lean_closure_set(v___f_253_, 4, v_p_244_);
lean_closure_set(v___f_253_, 5, v_inst_245_);
lean_closure_set(v___f_253_, 6, v_inst_246_);
lean_closure_set(v___f_253_, 7, v_toApplicative_247_);
lean_closure_set(v___f_253_, 8, v_toBind_248_);
lean_closure_set(v___f_253_, 9, v_inst_249_);
v___x_254_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_245_, v_s_250_);
v___x_255_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_254_, v___f_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__3___boxed(lean_object* v_text_256_, lean_object* v_inst_257_, lean_object* v___x_258_, lean_object* v_p_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_toApplicative_262_, lean_object* v_toBind_263_, lean_object* v_inst_264_, lean_object* v_s_265_, lean_object* v_env_266_){
_start:
{
uint8_t v___x_794__boxed_267_; lean_object* v_res_268_; 
v___x_794__boxed_267_ = lean_unbox(v___x_258_);
v_res_268_ = l_Lean_Doc_parseStrLit___redArg___lam__3(v_text_256_, v_inst_257_, v___x_794__boxed_267_, v_p_259_, v_inst_260_, v_inst_261_, v_toApplicative_262_, v_toBind_263_, v_inst_264_, v_s_265_, v_env_266_);
lean_dec(v_s_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4(lean_object* v_inst_269_, lean_object* v_inst_270_, uint8_t v___x_271_, lean_object* v_p_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_toApplicative_275_, lean_object* v_toBind_276_, lean_object* v_inst_277_, lean_object* v_s_278_, lean_object* v_text_279_){
_start:
{
lean_object* v_getEnv_280_; lean_object* v___x_281_; lean_object* v___f_282_; lean_object* v___x_283_; 
v_getEnv_280_ = lean_ctor_get(v_inst_269_, 0);
lean_inc(v_getEnv_280_);
lean_dec_ref(v_inst_269_);
v___x_281_ = lean_box(v___x_271_);
lean_inc(v_toBind_276_);
v___f_282_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_282_, 0, v_text_279_);
lean_closure_set(v___f_282_, 1, v_inst_270_);
lean_closure_set(v___f_282_, 2, v___x_281_);
lean_closure_set(v___f_282_, 3, v_p_272_);
lean_closure_set(v___f_282_, 4, v_inst_273_);
lean_closure_set(v___f_282_, 5, v_inst_274_);
lean_closure_set(v___f_282_, 6, v_toApplicative_275_);
lean_closure_set(v___f_282_, 7, v_toBind_276_);
lean_closure_set(v___f_282_, 8, v_inst_277_);
lean_closure_set(v___f_282_, 9, v_s_278_);
v___x_283_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v_getEnv_280_, v___f_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg___lam__4___boxed(lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v___x_286_, lean_object* v_p_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_toApplicative_290_, lean_object* v_toBind_291_, lean_object* v_inst_292_, lean_object* v_s_293_, lean_object* v_text_294_){
_start:
{
uint8_t v___x_818__boxed_295_; lean_object* v_res_296_; 
v___x_818__boxed_295_ = lean_unbox(v___x_286_);
v_res_296_ = l_Lean_Doc_parseStrLit___redArg___lam__4(v_inst_284_, v_inst_285_, v___x_818__boxed_295_, v_p_287_, v_inst_288_, v_inst_289_, v_toApplicative_290_, v_toBind_291_, v_inst_292_, v_s_293_, v_text_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_p_303_, lean_object* v_s_304_){
_start:
{
uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_305_ = 1;
v___x_306_ = l_Lean_Syntax_getPos_x3f(v_s_304_, v___x_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_inst_298_);
v___x_307_ = l_Lean_TSyntax_getString(v_s_304_);
lean_dec(v_s_304_);
v___x_308_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_297_, v_inst_299_, v_inst_300_, v_inst_301_, v_inst_302_, v_p_303_, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v_toApplicative_309_; lean_object* v_toBind_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
lean_dec_ref_known(v___x_306_, 1);
v_toApplicative_309_ = lean_ctor_get(v_inst_297_, 0);
lean_inc_ref(v_toApplicative_309_);
v_toBind_310_ = lean_ctor_get(v_inst_297_, 1);
lean_inc_n(v_toBind_310_, 2);
v___x_311_ = lean_box(v___x_305_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_312_, 0, v_inst_299_);
lean_closure_set(v___f_312_, 1, v_inst_301_);
lean_closure_set(v___f_312_, 2, v___x_311_);
lean_closure_set(v___f_312_, 3, v_p_303_);
lean_closure_set(v___f_312_, 4, v_inst_297_);
lean_closure_set(v___f_312_, 5, v_inst_300_);
lean_closure_set(v___f_312_, 6, v_toApplicative_309_);
lean_closure_set(v___f_312_, 7, v_toBind_310_);
lean_closure_set(v___f_312_, 8, v_inst_302_);
lean_closure_set(v___f_312_, 9, v_s_304_);
v___x_313_ = lean_apply_4(v_toBind_310_, lean_box(0), lean_box(0), v_inst_298_, v___f_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_p_321_, lean_object* v_s_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Doc_parseStrLit___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_p_321_, v_s_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_343_; 
v_fst_326_ = lean_ctor_get(v_a_325_, 0);
v_snd_327_ = lean_ctor_get(v_a_325_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_325_);
if (v_isSharedCheck_343_ == 0)
{
v___x_329_ = v_a_325_;
v_isShared_330_ = v_isSharedCheck_343_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_inc(v_fst_326_);
lean_dec(v_a_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_343_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_nat_dec_lt(v___x_331_, v_fst_326_);
if (v___x_332_ == 0)
{
lean_object* v___x_334_; 
if (v_isShared_330_ == 0)
{
v___x_334_ = v___x_329_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_fst_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_snd_327_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_336_ = lean_string_utf8_prev(v_str_324_, v_fst_326_);
lean_dec(v_fst_326_);
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_add(v_snd_327_, v___x_337_);
lean_dec(v_snd_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_338_);
lean_ctor_set(v___x_329_, 0, v___x_336_);
v___x_340_ = v___x_329_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_342_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
v_a_325_ = v___x_340_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_344_, v_a_345_);
lean_dec_ref(v_str_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_347_, lean_object* v_p_348_){
_start:
{
lean_object* v_n_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_snd_352_; 
v_n_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_p_348_);
lean_ctor_set(v___x_350_, 1, v_n_349_);
v___x_351_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_347_, v___x_350_);
v_snd_352_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_snd_352_);
lean_dec_ref(v___x_351_);
return v_snd_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_353_, lean_object* v_p_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_353_, v_p_354_);
lean_dec_ref(v_str_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_356_, lean_object* v_inst_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_356_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_360_, lean_object* v_inst_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_360_, v_inst_361_, v_a_362_);
lean_dec_ref(v_str_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_364_, lean_object* v_p_365_, lean_object* v_j_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_zero_368_; uint8_t v_isZero_369_; 
v_zero_368_ = lean_unsigned_to_nat(0u);
v_isZero_369_ = lean_nat_dec_eq(v_j_366_, v_zero_368_);
if (v_isZero_369_ == 1)
{
lean_dec(v_j_366_);
return v_a_367_;
}
else
{
lean_object* v_one_370_; lean_object* v_n_371_; lean_object* v___x_372_; 
lean_dec(v_a_367_);
v_one_370_ = lean_unsigned_to_nat(1u);
v_n_371_ = lean_nat_sub(v_j_366_, v_one_370_);
lean_dec(v_j_366_);
v___x_372_ = lean_string_utf8_next(v_str_364_, v_p_365_);
v_j_366_ = v_n_371_;
v_a_367_ = v___x_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_374_, lean_object* v_p_375_, lean_object* v_j_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_374_, v_p_375_, v_j_376_, v_a_377_);
lean_dec(v_p_375_);
lean_dec_ref(v_str_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_379_, lean_object* v_n_380_, lean_object* v_p_381_){
_start:
{
lean_object* v___x_382_; 
lean_inc(v_p_381_);
v___x_382_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_379_, v_p_381_, v_n_380_, v_p_381_);
lean_dec(v_p_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_383_, lean_object* v_n_384_, lean_object* v_p_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_383_, v_n_384_, v_p_385_);
lean_dec_ref(v_str_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_387_, lean_object* v_p_388_, lean_object* v_n_389_, lean_object* v_j_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_387_, v_p_388_, v_j_390_, v_a_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_394_, lean_object* v_p_395_, lean_object* v_n_396_, lean_object* v_j_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_394_, v_p_395_, v_n_396_, v_j_397_, v_a_398_, v_a_399_);
lean_dec(v_n_396_);
lean_dec(v_p_395_);
lean_dec_ref(v_str_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_401_, lean_object* v_posOfStr_402_, lean_object* v_str_403_, lean_object* v_posInStr_404_){
_start:
{
lean_object* v_source_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_source_405_ = lean_ctor_get(v_text_401_, 0);
v___x_406_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_403_, v_posInStr_404_);
lean_inc(v_posOfStr_402_);
v___x_407_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_405_, v_posOfStr_402_, v___x_406_, v_posOfStr_402_);
lean_dec(v_posOfStr_402_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_408_, lean_object* v_posOfStr_409_, lean_object* v_str_410_, lean_object* v_posInStr_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_408_, v_posOfStr_409_, v_str_410_, v_posInStr_411_);
lean_dec_ref(v_str_410_);
lean_dec_ref(v_text_408_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_413_, lean_object* v_posOfStr_414_, lean_object* v_str_415_, lean_object* v_a_416_){
_start:
{
switch(lean_obj_tag(v_a_416_))
{
case 0:
{
lean_object* v_pos_417_; lean_object* v_endPos_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v_pos_417_ = lean_ctor_get(v_a_416_, 1);
lean_inc(v_pos_417_);
v_endPos_418_ = lean_ctor_get(v_a_416_, 3);
lean_inc(v_endPos_418_);
lean_dec_ref_known(v_a_416_, 4);
lean_inc(v_posOfStr_414_);
v___x_419_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_413_, v_posOfStr_414_, v_str_415_, v_pos_417_);
v___x_420_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_413_, v_posOfStr_414_, v_str_415_, v_endPos_418_);
v___x_421_ = 1;
v___x_422_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*2, v___x_421_);
return v___x_422_;
}
case 1:
{
lean_object* v_pos_423_; lean_object* v_endPos_424_; uint8_t v_canonical_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_434_; 
v_pos_423_ = lean_ctor_get(v_a_416_, 0);
v_endPos_424_ = lean_ctor_get(v_a_416_, 1);
v_canonical_425_ = lean_ctor_get_uint8(v_a_416_, sizeof(void*)*2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_427_ = v_a_416_;
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_endPos_424_);
lean_inc(v_pos_423_);
lean_dec(v_a_416_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_posOfStr_414_);
v___x_429_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_413_, v_posOfStr_414_, v_str_415_, v_pos_423_);
v___x_430_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_413_, v_posOfStr_414_, v_str_415_, v_endPos_424_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_430_);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*2, v_canonical_425_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
default: 
{
lean_dec(v_posOfStr_414_);
return v_a_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_435_, lean_object* v_posOfStr_436_, lean_object* v_str_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_435_, v_posOfStr_436_, v_str_437_, v_a_438_);
lean_dec_ref(v_str_437_);
lean_dec_ref(v_text_435_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_440_, lean_object* v_posOfStr_441_, lean_object* v_str_442_, lean_object* v_a_443_){
_start:
{
switch(lean_obj_tag(v_a_443_))
{
case 0:
{
lean_dec(v_posOfStr_441_);
return v_a_443_;
}
case 1:
{
lean_object* v_info_444_; lean_object* v_kind_445_; lean_object* v_args_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_457_; 
v_info_444_ = lean_ctor_get(v_a_443_, 0);
v_kind_445_ = lean_ctor_get(v_a_443_, 1);
v_args_446_ = lean_ctor_get(v_a_443_, 2);
v_isSharedCheck_457_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_457_ == 0)
{
v___x_448_ = v_a_443_;
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_args_446_);
lean_inc(v_kind_445_);
lean_inc(v_info_444_);
lean_dec(v_a_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; size_t v_sz_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_posOfStr_441_);
v___x_450_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_440_, v_posOfStr_441_, v_str_442_, v_info_444_);
v_sz_451_ = lean_array_size(v_args_446_);
v___x_452_ = ((size_t)0ULL);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_440_, v_posOfStr_441_, v_str_442_, v_sz_451_, v___x_452_, v_args_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_453_);
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_455_ = v___x_448_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_kind_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
case 2:
{
lean_object* v_info_458_; lean_object* v_val_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_info_458_ = lean_ctor_get(v_a_443_, 0);
v_val_459_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v_a_443_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_val_459_);
lean_inc(v_info_458_);
lean_dec(v_a_443_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_440_, v_posOfStr_441_, v_str_442_, v_info_458_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_val_459_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
default: 
{
lean_object* v_info_468_; lean_object* v_rawVal_469_; lean_object* v_val_470_; lean_object* v_preresolved_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
v_info_468_ = lean_ctor_get(v_a_443_, 0);
v_rawVal_469_ = lean_ctor_get(v_a_443_, 1);
v_val_470_ = lean_ctor_get(v_a_443_, 2);
v_preresolved_471_ = lean_ctor_get(v_a_443_, 3);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v_a_443_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_preresolved_471_);
lean_inc(v_val_470_);
lean_inc(v_rawVal_469_);
lean_inc(v_info_468_);
lean_dec(v_a_443_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_440_, v_posOfStr_441_, v_str_442_, v_info_468_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_rawVal_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_val_470_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_preresolved_471_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_480_, lean_object* v_posOfStr_481_, lean_object* v_str_482_, size_t v_sz_483_, size_t v_i_484_, lean_object* v_bs_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_484_, v_sz_483_);
if (v___x_486_ == 0)
{
lean_dec(v_posOfStr_481_);
return v_bs_485_;
}
else
{
lean_object* v_v_487_; lean_object* v___x_488_; lean_object* v_bs_x27_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_v_487_ = lean_array_uget(v_bs_485_, v_i_484_);
v___x_488_ = lean_unsigned_to_nat(0u);
v_bs_x27_489_ = lean_array_uset(v_bs_485_, v_i_484_, v___x_488_);
lean_inc(v_posOfStr_481_);
v___x_490_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_480_, v_posOfStr_481_, v_str_482_, v_v_487_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_484_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_489_, v_i_484_, v___x_490_);
v_i_484_ = v___x_492_;
v_bs_485_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_495_, lean_object* v_posOfStr_496_, lean_object* v_str_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_bs_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_495_, v_posOfStr_496_, v_str_497_, v_sz_boxed_501_, v_i_boxed_502_, v_bs_500_);
lean_dec_ref(v_str_497_);
lean_dec_ref(v_text_495_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_504_, lean_object* v_posOfStr_505_, lean_object* v_str_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_504_, v_posOfStr_505_, v_str_506_, v_a_507_);
lean_dec_ref(v_str_506_);
lean_dec_ref(v_text_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_, lean_object* v_h__3_512_, lean_object* v_h__4_513_){
_start:
{
switch(lean_obj_tag(v_x_509_))
{
case 0:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_h__3_512_);
lean_dec(v_h__2_511_);
lean_dec(v_h__1_510_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_1(v_h__4_513_, v___x_514_);
return v___x_515_;
}
case 1:
{
lean_object* v_info_516_; lean_object* v_kind_517_; lean_object* v_args_518_; lean_object* v___x_519_; 
lean_dec(v_h__4_513_);
lean_dec(v_h__3_512_);
lean_dec(v_h__2_511_);
v_info_516_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_info_516_);
v_kind_517_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_kind_517_);
v_args_518_ = lean_ctor_get(v_x_509_, 2);
lean_inc_ref(v_args_518_);
lean_dec_ref_known(v_x_509_, 3);
v___x_519_ = lean_apply_3(v_h__1_510_, v_info_516_, v_kind_517_, v_args_518_);
return v___x_519_;
}
case 2:
{
lean_object* v_info_520_; lean_object* v_val_521_; lean_object* v___x_522_; 
lean_dec(v_h__4_513_);
lean_dec(v_h__2_511_);
lean_dec(v_h__1_510_);
v_info_520_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_info_520_);
v_val_521_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_val_521_);
lean_dec_ref_known(v_x_509_, 2);
v___x_522_ = lean_apply_2(v_h__3_512_, v_info_520_, v_val_521_);
return v___x_522_;
}
default: 
{
lean_object* v_info_523_; lean_object* v_rawVal_524_; lean_object* v_val_525_; lean_object* v_preresolved_526_; lean_object* v___x_527_; 
lean_dec(v_h__4_513_);
lean_dec(v_h__3_512_);
lean_dec(v_h__1_510_);
v_info_523_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_info_523_);
v_rawVal_524_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_rawVal_524_);
v_val_525_ = lean_ctor_get(v_x_509_, 2);
lean_inc(v_val_525_);
v_preresolved_526_ = lean_ctor_get(v_x_509_, 3);
lean_inc(v_preresolved_526_);
lean_dec_ref_known(v_x_509_, 4);
v___x_527_ = lean_apply_4(v_h__2_511_, v_info_523_, v_rawVal_524_, v_val_525_, v_preresolved_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_528_, lean_object* v_x_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_, lean_object* v_h__3_532_, lean_object* v_h__4_533_){
_start:
{
switch(lean_obj_tag(v_x_529_))
{
case 0:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_h__3_532_);
lean_dec(v_h__2_531_);
lean_dec(v_h__1_530_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_apply_1(v_h__4_533_, v___x_534_);
return v___x_535_;
}
case 1:
{
lean_object* v_info_536_; lean_object* v_kind_537_; lean_object* v_args_538_; lean_object* v___x_539_; 
lean_dec(v_h__4_533_);
lean_dec(v_h__3_532_);
lean_dec(v_h__2_531_);
v_info_536_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_info_536_);
v_kind_537_ = lean_ctor_get(v_x_529_, 1);
lean_inc(v_kind_537_);
v_args_538_ = lean_ctor_get(v_x_529_, 2);
lean_inc_ref(v_args_538_);
lean_dec_ref_known(v_x_529_, 3);
v___x_539_ = lean_apply_3(v_h__1_530_, v_info_536_, v_kind_537_, v_args_538_);
return v___x_539_;
}
case 2:
{
lean_object* v_info_540_; lean_object* v_val_541_; lean_object* v___x_542_; 
lean_dec(v_h__4_533_);
lean_dec(v_h__2_531_);
lean_dec(v_h__1_530_);
v_info_540_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_info_540_);
v_val_541_ = lean_ctor_get(v_x_529_, 1);
lean_inc_ref(v_val_541_);
lean_dec_ref_known(v_x_529_, 2);
v___x_542_ = lean_apply_2(v_h__3_532_, v_info_540_, v_val_541_);
return v___x_542_;
}
default: 
{
lean_object* v_info_543_; lean_object* v_rawVal_544_; lean_object* v_val_545_; lean_object* v_preresolved_546_; lean_object* v___x_547_; 
lean_dec(v_h__4_533_);
lean_dec(v_h__3_532_);
lean_dec(v_h__1_530_);
v_info_543_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_info_543_);
v_rawVal_544_ = lean_ctor_get(v_x_529_, 1);
lean_inc_ref(v_rawVal_544_);
v_val_545_ = lean_ctor_get(v_x_529_, 2);
lean_inc(v_val_545_);
v_preresolved_546_ = lean_ctor_get(v_x_529_, 3);
lean_inc(v_preresolved_546_);
lean_dec_ref_known(v_x_529_, 4);
v___x_547_ = lean_apply_4(v_h__2_531_, v_info_543_, v_rawVal_544_, v_val_545_, v_preresolved_546_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_548_, lean_object* v_h__1_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_apply_2(v_h__1_549_, v_x_548_, lean_box(0));
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_551_, lean_object* v_P_552_, lean_object* v_motive_553_, lean_object* v_x_554_, lean_object* v_h__1_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_apply_2(v_h__1_555_, v_x_554_, lean_box(0));
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_text_557_, lean_object* v_pos_558_, lean_object* v_str_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_fst_561_ = lean_ctor_get(v_x_560_, 0);
v_snd_562_ = lean_ctor_get(v_x_560_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_x_560_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_inc(v_fst_561_);
lean_dec(v_x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_557_, v_pos_558_, v_str_559_, v_fst_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_562_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed(lean_object* v_text_571_, lean_object* v_pos_572_, lean_object* v_str_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(v_text_571_, v_pos_572_, v_str_573_, v_x_574_);
lean_dec_ref(v_str_573_);
lean_dec_ref(v_text_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_env_595_, lean_object* v_p_596_, lean_object* v_ictx_597_, lean_object* v_s_598_, lean_object* v_text_599_, lean_object* v_pos_600_, lean_object* v_str_601_, lean_object* v___f_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_toApplicative_605_, lean_object* v_____do__lift_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_s_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_box(0);
lean_inc_ref(v_env_595_);
v___x_609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_609_, 0, v_env_595_);
lean_ctor_set(v___x_609_, 1, v_____do__lift_606_);
lean_ctor_set(v___x_609_, 2, v___x_607_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
v___x_610_ = l_Lean_Parser_getTokenTable(v_env_595_);
lean_inc_ref(v_ictx_597_);
v_s_611_ = l_Lean_Parser_ParserFn_run(v_p_596_, v_ictx_597_, v___x_609_, v___x_610_, v_s_598_);
lean_inc_ref(v_s_611_);
v___x_612_ = l_Lean_Parser_ParserState_allErrors(v_s_611_);
v___x_613_ = lean_array_get_size(v___x_612_);
lean_dec_ref(v___x_612_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v_stxStack_616_; lean_object* v_lhsPrec_617_; lean_object* v_pos_618_; lean_object* v_cache_619_; lean_object* v_errorMsg_620_; lean_object* v_recoveredErrors_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_toApplicative_605_);
v_stxStack_616_ = lean_ctor_get(v_s_611_, 0);
v_lhsPrec_617_ = lean_ctor_get(v_s_611_, 1);
v_pos_618_ = lean_ctor_get(v_s_611_, 2);
v_cache_619_ = lean_ctor_get(v_s_611_, 3);
v_errorMsg_620_ = lean_ctor_get(v_s_611_, 4);
v_recoveredErrors_621_ = lean_ctor_get(v_s_611_, 5);
v_isSharedCheck_658_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_658_ == 0)
{
v___x_623_ = v_s_611_;
v_isShared_624_ = v_isSharedCheck_658_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_recoveredErrors_621_);
lean_inc(v_errorMsg_620_);
lean_inc(v_cache_619_);
lean_inc(v_pos_618_);
lean_inc(v_lhsPrec_617_);
lean_inc(v_stxStack_616_);
lean_dec(v_s_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_658_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___y_627_; 
lean_inc(v_pos_600_);
v___x_625_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_599_, v_pos_600_, v_str_601_, v_pos_618_);
if (lean_obj_tag(v_errorMsg_620_) == 0)
{
lean_dec(v_pos_600_);
v___y_627_ = v_errorMsg_620_;
goto v___jp_626_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_657_; 
v_val_639_ = lean_ctor_get(v_errorMsg_620_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_errorMsg_620_);
if (v_isSharedCheck_657_ == 0)
{
v___x_641_ = v_errorMsg_620_;
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v_errorMsg_620_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_unexpectedTk_643_; lean_object* v_unexpected_644_; lean_object* v_expected_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_656_; 
v_unexpectedTk_643_ = lean_ctor_get(v_val_639_, 0);
v_unexpected_644_ = lean_ctor_get(v_val_639_, 1);
v_expected_645_ = lean_ctor_get(v_val_639_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_val_639_);
if (v_isSharedCheck_656_ == 0)
{
v___x_647_ = v_val_639_;
v_isShared_648_ = v_isSharedCheck_656_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_expected_645_);
lean_inc(v_unexpected_644_);
lean_inc(v_unexpectedTk_643_);
lean_dec(v_val_639_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_656_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_599_, v_pos_600_, v_str_601_, v_unexpectedTk_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_unexpected_644_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_expected_645_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_651_);
v___x_653_ = v___x_641_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v___y_627_ = v___x_653_;
goto v___jp_626_;
}
}
}
}
}
v___jp_626_:
{
lean_object* v___x_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v___x_631_; lean_object* v_s_633_; 
v___x_628_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___closed__9));
v_sz_629_ = lean_array_size(v_recoveredErrors_621_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_628_, v___f_602_, v_sz_629_, v___x_630_, v_recoveredErrors_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 5, v___x_631_);
lean_ctor_set(v___x_623_, 4, v___y_627_);
lean_ctor_set(v___x_623_, 2, v___x_625_);
v_s_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_stxStack_616_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_lhsPrec_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_cache_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v___y_627_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v___x_631_);
v_s_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_597_, v_s_633_);
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = l_Lean_MessageData_ofFormat(v___x_635_);
v___x_637_ = l_Lean_throwError___redArg(v_inst_603_, v_inst_604_, v___x_636_);
return v___x_637_;
}
}
}
}
else
{
lean_object* v_stxStack_659_; lean_object* v_pos_660_; uint8_t v___x_661_; 
lean_dec_ref(v___f_602_);
v_stxStack_659_ = lean_ctor_get(v_s_611_, 0);
lean_inc_ref(v_stxStack_659_);
v_pos_660_ = lean_ctor_get(v_s_611_, 2);
lean_inc(v_pos_660_);
v___x_661_ = l_Lean_Parser_InputContext_atEnd(v_ictx_597_, v_pos_660_);
lean_dec(v_pos_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_stxStack_659_);
lean_dec_ref(v_toApplicative_605_);
lean_dec(v_pos_600_);
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_663_ = l_Lean_Parser_ParserState_mkError(v_s_611_, v___x_662_);
v___x_664_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_597_, v___x_663_);
v___x_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___x_666_ = l_Lean_MessageData_ofFormat(v___x_665_);
v___x_667_ = l_Lean_throwError___redArg(v_inst_603_, v_inst_604_, v___x_666_);
return v___x_667_;
}
else
{
lean_object* v_toPure_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_s_611_);
lean_dec_ref(v_inst_604_);
lean_dec_ref(v_inst_603_);
lean_dec_ref(v_ictx_597_);
v_toPure_668_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc(v_toPure_668_);
lean_dec_ref(v_toApplicative_605_);
v___x_669_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_659_);
lean_dec_ref(v_stxStack_659_);
v___x_670_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_599_, v_pos_600_, v_str_601_, v___x_669_);
v___x_671_ = lean_apply_2(v_toPure_668_, lean_box(0), v___x_670_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_env_672_, lean_object* v_p_673_, lean_object* v_ictx_674_, lean_object* v_s_675_, lean_object* v_text_676_, lean_object* v_pos_677_, lean_object* v_str_678_, lean_object* v___f_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_toApplicative_682_, lean_object* v_____do__lift_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_env_672_, v_p_673_, v_ictx_674_, v_s_675_, v_text_676_, v_pos_677_, v_str_678_, v___f_679_, v_inst_680_, v_inst_681_, v_toApplicative_682_, v_____do__lift_683_);
lean_dec_ref(v_str_678_);
lean_dec_ref(v_text_676_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_str_685_, uint8_t v___x_686_, lean_object* v_env_687_, lean_object* v_p_688_, lean_object* v_text_689_, lean_object* v_pos_690_, lean_object* v___f_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_toApplicative_694_, lean_object* v_toBind_695_, lean_object* v_inst_696_, lean_object* v_____do__lift_697_){
_start:
{
lean_object* v___x_698_; lean_object* v_ictx_699_; lean_object* v_s_700_; lean_object* v___f_701_; lean_object* v___x_702_; 
v___x_698_ = lean_string_utf8_byte_size(v_str_685_);
lean_inc_ref(v_str_685_);
v_ictx_699_ = l_Lean_Parser_mkInputContext___redArg(v_str_685_, v_____do__lift_697_, v___x_686_, v___x_698_);
v_s_700_ = l_Lean_Parser_mkParserState(v_str_685_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_701_, 0, v_env_687_);
lean_closure_set(v___f_701_, 1, v_p_688_);
lean_closure_set(v___f_701_, 2, v_ictx_699_);
lean_closure_set(v___f_701_, 3, v_s_700_);
lean_closure_set(v___f_701_, 4, v_text_689_);
lean_closure_set(v___f_701_, 5, v_pos_690_);
lean_closure_set(v___f_701_, 6, v_str_685_);
lean_closure_set(v___f_701_, 7, v___f_691_);
lean_closure_set(v___f_701_, 8, v_inst_692_);
lean_closure_set(v___f_701_, 9, v_inst_693_);
lean_closure_set(v___f_701_, 10, v_toApplicative_694_);
v___x_702_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v_inst_696_, v___f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_str_703_, lean_object* v___x_704_, lean_object* v_env_705_, lean_object* v_p_706_, lean_object* v_text_707_, lean_object* v_pos_708_, lean_object* v___f_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_toApplicative_712_, lean_object* v_toBind_713_, lean_object* v_inst_714_, lean_object* v_____do__lift_715_){
_start:
{
uint8_t v___x_1990__boxed_716_; lean_object* v_res_717_; 
v___x_1990__boxed_716_ = lean_unbox(v___x_704_);
v_res_717_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_str_703_, v___x_1990__boxed_716_, v_env_705_, v_p_706_, v_text_707_, v_pos_708_, v___f_709_, v_inst_710_, v_inst_711_, v_toApplicative_712_, v_toBind_713_, v_inst_714_, v_____do__lift_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_inst_718_, lean_object* v_strLit_719_, lean_object* v_text_720_, uint8_t v___x_721_, lean_object* v_env_722_, lean_object* v_p_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_toApplicative_726_, lean_object* v_toBind_727_, lean_object* v_inst_728_, lean_object* v_pos_729_){
_start:
{
lean_object* v_getFileName_730_; lean_object* v_str_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; 
v_getFileName_730_ = lean_ctor_get(v_inst_718_, 2);
lean_inc(v_getFileName_730_);
lean_dec_ref(v_inst_718_);
v_str_731_ = l_Lean_TSyntax_getString(v_strLit_719_);
lean_inc_ref(v_str_731_);
lean_inc(v_pos_729_);
lean_inc_ref(v_text_720_);
v___f_732_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_732_, 0, v_text_720_);
lean_closure_set(v___f_732_, 1, v_pos_729_);
lean_closure_set(v___f_732_, 2, v_str_731_);
v___x_733_ = lean_box(v___x_721_);
lean_inc(v_toBind_727_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 13, 12);
lean_closure_set(v___f_734_, 0, v_str_731_);
lean_closure_set(v___f_734_, 1, v___x_733_);
lean_closure_set(v___f_734_, 2, v_env_722_);
lean_closure_set(v___f_734_, 3, v_p_723_);
lean_closure_set(v___f_734_, 4, v_text_720_);
lean_closure_set(v___f_734_, 5, v_pos_729_);
lean_closure_set(v___f_734_, 6, v___f_732_);
lean_closure_set(v___f_734_, 7, v_inst_724_);
lean_closure_set(v___f_734_, 8, v_inst_725_);
lean_closure_set(v___f_734_, 9, v_toApplicative_726_);
lean_closure_set(v___f_734_, 10, v_toBind_727_);
lean_closure_set(v___f_734_, 11, v_inst_728_);
v___x_735_ = lean_apply_4(v_toBind_727_, lean_box(0), lean_box(0), v_getFileName_730_, v___f_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_inst_736_, lean_object* v_strLit_737_, lean_object* v_text_738_, lean_object* v___x_739_, lean_object* v_env_740_, lean_object* v_p_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_toApplicative_744_, lean_object* v_toBind_745_, lean_object* v_inst_746_, lean_object* v_pos_747_){
_start:
{
uint8_t v___x_2015__boxed_748_; lean_object* v_res_749_; 
v___x_2015__boxed_748_ = lean_unbox(v___x_739_);
v_res_749_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_inst_736_, v_strLit_737_, v_text_738_, v___x_2015__boxed_748_, v_env_740_, v_p_741_, v_inst_742_, v_inst_743_, v_toApplicative_744_, v_toBind_745_, v_inst_746_, v_pos_747_);
lean_dec(v_strLit_737_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v___f_750_, lean_object* v_pos_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_apply_1(v___f_750_, v_pos_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__0));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v_text_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_strLit_759_, lean_object* v_toBind_760_, lean_object* v___f_761_, lean_object* v_toApplicative_762_, lean_object* v___f_763_, lean_object* v_____r_764_, lean_object* v_pos_765_){
_start:
{
lean_object* v_source_766_; uint32_t v___x_767_; uint32_t v___x_768_; uint8_t v___x_769_; 
v_source_766_ = lean_ctor_get(v_text_756_, 0);
v___x_767_ = lean_string_utf8_get(v_source_766_, v_pos_765_);
v___x_768_ = 34;
v___x_769_ = lean_uint32_dec_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v___f_763_);
lean_dec_ref(v_toApplicative_762_);
v___x_770_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___closed__1);
v___x_771_ = l_Lean_throwErrorAt___redArg(v_inst_757_, v_inst_758_, v_strLit_759_, v___x_770_);
v___x_772_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_771_, v___f_761_);
return v___x_772_;
}
else
{
lean_object* v_toPure_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v___f_761_);
lean_dec(v_strLit_759_);
lean_dec_ref(v_inst_758_);
lean_dec_ref(v_inst_757_);
v_toPure_773_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_inc(v_toPure_773_);
lean_dec_ref(v_toApplicative_762_);
v___x_774_ = lean_string_utf8_next(v_source_766_, v_pos_765_);
v___x_775_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_774_);
v___x_776_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_775_, v___f_763_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed(lean_object* v_text_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_strLit_780_, lean_object* v_toBind_781_, lean_object* v___f_782_, lean_object* v_toApplicative_783_, lean_object* v___f_784_, lean_object* v_____r_785_, lean_object* v_pos_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(v_text_777_, v_inst_778_, v_inst_779_, v_strLit_780_, v_toBind_781_, v___f_782_, v_toApplicative_783_, v___f_784_, v_____r_785_, v_pos_786_);
lean_dec(v_pos_786_);
lean_dec_ref(v_text_777_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_788_, lean_object* v_____s_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_box(0);
v___x_791_ = lean_apply_2(v___f_788_, v___x_790_, v_____s_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_toPure_792_, lean_object* v_____do__lift_793_){
_start:
{
if (lean_obj_tag(v_____do__lift_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_a_794_ = lean_ctor_get(v_____do__lift_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_____do__lift_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v_____do__lift_793_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v_____do__lift_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 1);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_799_);
return v___x_800_;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_a_803_ = lean_ctor_get(v_____do__lift_793_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_____do__lift_793_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v_____do__lift_793_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v_____do__lift_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 0);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_808_);
return v___x_809_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_833_, lean_object* v___f_834_, lean_object* v_toApplicative_835_, lean_object* v_toBind_836_, lean_object* v_inst_837_, lean_object* v___f_838_, lean_object* v_____x_839_){
_start:
{
lean_object* v_start_840_; lean_object* v_source_841_; uint32_t v___x_842_; uint32_t v___x_843_; uint8_t v___x_844_; 
v_start_840_ = lean_ctor_get(v_____x_839_, 0);
lean_inc(v_start_840_);
lean_dec_ref(v_____x_839_);
v_source_841_ = lean_ctor_get(v_text_833_, 0);
lean_inc_ref(v_source_841_);
lean_dec_ref(v_text_833_);
v___x_842_ = lean_string_utf8_get(v_source_841_, v_start_840_);
v___x_843_ = 114;
v___x_844_ = lean_uint32_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_source_841_);
lean_dec(v___f_838_);
lean_dec_ref(v_inst_837_);
lean_dec(v_toBind_836_);
lean_dec_ref(v_toApplicative_835_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_2(v___f_834_, v___x_845_, v_start_840_);
return v___x_846_;
}
else
{
lean_object* v_toPure_847_; lean_object* v_pos_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___f_834_);
v_toPure_847_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_inc_n(v_toPure_847_, 2);
lean_dec_ref(v_toApplicative_835_);
v_pos_848_ = lean_string_utf8_next(v_source_841_, v_start_840_);
lean_dec(v_start_840_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7), 2, 1);
lean_closure_set(v___f_849_, 0, v_toPure_847_);
lean_inc(v_toBind_836_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_850_, 0, v_source_841_);
lean_closure_set(v___f_850_, 1, v_toPure_847_);
lean_closure_set(v___f_850_, 2, v_toBind_836_);
lean_closure_set(v___f_850_, 3, v___f_849_);
v___x_851_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_837_, v___f_850_, v_pos_848_);
v___x_852_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_851_, v___f_838_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_853_, lean_object* v_strLit_854_, lean_object* v_text_855_, uint8_t v___x_856_, lean_object* v_p_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_toApplicative_860_, lean_object* v_toBind_861_, lean_object* v_inst_862_, lean_object* v_env_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_864_ = lean_box(v___x_856_);
lean_inc_n(v_toBind_861_, 3);
lean_inc_ref_n(v_toApplicative_860_, 2);
lean_inc_ref(v_inst_859_);
lean_inc_ref_n(v_inst_858_, 3);
lean_inc_ref_n(v_text_855_, 2);
lean_inc_n(v_strLit_854_, 2);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_865_, 0, v_inst_853_);
lean_closure_set(v___f_865_, 1, v_strLit_854_);
lean_closure_set(v___f_865_, 2, v_text_855_);
lean_closure_set(v___f_865_, 3, v___x_864_);
lean_closure_set(v___f_865_, 4, v_env_863_);
lean_closure_set(v___f_865_, 5, v_p_857_);
lean_closure_set(v___f_865_, 6, v_inst_858_);
lean_closure_set(v___f_865_, 7, v_inst_859_);
lean_closure_set(v___f_865_, 8, v_toApplicative_860_);
lean_closure_set(v___f_865_, 9, v_toBind_861_);
lean_closure_set(v___f_865_, 10, v_inst_862_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4), 2, 1);
lean_closure_set(v___f_866_, 0, v___f_865_);
lean_inc_ref(v___f_866_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6___boxed), 10, 8);
lean_closure_set(v___f_867_, 0, v_text_855_);
lean_closure_set(v___f_867_, 1, v_inst_858_);
lean_closure_set(v___f_867_, 2, v_inst_859_);
lean_closure_set(v___f_867_, 3, v_strLit_854_);
lean_closure_set(v___f_867_, 4, v_toBind_861_);
lean_closure_set(v___f_867_, 5, v___f_866_);
lean_closure_set(v___f_867_, 6, v_toApplicative_860_);
lean_closure_set(v___f_867_, 7, v___f_866_);
lean_inc_ref(v___f_867_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_868_, 0, v___f_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 7, 6);
lean_closure_set(v___f_869_, 0, v_text_855_);
lean_closure_set(v___f_869_, 1, v___f_867_);
lean_closure_set(v___f_869_, 2, v_toApplicative_860_);
lean_closure_set(v___f_869_, 3, v_toBind_861_);
lean_closure_set(v___f_869_, 4, v_inst_858_);
lean_closure_set(v___f_869_, 5, v___f_868_);
v___x_870_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_858_, v_strLit_854_);
lean_dec(v_strLit_854_);
v___x_871_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v___x_870_, v___f_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_872_, lean_object* v_strLit_873_, lean_object* v_text_874_, lean_object* v___x_875_, lean_object* v_p_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_toApplicative_879_, lean_object* v_toBind_880_, lean_object* v_inst_881_, lean_object* v_env_882_){
_start:
{
uint8_t v___x_2181__boxed_883_; lean_object* v_res_884_; 
v___x_2181__boxed_883_ = lean_unbox(v___x_875_);
v_res_884_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_872_, v_strLit_873_, v_text_874_, v___x_2181__boxed_883_, v_p_876_, v_inst_877_, v_inst_878_, v_toApplicative_879_, v_toBind_880_, v_inst_881_, v_env_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_strLit_887_, uint8_t v___x_888_, lean_object* v_p_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_toApplicative_892_, lean_object* v_toBind_893_, lean_object* v_inst_894_, lean_object* v_text_895_){
_start:
{
lean_object* v_getEnv_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; 
v_getEnv_896_ = lean_ctor_get(v_inst_885_, 0);
lean_inc(v_getEnv_896_);
lean_dec_ref(v_inst_885_);
v___x_897_ = lean_box(v___x_888_);
lean_inc(v_toBind_893_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_898_, 0, v_inst_886_);
lean_closure_set(v___f_898_, 1, v_strLit_887_);
lean_closure_set(v___f_898_, 2, v_text_895_);
lean_closure_set(v___f_898_, 3, v___x_897_);
lean_closure_set(v___f_898_, 4, v_p_889_);
lean_closure_set(v___f_898_, 5, v_inst_890_);
lean_closure_set(v___f_898_, 6, v_inst_891_);
lean_closure_set(v___f_898_, 7, v_toApplicative_892_);
lean_closure_set(v___f_898_, 8, v_toBind_893_);
lean_closure_set(v___f_898_, 9, v_inst_894_);
v___x_899_ = lean_apply_4(v_toBind_893_, lean_box(0), lean_box(0), v_getEnv_896_, v___f_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_strLit_902_, lean_object* v___x_903_, lean_object* v_p_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_toApplicative_907_, lean_object* v_toBind_908_, lean_object* v_inst_909_, lean_object* v_text_910_){
_start:
{
uint8_t v___x_2213__boxed_911_; lean_object* v_res_912_; 
v___x_2213__boxed_911_ = lean_unbox(v___x_903_);
v_res_912_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_900_, v_inst_901_, v_strLit_902_, v___x_2213__boxed_911_, v_p_904_, v_inst_905_, v_inst_906_, v_toApplicative_907_, v_toBind_908_, v_inst_909_, v_text_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_p_919_, lean_object* v_strLit_920_){
_start:
{
uint8_t v___x_921_; lean_object* v___x_922_; 
v___x_921_ = 1;
v___x_922_ = l_Lean_Syntax_getPos_x3f(v_strLit_920_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_inst_914_);
v___x_923_ = l_Lean_TSyntax_getString(v_strLit_920_);
lean_dec(v_strLit_920_);
v___x_924_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_913_, v_inst_915_, v_inst_916_, v_inst_917_, v_inst_918_, v_p_919_, v___x_923_);
return v___x_924_;
}
else
{
lean_object* v_toApplicative_925_; lean_object* v_toBind_926_; lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___x_929_; 
lean_dec_ref_known(v___x_922_, 1);
v_toApplicative_925_ = lean_ctor_get(v_inst_913_, 0);
lean_inc_ref(v_toApplicative_925_);
v_toBind_926_ = lean_ctor_get(v_inst_913_, 1);
lean_inc_n(v_toBind_926_, 2);
v___x_927_ = lean_box(v___x_921_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 11, 10);
lean_closure_set(v___f_928_, 0, v_inst_915_);
lean_closure_set(v___f_928_, 1, v_inst_917_);
lean_closure_set(v___f_928_, 2, v_strLit_920_);
lean_closure_set(v___f_928_, 3, v___x_927_);
lean_closure_set(v___f_928_, 4, v_p_919_);
lean_closure_set(v___f_928_, 5, v_inst_913_);
lean_closure_set(v___f_928_, 6, v_inst_916_);
lean_closure_set(v___f_928_, 7, v_toApplicative_925_);
lean_closure_set(v___f_928_, 8, v_toBind_926_);
lean_closure_set(v___f_928_, 9, v_inst_918_);
v___x_929_ = lean_apply_4(v_toBind_926_, lean_box(0), lean_box(0), v_inst_914_, v___f_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_p_937_, lean_object* v_strLit_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_931_, v_inst_932_, v_inst_933_, v_inst_934_, v_inst_935_, v_inst_936_, v_p_937_, v_strLit_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0(lean_object* v_toApplicative_940_, lean_object* v_st_941_, uint8_t v_err_942_){
_start:
{
lean_object* v_toPure_943_; lean_object* v_stxStack_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_toPure_943_ = lean_ctor_get(v_toApplicative_940_, 1);
lean_inc(v_toPure_943_);
lean_dec_ref(v_toApplicative_940_);
v_stxStack_944_ = lean_ctor_get(v_st_941_, 0);
v___x_945_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_944_);
v___x_946_ = lean_box(v_err_942_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_apply_2(v_toPure_943_, lean_box(0), v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_949_, lean_object* v_st_950_, lean_object* v_err_951_){
_start:
{
uint8_t v_err_boxed_952_; lean_object* v_res_953_; 
v_err_boxed_952_ = lean_unbox(v_err_951_);
v_res_953_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__0(v_toApplicative_949_, v_st_950_, v_err_boxed_952_);
lean_dec_ref(v_st_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1(lean_object* v___f_954_, uint8_t v_err_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_box(v_err_955_);
v___x_957_ = lean_apply_1(v___f_954_, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed(lean_object* v___f_958_, lean_object* v_err_959_){
_start:
{
uint8_t v_err_boxed_960_; lean_object* v_res_961_; 
v_err_boxed_960_ = lean_unbox(v_err_959_);
v_res_961_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__1(v___f_958_, v_err_boxed_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2(lean_object* v_toApplicative_962_, uint8_t v___x_963_, lean_object* v_toBind_964_, lean_object* v___f_965_, lean_object* v_____r_966_){
_start:
{
lean_object* v_toPure_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_toPure_967_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc(v_toPure_967_);
lean_dec_ref(v_toApplicative_962_);
v___x_968_ = lean_box(v___x_963_);
v___x_969_ = lean_apply_2(v_toPure_967_, lean_box(0), v___x_968_);
v___x_970_ = lean_apply_4(v_toBind_964_, lean_box(0), lean_box(0), v___x_969_, v___f_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_971_, lean_object* v___x_972_, lean_object* v_toBind_973_, lean_object* v___f_974_, lean_object* v_____r_975_){
_start:
{
uint8_t v___x_1940__boxed_976_; lean_object* v_res_977_; 
v___x_1940__boxed_976_ = lean_unbox(v___x_972_);
v_res_977_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__2(v_toApplicative_971_, v___x_1940__boxed_976_, v_toBind_973_, v___f_974_, v_____r_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6(lean_object* v_env_978_, lean_object* v_contents_979_, lean_object* v_p_980_, lean_object* v_ictx_981_, lean_object* v_toApplicative_982_, uint8_t v___x_983_, lean_object* v_toBind_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_____do__lift_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_st_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_990_ = lean_box(0);
v___x_991_ = lean_box(0);
lean_inc_ref(v_env_978_);
v___x_992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_992_, 0, v_env_978_);
lean_ctor_set(v___x_992_, 1, v_____do__lift_989_);
lean_ctor_set(v___x_992_, 2, v___x_990_);
lean_ctor_set(v___x_992_, 3, v___x_991_);
v___x_993_ = l_Lean_Parser_getTokenTable(v_env_978_);
v___x_994_ = l_Lean_Parser_mkParserState(v_contents_979_);
lean_inc_ref(v_ictx_981_);
v_st_995_ = l_Lean_Parser_ParserFn_run(v_p_980_, v_ictx_981_, v___x_992_, v___x_993_, v___x_994_);
lean_inc_ref_n(v_st_995_, 2);
lean_inc_ref(v_toApplicative_982_);
v___f_996_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_996_, 0, v_toApplicative_982_);
lean_closure_set(v___f_996_, 1, v_st_995_);
v___x_997_ = l_Lean_Parser_ParserState_allErrors(v_st_995_);
v___x_998_ = lean_array_get_size(v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_nat_dec_eq(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1001_, 0, v___f_996_);
v___x_1002_ = lean_box(v___x_983_);
lean_inc(v_toBind_984_);
v___f_1003_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1003_, 0, v_toApplicative_982_);
lean_closure_set(v___f_1003_, 1, v___x_1002_);
lean_closure_set(v___f_1003_, 2, v_toBind_984_);
lean_closure_set(v___f_1003_, 3, v___f_1001_);
v___x_1004_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_981_, v_st_995_);
v___x_1005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = l_Lean_MessageData_ofFormat(v___x_1005_);
v___x_1007_ = l_Lean_logError___redArg(v_inst_985_, v_inst_986_, v_inst_987_, v_inst_988_, v___x_1006_);
v___x_1008_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_1007_, v___f_1003_);
return v___x_1008_;
}
else
{
lean_object* v_pos_1009_; uint8_t v___x_1010_; 
v_pos_1009_ = lean_ctor_get(v_st_995_, 2);
lean_inc(v_pos_1009_);
v___x_1010_ = l_Lean_Parser_InputContext_atEnd(v_ictx_981_, v_pos_1009_);
lean_dec(v_pos_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1011_, 0, v___f_996_);
v___x_1012_ = lean_box(v___x_983_);
lean_inc(v_toBind_984_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1013_, 0, v_toApplicative_982_);
lean_closure_set(v___f_1013_, 1, v___x_1012_);
lean_closure_set(v___f_1013_, 2, v_toBind_984_);
lean_closure_set(v___f_1013_, 3, v___f_1011_);
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1015_ = l_Lean_Parser_ParserState_mkError(v_st_995_, v___x_1014_);
v___x_1016_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_981_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
v___x_1019_ = l_Lean_logError___redArg(v_inst_985_, v_inst_986_, v_inst_987_, v_inst_988_, v___x_1018_);
v___x_1020_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_1019_, v___f_1013_);
return v___x_1020_;
}
else
{
lean_object* v_toPure_1021_; lean_object* v___f_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref(v_st_995_);
lean_dec(v_inst_988_);
lean_dec(v_inst_987_);
lean_dec_ref(v_inst_986_);
lean_dec_ref(v_inst_985_);
lean_dec_ref(v_ictx_981_);
v_toPure_1021_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_inc(v_toPure_1021_);
lean_dec_ref(v_toApplicative_982_);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1022_, 0, v___f_996_);
v___x_1023_ = 0;
v___x_1024_ = lean_box(v___x_1023_);
v___x_1025_ = lean_apply_2(v_toPure_1021_, lean_box(0), v___x_1024_);
v___x_1026_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_1025_, v___f_1022_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed(lean_object* v_env_1027_, lean_object* v_contents_1028_, lean_object* v_p_1029_, lean_object* v_ictx_1030_, lean_object* v_toApplicative_1031_, lean_object* v___x_1032_, lean_object* v_toBind_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_____do__lift_1038_){
_start:
{
uint8_t v___x_1956__boxed_1039_; lean_object* v_res_1040_; 
v___x_1956__boxed_1039_ = lean_unbox(v___x_1032_);
v_res_1040_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__6(v_env_1027_, v_contents_1028_, v_p_1029_, v_ictx_1030_, v_toApplicative_1031_, v___x_1956__boxed_1039_, v_toBind_1033_, v_inst_1034_, v_inst_1035_, v_inst_1036_, v_inst_1037_, v_____do__lift_1038_);
lean_dec_ref(v_contents_1028_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3(lean_object* v_contents_1041_, uint8_t v___x_1042_, lean_object* v_env_1043_, lean_object* v_p_1044_, lean_object* v_toApplicative_1045_, lean_object* v_toBind_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_____do__lift_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v_ictx_1053_; lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; 
v___x_1052_ = lean_string_utf8_byte_size(v_contents_1041_);
lean_inc_ref(v_contents_1041_);
v_ictx_1053_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1041_, v_____do__lift_1051_, v___x_1042_, v___x_1052_);
v___x_1054_ = lean_box(v___x_1042_);
lean_inc(v_inst_1050_);
lean_inc(v_toBind_1046_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_1055_, 0, v_env_1043_);
lean_closure_set(v___f_1055_, 1, v_contents_1041_);
lean_closure_set(v___f_1055_, 2, v_p_1044_);
lean_closure_set(v___f_1055_, 3, v_ictx_1053_);
lean_closure_set(v___f_1055_, 4, v_toApplicative_1045_);
lean_closure_set(v___f_1055_, 5, v___x_1054_);
lean_closure_set(v___f_1055_, 6, v_toBind_1046_);
lean_closure_set(v___f_1055_, 7, v_inst_1047_);
lean_closure_set(v___f_1055_, 8, v_inst_1048_);
lean_closure_set(v___f_1055_, 9, v_inst_1049_);
lean_closure_set(v___f_1055_, 10, v_inst_1050_);
v___x_1056_ = lean_apply_4(v_toBind_1046_, lean_box(0), lean_box(0), v_inst_1050_, v___f_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed(lean_object* v_contents_1057_, lean_object* v___x_1058_, lean_object* v_env_1059_, lean_object* v_p_1060_, lean_object* v_toApplicative_1061_, lean_object* v_toBind_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_____do__lift_1067_){
_start:
{
uint8_t v___x_2042__boxed_1068_; lean_object* v_res_1069_; 
v___x_2042__boxed_1068_ = lean_unbox(v___x_1058_);
v_res_1069_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__3(v_contents_1057_, v___x_2042__boxed_1068_, v_env_1059_, v_p_1060_, v_toApplicative_1061_, v_toBind_1062_, v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_____do__lift_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4(lean_object* v_inst_1070_, lean_object* v_contents_1071_, uint8_t v___x_1072_, lean_object* v_p_1073_, lean_object* v_toApplicative_1074_, lean_object* v_toBind_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_env_1079_){
_start:
{
lean_object* v_getFileName_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
v_getFileName_1080_ = lean_ctor_get(v_inst_1070_, 2);
lean_inc(v_getFileName_1080_);
v___x_1081_ = lean_box(v___x_1072_);
lean_inc(v_toBind_1075_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1082_, 0, v_contents_1071_);
lean_closure_set(v___f_1082_, 1, v___x_1081_);
lean_closure_set(v___f_1082_, 2, v_env_1079_);
lean_closure_set(v___f_1082_, 3, v_p_1073_);
lean_closure_set(v___f_1082_, 4, v_toApplicative_1074_);
lean_closure_set(v___f_1082_, 5, v_toBind_1075_);
lean_closure_set(v___f_1082_, 6, v_inst_1076_);
lean_closure_set(v___f_1082_, 7, v_inst_1070_);
lean_closure_set(v___f_1082_, 8, v_inst_1077_);
lean_closure_set(v___f_1082_, 9, v_inst_1078_);
v___x_1083_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v_getFileName_1080_, v___f_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed(lean_object* v_inst_1084_, lean_object* v_contents_1085_, lean_object* v___x_1086_, lean_object* v_p_1087_, lean_object* v_toApplicative_1088_, lean_object* v_toBind_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_env_1093_){
_start:
{
uint8_t v___x_2069__boxed_1094_; lean_object* v_res_1095_; 
v___x_2069__boxed_1094_ = lean_unbox(v___x_1086_);
v_res_1095_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__4(v_inst_1084_, v_contents_1085_, v___x_2069__boxed_1094_, v_p_1087_, v_toApplicative_1088_, v_toBind_1089_, v_inst_1090_, v_inst_1091_, v_inst_1092_, v_env_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5(lean_object* v_toApplicative_1096_, lean_object* v_s_1097_, uint8_t v_err_1098_){
_start:
{
lean_object* v_toPure_1099_; lean_object* v_stxStack_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_toPure_1099_ = lean_ctor_get(v_toApplicative_1096_, 1);
lean_inc(v_toPure_1099_);
lean_dec_ref(v_toApplicative_1096_);
v_stxStack_1100_ = lean_ctor_get(v_s_1097_, 0);
v___x_1101_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1100_);
v___x_1102_ = lean_box(v_err_1098_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_apply_2(v_toPure_1099_, lean_box(0), v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed(lean_object* v_toApplicative_1105_, lean_object* v_s_1106_, lean_object* v_err_1107_){
_start:
{
uint8_t v_err_boxed_1108_; lean_object* v_res_1109_; 
v_err_boxed_1108_ = lean_unbox(v_err_1107_);
v_res_1109_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__5(v_toApplicative_1105_, v_s_1106_, v_err_boxed_1108_);
lean_dec_ref(v_s_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12(lean_object* v_env_1110_, lean_object* v_p_1111_, lean_object* v_ictx_1112_, lean_object* v_s_1113_, lean_object* v_toApplicative_1114_, uint8_t v___x_1115_, lean_object* v_toBind_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, uint8_t v___x_1121_, lean_object* v_____do__lift_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_s_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_box(0);
lean_inc_ref(v_env_1110_);
v___x_1125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1125_, 0, v_env_1110_);
lean_ctor_set(v___x_1125_, 1, v_____do__lift_1122_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
v___x_1126_ = l_Lean_Parser_getTokenTable(v_env_1110_);
lean_inc_ref(v_ictx_1112_);
v_s_1127_ = l_Lean_Parser_ParserFn_run(v_p_1111_, v_ictx_1112_, v___x_1125_, v___x_1126_, v_s_1113_);
lean_inc_ref_n(v_s_1127_, 2);
lean_inc_ref(v_toApplicative_1114_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1128_, 0, v_toApplicative_1114_);
lean_closure_set(v___f_1128_, 1, v_s_1127_);
v___x_1129_ = l_Lean_Parser_ParserState_allErrors(v_s_1127_);
v___x_1130_ = lean_array_get_size(v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_nat_dec_eq(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1133_, 0, v___f_1128_);
v___x_1134_ = lean_box(v___x_1115_);
lean_inc(v_toBind_1116_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1135_, 0, v_toApplicative_1114_);
lean_closure_set(v___f_1135_, 1, v___x_1134_);
lean_closure_set(v___f_1135_, 2, v_toBind_1116_);
lean_closure_set(v___f_1135_, 3, v___f_1133_);
v___x_1136_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1112_, v_s_1127_);
v___x_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
v___x_1139_ = l_Lean_logError___redArg(v_inst_1117_, v_inst_1118_, v_inst_1119_, v_inst_1120_, v___x_1138_);
v___x_1140_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v___x_1139_, v___f_1135_);
return v___x_1140_;
}
else
{
lean_object* v_pos_1141_; uint8_t v___x_1142_; 
v_pos_1141_ = lean_ctor_get(v_s_1127_, 2);
lean_inc(v_pos_1141_);
v___x_1142_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1112_, v_pos_1141_);
lean_dec(v_pos_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1143_, 0, v___f_1128_);
v___x_1144_ = lean_box(v___x_1115_);
lean_inc(v_toBind_1116_);
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1145_, 0, v_toApplicative_1114_);
lean_closure_set(v___f_1145_, 1, v___x_1144_);
lean_closure_set(v___f_1145_, 2, v_toBind_1116_);
lean_closure_set(v___f_1145_, 3, v___f_1143_);
v___x_1146_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1147_ = l_Lean_Parser_ParserState_mkError(v_s_1127_, v___x_1146_);
v___x_1148_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1112_, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofFormat(v___x_1149_);
v___x_1151_ = l_Lean_logError___redArg(v_inst_1117_, v_inst_1118_, v_inst_1119_, v_inst_1120_, v___x_1150_);
v___x_1152_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v___x_1151_, v___f_1145_);
return v___x_1152_;
}
else
{
lean_object* v_toPure_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_s_1127_);
lean_dec(v_inst_1120_);
lean_dec(v_inst_1119_);
lean_dec_ref(v_inst_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec_ref(v_ictx_1112_);
v_toPure_1153_ = lean_ctor_get(v_toApplicative_1114_, 1);
lean_inc(v_toPure_1153_);
lean_dec_ref(v_toApplicative_1114_);
v___f_1154_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1154_, 0, v___f_1128_);
v___x_1155_ = lean_box(v___x_1121_);
v___x_1156_ = lean_apply_2(v_toPure_1153_, lean_box(0), v___x_1155_);
v___x_1157_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v___x_1156_, v___f_1154_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed(lean_object* v_env_1158_, lean_object* v_p_1159_, lean_object* v_ictx_1160_, lean_object* v_s_1161_, lean_object* v_toApplicative_1162_, lean_object* v___x_1163_, lean_object* v_toBind_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v___x_1169_, lean_object* v_____do__lift_1170_){
_start:
{
uint8_t v___x_2098__boxed_1171_; uint8_t v___x_2103__boxed_1172_; lean_object* v_res_1173_; 
v___x_2098__boxed_1171_ = lean_unbox(v___x_1163_);
v___x_2103__boxed_1172_ = lean_unbox(v___x_1169_);
v_res_1173_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__12(v_env_1158_, v_p_1159_, v_ictx_1160_, v_s_1161_, v_toApplicative_1162_, v___x_2098__boxed_1171_, v_toBind_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_, v_inst_1168_, v___x_2103__boxed_1172_, v_____do__lift_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7(lean_object* v_source_1174_, uint8_t v___x_1175_, lean_object* v___y_1176_, lean_object* v_env_1177_, lean_object* v_p_1178_, lean_object* v_toApplicative_1179_, lean_object* v_toBind_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, uint8_t v___x_1185_, lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v_____do__lift_1188_){
_start:
{
lean_object* v_ictx_1189_; lean_object* v___x_1190_; lean_object* v___y_1192_; 
lean_inc_ref(v_source_1174_);
v_ictx_1189_ = l_Lean_Parser_mkInputContext___redArg(v_source_1174_, v_____do__lift_1188_, v___x_1175_, v___y_1176_);
v___x_1190_ = l_Lean_Parser_mkParserState(v_source_1174_);
lean_dec_ref(v_source_1174_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1199_ = l_panic___redArg(v___x_1187_, v___x_1198_);
v___y_1192_ = v___x_1199_;
goto v___jp_1191_;
}
else
{
lean_object* v_val_1200_; 
v_val_1200_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v___x_1186_, 1);
v___y_1192_ = v_val_1200_;
goto v___jp_1191_;
}
v___jp_1191_:
{
lean_object* v_s_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; 
v_s_1193_ = l_Lean_Parser_ParserState_setPos(v___x_1190_, v___y_1192_);
v___x_1194_ = lean_box(v___x_1175_);
v___x_1195_ = lean_box(v___x_1185_);
lean_inc(v_inst_1184_);
lean_inc(v_toBind_1180_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__12___boxed), 13, 12);
lean_closure_set(v___f_1196_, 0, v_env_1177_);
lean_closure_set(v___f_1196_, 1, v_p_1178_);
lean_closure_set(v___f_1196_, 2, v_ictx_1189_);
lean_closure_set(v___f_1196_, 3, v_s_1193_);
lean_closure_set(v___f_1196_, 4, v_toApplicative_1179_);
lean_closure_set(v___f_1196_, 5, v___x_1194_);
lean_closure_set(v___f_1196_, 6, v_toBind_1180_);
lean_closure_set(v___f_1196_, 7, v_inst_1181_);
lean_closure_set(v___f_1196_, 8, v_inst_1182_);
lean_closure_set(v___f_1196_, 9, v_inst_1183_);
lean_closure_set(v___f_1196_, 10, v_inst_1184_);
lean_closure_set(v___f_1196_, 11, v___x_1195_);
v___x_1197_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v_inst_1184_, v___f_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed(lean_object* v_source_1201_, lean_object* v___x_1202_, lean_object* v___y_1203_, lean_object* v_env_1204_, lean_object* v_p_1205_, lean_object* v_toApplicative_1206_, lean_object* v_toBind_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v_____do__lift_1215_){
_start:
{
uint8_t v___x_2192__boxed_1216_; uint8_t v___x_2198__boxed_1217_; lean_object* v_res_1218_; 
v___x_2192__boxed_1216_ = lean_unbox(v___x_1202_);
v___x_2198__boxed_1217_ = lean_unbox(v___x_1212_);
v_res_1218_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__7(v_source_1201_, v___x_2192__boxed_1216_, v___y_1203_, v_env_1204_, v_p_1205_, v_toApplicative_1206_, v_toBind_1207_, v_inst_1208_, v_inst_1209_, v_inst_1210_, v_inst_1211_, v___x_2198__boxed_1217_, v___x_1213_, v___x_1214_, v_____do__lift_1215_);
lean_dec(v___x_1214_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8(lean_object* v_text_1219_, lean_object* v_inst_1220_, uint8_t v___x_1221_, lean_object* v_p_1222_, lean_object* v_toApplicative_1223_, lean_object* v_toBind_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, uint8_t v___x_1228_, lean_object* v___x_1229_, lean_object* v_s_1230_, lean_object* v_env_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1242_; lean_object* v___x_1246_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1246_ = l_Lean_Syntax_getTailPos_x3f(v_s_1230_, v___x_1221_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1248_ = l_panic___redArg(v___x_1232_, v___x_1247_);
v___y_1242_ = v___x_1248_;
goto v___jp_1241_;
}
else
{
lean_object* v_val_1249_; 
v_val_1249_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1246_, 1);
v___y_1242_ = v_val_1249_;
goto v___jp_1241_;
}
v___jp_1233_:
{
lean_object* v_getFileName_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; 
v_getFileName_1236_ = lean_ctor_get(v_inst_1220_, 2);
lean_inc(v_getFileName_1236_);
v___x_1237_ = lean_box(v___x_1221_);
v___x_1238_ = lean_box(v___x_1228_);
lean_inc(v_toBind_1224_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__7___boxed), 15, 14);
lean_closure_set(v___f_1239_, 0, v___y_1234_);
lean_closure_set(v___f_1239_, 1, v___x_1237_);
lean_closure_set(v___f_1239_, 2, v___y_1235_);
lean_closure_set(v___f_1239_, 3, v_env_1231_);
lean_closure_set(v___f_1239_, 4, v_p_1222_);
lean_closure_set(v___f_1239_, 5, v_toApplicative_1223_);
lean_closure_set(v___f_1239_, 6, v_toBind_1224_);
lean_closure_set(v___f_1239_, 7, v_inst_1225_);
lean_closure_set(v___f_1239_, 8, v_inst_1220_);
lean_closure_set(v___f_1239_, 9, v_inst_1226_);
lean_closure_set(v___f_1239_, 10, v_inst_1227_);
lean_closure_set(v___f_1239_, 11, v___x_1238_);
lean_closure_set(v___f_1239_, 12, v___x_1229_);
lean_closure_set(v___f_1239_, 13, v___x_1232_);
v___x_1240_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v_getFileName_1236_, v___f_1239_);
return v___x_1240_;
}
v___jp_1241_:
{
lean_object* v_source_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_source_1243_ = lean_ctor_get(v_text_1219_, 0);
lean_inc_ref(v_source_1243_);
lean_dec_ref(v_text_1219_);
v___x_1244_ = lean_string_utf8_byte_size(v_source_1243_);
v___x_1245_ = lean_nat_dec_le(v___y_1242_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v___y_1242_);
v___y_1234_ = v_source_1243_;
v___y_1235_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v_source_1243_;
v___y_1235_ = v___y_1242_;
goto v___jp_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed(lean_object* v_text_1250_, lean_object* v_inst_1251_, lean_object* v___x_1252_, lean_object* v_p_1253_, lean_object* v_toApplicative_1254_, lean_object* v_toBind_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v_s_1261_, lean_object* v_env_1262_){
_start:
{
uint8_t v___x_2258__boxed_1263_; uint8_t v___x_2262__boxed_1264_; lean_object* v_res_1265_; 
v___x_2258__boxed_1263_ = lean_unbox(v___x_1252_);
v___x_2262__boxed_1264_ = lean_unbox(v___x_1259_);
v_res_1265_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__8(v_text_1250_, v_inst_1251_, v___x_2258__boxed_1263_, v_p_1253_, v_toApplicative_1254_, v_toBind_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v___x_2262__boxed_1264_, v___x_1260_, v_s_1261_, v_env_1262_);
lean_dec(v_s_1261_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9(lean_object* v_inst_1266_, lean_object* v_inst_1267_, uint8_t v___x_1268_, lean_object* v_p_1269_, lean_object* v_toApplicative_1270_, lean_object* v_toBind_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, uint8_t v___x_1275_, lean_object* v___x_1276_, lean_object* v_s_1277_, lean_object* v_text_1278_){
_start:
{
lean_object* v_getEnv_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; 
v_getEnv_1279_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc(v_getEnv_1279_);
lean_dec_ref(v_inst_1266_);
v___x_1280_ = lean_box(v___x_1268_);
v___x_1281_ = lean_box(v___x_1275_);
lean_inc(v_toBind_1271_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__8___boxed), 13, 12);
lean_closure_set(v___f_1282_, 0, v_text_1278_);
lean_closure_set(v___f_1282_, 1, v_inst_1267_);
lean_closure_set(v___f_1282_, 2, v___x_1280_);
lean_closure_set(v___f_1282_, 3, v_p_1269_);
lean_closure_set(v___f_1282_, 4, v_toApplicative_1270_);
lean_closure_set(v___f_1282_, 5, v_toBind_1271_);
lean_closure_set(v___f_1282_, 6, v_inst_1272_);
lean_closure_set(v___f_1282_, 7, v_inst_1273_);
lean_closure_set(v___f_1282_, 8, v_inst_1274_);
lean_closure_set(v___f_1282_, 9, v___x_1281_);
lean_closure_set(v___f_1282_, 10, v___x_1276_);
lean_closure_set(v___f_1282_, 11, v_s_1277_);
v___x_1283_ = lean_apply_4(v_toBind_1271_, lean_box(0), lean_box(0), v_getEnv_1279_, v___f_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v___x_1286_, lean_object* v_p_1287_, lean_object* v_toApplicative_1288_, lean_object* v_toBind_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v_s_1295_, lean_object* v_text_1296_){
_start:
{
uint8_t v___x_2317__boxed_1297_; uint8_t v___x_2321__boxed_1298_; lean_object* v_res_1299_; 
v___x_2317__boxed_1297_ = lean_unbox(v___x_1286_);
v___x_2321__boxed_1298_ = lean_unbox(v___x_1293_);
v_res_1299_ = l_Lean_Doc_parseStrLit_x27___redArg___lam__9(v_inst_1284_, v_inst_1285_, v___x_2317__boxed_1297_, v_p_1287_, v_toApplicative_1288_, v_toBind_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v___x_2321__boxed_1298_, v___x_1294_, v_s_1295_, v_text_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_p_1306_, lean_object* v_s_1307_){
_start:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = 1;
v___x_1309_ = l_Lean_Syntax_getPos_x3f(v_s_1307_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_toApplicative_1310_; lean_object* v_toBind_1311_; lean_object* v_getEnv_1312_; lean_object* v_contents_1313_; lean_object* v___x_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; 
lean_dec(v_inst_1301_);
v_toApplicative_1310_ = lean_ctor_get(v_inst_1300_, 0);
lean_inc_ref(v_toApplicative_1310_);
v_toBind_1311_ = lean_ctor_get(v_inst_1300_, 1);
lean_inc_n(v_toBind_1311_, 2);
v_getEnv_1312_ = lean_ctor_get(v_inst_1302_, 0);
lean_inc(v_getEnv_1312_);
lean_dec_ref(v_inst_1302_);
v_contents_1313_ = l_Lean_TSyntax_getString(v_s_1307_);
lean_dec(v_s_1307_);
v___x_1314_ = lean_box(v___x_1308_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1315_, 0, v_inst_1304_);
lean_closure_set(v___f_1315_, 1, v_contents_1313_);
lean_closure_set(v___f_1315_, 2, v___x_1314_);
lean_closure_set(v___f_1315_, 3, v_p_1306_);
lean_closure_set(v___f_1315_, 4, v_toApplicative_1310_);
lean_closure_set(v___f_1315_, 5, v_toBind_1311_);
lean_closure_set(v___f_1315_, 6, v_inst_1300_);
lean_closure_set(v___f_1315_, 7, v_inst_1303_);
lean_closure_set(v___f_1315_, 8, v_inst_1305_);
v___x_1316_ = lean_apply_4(v_toBind_1311_, lean_box(0), lean_box(0), v_getEnv_1312_, v___f_1315_);
return v___x_1316_;
}
else
{
lean_object* v_toApplicative_1317_; lean_object* v_toBind_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; 
v_toApplicative_1317_ = lean_ctor_get(v_inst_1300_, 0);
lean_inc_ref(v_toApplicative_1317_);
v_toBind_1318_ = lean_ctor_get(v_inst_1300_, 1);
lean_inc_n(v_toBind_1318_, 2);
v___x_1319_ = 0;
v___x_1320_ = lean_box(v___x_1308_);
v___x_1321_ = lean_box(v___x_1319_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Doc_parseStrLit_x27___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_1322_, 0, v_inst_1302_);
lean_closure_set(v___f_1322_, 1, v_inst_1304_);
lean_closure_set(v___f_1322_, 2, v___x_1320_);
lean_closure_set(v___f_1322_, 3, v_p_1306_);
lean_closure_set(v___f_1322_, 4, v_toApplicative_1317_);
lean_closure_set(v___f_1322_, 5, v_toBind_1318_);
lean_closure_set(v___f_1322_, 6, v_inst_1300_);
lean_closure_set(v___f_1322_, 7, v_inst_1303_);
lean_closure_set(v___f_1322_, 8, v_inst_1305_);
lean_closure_set(v___f_1322_, 9, v___x_1321_);
lean_closure_set(v___f_1322_, 10, v___x_1309_);
lean_closure_set(v___f_1322_, 11, v_s_1307_);
v___x_1323_ = lean_apply_4(v_toBind_1318_, lean_box(0), lean_box(0), v_inst_1301_, v___f_1322_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_p_1331_, lean_object* v_s_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_p_1331_, v_s_1332_);
return v___x_1333_;
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
