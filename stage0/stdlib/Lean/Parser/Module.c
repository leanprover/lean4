// Lean compiler output
// Module: Lean.Parser.Module
// Imports: public import Lean.Parser.Module.Syntax meta import Lean.Parser.Module.Syntax import Init.While
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
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
extern lean_object* l_Lean_Parser_SyntaxStack_empty;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
extern lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
lean_object* l_Lean_mkListNode(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Parser.Module"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__0 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__0_value;
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Parser.Module.updateTokens"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__1 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__1_value;
static const lean_string_object l_Lean_Parser_Module_updateTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Parser_Module_updateTokens___closed__2 = (const lean_object*)&l_Lean_Parser_Module_updateTokens___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Module_updateTokens___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_updateTokens___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
static const lean_ctor_object l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected identifier"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unexpected token '"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unexpected token"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "cannot use `import all` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "cannot use `meta import` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "cannot use `all` with `public import`; consider using separate `public import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` and `import all "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "` directives in order to import public data into the public scope and private data into the private scope."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "cannot use `public import` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_parseHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parseHeader___closed__0 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__0_value;
static const lean_string_object l_Lean_Parser_parseHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Parser_parseHeader___closed__1 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__1_value;
static lean_once_cell_t l_Lean_Parser_parseHeader___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_parseHeader___closed__2;
static lean_once_cell_t l_Lean_Parser_parseHeader___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_parseHeader___closed__3;
static lean_once_cell_t l_Lean_Parser_parseHeader___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_parseHeader___closed__4;
static const lean_string_object l_Lean_Parser_parseHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Parser_parseHeader___closed__5 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__5_value;
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_parseHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Parser_parseHeader___closed__6 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__6_value;
static const lean_string_object l_Lean_Parser_parseHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Parser_parseHeader___closed__7 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__7_value;
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_parseHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_parseHeader___closed__8_value_aux_2),((lean_object*)&l_Lean_Parser_parseHeader___closed__7_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Parser_parseHeader___closed__8 = (const lean_object*)&l_Lean_Parser_parseHeader___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eoi"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 206, 8, 118, 9, 188, 233, 7)}};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_isTerminalCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__0 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__0_value;
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 245, 50, 125, 205, 155, 109, 0)}};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__1 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__1_value;
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_isTerminalCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(36, 144, 26, 198, 154, 96, 74, 167)}};
static const lean_object* l_Lean_Parser_isTerminalCommand___closed__2 = (const lean_object*)&l_Lean_Parser_isTerminalCommand___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object*);
static const lean_array_object l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0_value;
static const lean_closure_object l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_tokenFn, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value;
static lean_once_cell_t l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_topLevelCommandParserFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_topLevelCommandParserFn___closed__0 = (const lean_object*)&l_Lean_Parser_topLevelCommandParserFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_topLevelCommandParserFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_topLevelCommandParserFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_topLevelCommandParserFn___closed__1 = (const lean_object*)&l_Lean_Parser_topLevelCommandParserFn___closed__1_value;
static lean_once_cell_t l_Lean_Parser_topLevelCommandParserFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_topLevelCommandParserFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to parse file"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value;
static lean_once_cell_t l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_testParseModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_testParseModule___closed__0 = (const lean_object*)&l_Lean_Parser_testParseModule___closed__0_value;
static const lean_string_object l_Lean_Parser_testParseModule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Parser_testParseModule___closed__1 = (const lean_object*)&l_Lean_Parser_testParseModule___closed__1_value;
static const lean_ctor_object l_Lean_Parser_testParseModule___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_testParseModule___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_testParseModule___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_testParseModule___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_testParseModule___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_testParseModule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_testParseModule___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_testParseModule___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l_Lean_Parser_testParseModule___closed__2 = (const lean_object*)&l_Lean_Parser_testParseModule___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(lean_object* v_msg_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0, &l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0_once, _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0);
v___x_4_ = lean_panic_fn(v___x_3_, v_msg_2_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_8_ = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__2));
v___x_9_ = lean_unsigned_to_nat(26u);
v___x_10_ = lean_unsigned_to_nat(23u);
v___x_11_ = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__1));
v___x_12_ = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__0));
v___x_13_ = l_mkPanicMessageWithDecl(v___x_12_, v___x_11_, v___x_10_, v___x_9_, v___x_8_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object* v_tokens_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_info_16_; lean_object* v___x_17_; 
v___x_15_ = l_Lean_Parser_Module_header;
v_info_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_info_16_);
v___x_17_ = l_Lean_Parser_addParserTokens(v_tokens_14_, v_info_16_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec_ref(v___x_17_);
v___x_18_ = lean_obj_once(&l_Lean_Parser_Module_updateTokens___closed__3, &l_Lean_Parser_Module_updateTokens___closed__3_once, _init_l_Lean_Parser_Module_updateTokens___closed__3);
v___x_19_ = l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; 
v_a_20_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v___x_17_);
return v_a_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object* v_as_26_, lean_object* v_i_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_i_27_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec(v_i_27_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_i_27_, v_one_31_);
lean_dec(v_i_27_);
v___x_33_ = l_Subarray_get___redArg(v_as_26_, v_n_32_);
v___x_34_ = l_Lean_Syntax_getTailInfo(v___x_33_);
lean_dec(v___x_33_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_trailing_35_; lean_object* v___x_36_; 
lean_dec(v_n_32_);
v_trailing_35_ = lean_ctor_get(v___x_34_, 2);
lean_inc_ref(v_trailing_35_);
lean_dec_ref(v___x_34_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v_trailing_35_);
return v___x_36_;
}
else
{
lean_dec(v___x_34_);
v_i_27_ = v_n_32_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object* v_as_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_38_, v_i_39_);
lean_dec_ref(v_as_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object* v_s_41_){
_start:
{
lean_object* v___x_42_; lean_object* v_start_43_; lean_object* v_stop_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = l_Lean_Parser_SyntaxStack_toSubarray(v_s_41_);
v_start_43_ = lean_ctor_get(v___x_42_, 1);
lean_inc(v_start_43_);
v_stop_44_ = lean_ctor_get(v___x_42_, 2);
lean_inc(v_stop_44_);
v___x_45_ = lean_nat_sub(v_stop_44_, v_start_43_);
lean_dec(v_start_43_);
lean_dec(v_stop_44_);
v___x_46_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v___x_42_, v___x_45_);
lean_dec_ref(v___x_42_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object* v_as_47_, lean_object* v_i_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_47_, v_i_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object* v_as_51_, lean_object* v_i_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(v_as_51_, v_i_52_, v_a_53_);
lean_dec_ref(v_as_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* v_c_60_, lean_object* v_pos_61_, lean_object* v_stk_62_, lean_object* v_e_63_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v_pos_78_; lean_object* v_endPos_x3f_79_; lean_object* v_e_80_; lean_object* v_unexpectedTk_94_; lean_object* v_expected_95_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v_pos_107_; lean_object* v_endPos_x3f_108_; lean_object* v_endPos_x3f_116_; uint8_t v___x_117_; 
v_unexpectedTk_94_ = lean_ctor_get(v_e_63_, 0);
v_expected_95_ = lean_ctor_get(v_e_63_, 2);
v_endPos_x3f_116_ = lean_box(0);
v___x_117_ = l_Lean_Syntax_isMissing(v_unexpectedTk_94_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_inc(v_expected_95_);
lean_inc(v_unexpectedTk_94_);
lean_dec_ref(v_e_63_);
v___x_118_ = l_Lean_Syntax_getRange_x3f(v_unexpectedTk_94_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_pos_61_);
v_val_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_128_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_start_123_; lean_object* v_stop_124_; lean_object* v_endPos_x3f_126_; 
v_start_123_ = lean_ctor_get(v_val_119_, 0);
lean_inc(v_start_123_);
v_stop_124_ = lean_ctor_get(v_val_119_, 1);
lean_inc(v_stop_124_);
lean_dec(v_val_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_stop_124_);
v_endPos_x3f_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_stop_124_);
v_endPos_x3f_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_pos_107_ = v_start_123_;
v_endPos_x3f_108_ = v_endPos_x3f_126_;
goto v___jp_106_;
}
}
}
else
{
lean_dec(v___x_118_);
v_pos_107_ = v_pos_61_;
v_endPos_x3f_108_ = v_endPos_x3f_116_;
goto v___jp_106_;
}
}
else
{
lean_dec_ref(v_stk_62_);
v_pos_78_ = v_pos_61_;
v_endPos_x3f_79_ = v_endPos_x3f_116_;
v_e_80_ = v_e_63_;
goto v___jp_77_;
}
v___jp_64_:
{
uint8_t v___x_69_; uint8_t v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = 1;
v___x_70_ = 2;
v___x_71_ = 0;
v___x_72_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_73_ = l_Lean_Parser_Error_toString(v___y_65_);
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___x_75_ = l_Lean_MessageData_ofFormat(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_76_, 0, v___y_66_);
lean_ctor_set(v___x_76_, 1, v___y_67_);
lean_ctor_set(v___x_76_, 2, v___y_68_);
lean_ctor_set(v___x_76_, 3, v___x_72_);
lean_ctor_set(v___x_76_, 4, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*5, v___x_69_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*5 + 1, v___x_70_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*5 + 2, v___x_71_);
return v___x_76_;
}
v___jp_77_:
{
lean_object* v_fileName_81_; lean_object* v_fileMap_82_; lean_object* v___x_83_; 
v_fileName_81_ = lean_ctor_get(v_c_60_, 1);
lean_inc_ref(v_fileName_81_);
v_fileMap_82_ = lean_ctor_get(v_c_60_, 2);
lean_inc_ref(v_fileMap_82_);
lean_dec_ref(v_c_60_);
lean_inc_ref(v_fileMap_82_);
v___x_83_ = l_Lean_FileMap_toPosition(v_fileMap_82_, v_pos_78_);
lean_dec(v_pos_78_);
if (lean_obj_tag(v_endPos_x3f_79_) == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_fileMap_82_);
v___x_84_ = lean_box(0);
v___y_65_ = v_e_80_;
v___y_66_ = v_fileName_81_;
v___y_67_ = v___x_83_;
v___y_68_ = v___x_84_;
goto v___jp_64_;
}
else
{
lean_object* v_val_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_val_85_ = lean_ctor_get(v_endPos_x3f_79_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v_endPos_x3f_79_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v_endPos_x3f_79_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_val_85_);
lean_dec(v_endPos_x3f_79_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = l_Lean_FileMap_toPosition(v_fileMap_82_, v_val_85_);
lean_dec(v_val_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
v___y_65_ = v_e_80_;
v___y_66_ = v_fileName_81_;
v___y_67_ = v___x_83_;
v___y_68_ = v___x_91_;
goto v___jp_64_;
}
}
}
}
v___jp_96_:
{
lean_object* v_e_100_; lean_object* v___x_101_; 
v_e_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_e_100_, 0, v_unexpectedTk_94_);
lean_ctor_set(v_e_100_, 1, v___y_99_);
lean_ctor_set(v_e_100_, 2, v_expected_95_);
v___x_101_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(v_stk_62_);
if (lean_obj_tag(v___x_101_) == 1)
{
lean_object* v_val_102_; lean_object* v_startPos_103_; lean_object* v_stopPos_104_; uint8_t v___x_105_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_102_);
lean_dec_ref(v___x_101_);
v_startPos_103_ = lean_ctor_get(v_val_102_, 1);
lean_inc(v_startPos_103_);
v_stopPos_104_ = lean_ctor_get(v_val_102_, 2);
lean_inc(v_stopPos_104_);
lean_dec(v_val_102_);
v___x_105_ = lean_nat_dec_eq(v_stopPos_104_, v___y_97_);
lean_dec(v_stopPos_104_);
if (v___x_105_ == 0)
{
lean_dec(v_startPos_103_);
v_pos_78_ = v___y_97_;
v_endPos_x3f_79_ = v___y_98_;
v_e_80_ = v_e_100_;
goto v___jp_77_;
}
else
{
lean_dec(v___y_97_);
v_pos_78_ = v_startPos_103_;
v_endPos_x3f_79_ = v___y_98_;
v_e_80_ = v_e_100_;
goto v___jp_77_;
}
}
else
{
lean_dec(v___x_101_);
v_pos_78_ = v___y_97_;
v_endPos_x3f_79_ = v___y_98_;
v_e_80_ = v_e_100_;
goto v___jp_77_;
}
}
v___jp_106_:
{
switch(lean_obj_tag(v_unexpectedTk_94_))
{
case 3:
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1));
v___y_97_ = v_pos_107_;
v___y_98_ = v_endPos_x3f_108_;
v___y_99_ = v___x_109_;
goto v___jp_96_;
}
case 2:
{
lean_object* v_val_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_val_110_ = lean_ctor_get(v_unexpectedTk_94_, 1);
v___x_111_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2));
v___x_112_ = lean_string_append(v___x_111_, v_val_110_);
v___x_113_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3));
v___x_114_ = lean_string_append(v___x_112_, v___x_113_);
v___y_97_ = v_pos_107_;
v___y_98_ = v_endPos_x3f_108_;
v___y_99_ = v___x_114_;
goto v___jp_96_;
}
default: 
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
v___y_97_ = v_pos_107_;
v___y_98_ = v_endPos_x3f_108_;
v___y_99_ = v___x_115_;
goto v___jp_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(lean_object* v_stx_129_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Syntax_getHeadInfo_x3f(v_stx_129_);
if (lean_obj_tag(v___x_134_) == 1)
{
lean_object* v_val_135_; 
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_134_);
if (lean_obj_tag(v_val_135_) == 0)
{
lean_object* v_leading_136_; lean_object* v_pos_137_; lean_object* v_trailing_138_; lean_object* v_endPos_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_161_; 
v_leading_136_ = lean_ctor_get(v_val_135_, 0);
v_pos_137_ = lean_ctor_get(v_val_135_, 1);
v_trailing_138_ = lean_ctor_get(v_val_135_, 2);
v_endPos_139_ = lean_ctor_get(v_val_135_, 3);
v_isSharedCheck_161_ = !lean_is_exclusive(v_val_135_);
if (v_isSharedCheck_161_ == 0)
{
v___x_141_ = v_val_135_;
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_endPos_139_);
lean_inc(v_trailing_138_);
lean_inc(v_pos_137_);
lean_inc(v_leading_136_);
lean_dec(v_val_135_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_str_143_; lean_object* v_stopPos_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v_str_143_ = lean_ctor_get(v_leading_136_, 0);
v_stopPos_144_ = lean_ctor_get(v_leading_136_, 2);
v_isSharedCheck_159_ = !lean_is_exclusive(v_leading_136_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_leading_136_, 1);
lean_dec(v_unused_160_);
v___x_146_ = v_leading_136_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_stopPos_144_);
lean_inc(v_str_143_);
lean_dec(v_leading_136_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(0u);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_str_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_stopPos_144_);
v___x_150_ = v_reuseFailAlloc_158_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_150_);
v___x_152_ = v___x_141_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_pos_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_trailing_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_endPos_139_);
v___x_152_ = v_reuseFailAlloc_157_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = l_Lean_Syntax_setHeadInfo(v_stx_129_, v___x_152_);
v___x_154_ = 1;
v___x_155_ = lean_box(v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_153_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
}
}
}
}
else
{
lean_dec(v_val_135_);
goto v___jp_130_;
}
}
else
{
lean_dec(v___x_134_);
goto v___jp_130_;
}
v___jp_130_:
{
uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = 0;
v___x_132_ = lean_box(v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_stx_129_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
lean_dec_ref(v_x_163_);
v___x_165_ = 0;
return v___x_165_;
}
}
else
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_166_; 
lean_dec_ref(v_x_162_);
v___x_166_ = 0;
return v___x_166_;
}
else
{
lean_object* v_val_167_; lean_object* v_val_168_; uint8_t v___x_169_; 
v_val_167_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_val_167_);
lean_dec_ref(v_x_162_);
v_val_168_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v_x_163_);
v___x_169_ = l_Lean_Parser_instBEqError_beq(v_val_167_, v_val_168_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_170_, v_x_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object* v_inputCtx_174_, lean_object* v_as_175_, size_t v_sz_176_, size_t v_i_177_, lean_object* v_b_178_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec_ref(v_inputCtx_174_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v_b_178_);
return v___x_181_;
}
else
{
lean_object* v_a_182_; lean_object* v_snd_183_; lean_object* v_fst_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; 
v_a_182_ = lean_array_uget_borrowed(v_as_175_, v_i_177_);
v_snd_183_ = lean_ctor_get(v_a_182_, 1);
v_fst_184_ = lean_ctor_get(v_a_182_, 0);
v_fst_185_ = lean_ctor_get(v_snd_183_, 0);
v_snd_186_ = lean_ctor_get(v_snd_183_, 1);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
lean_inc(v_fst_184_);
lean_inc_ref(v_inputCtx_174_);
v___x_187_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_174_, v_fst_184_, v_fst_185_, v_snd_186_);
v___x_188_ = l_Lean_MessageLog_add(v___x_187_, v_b_178_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_177_, v___x_189_);
v_i_177_ = v___x_190_;
v_b_178_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object* v_inputCtx_192_, lean_object* v_as_193_, lean_object* v_sz_194_, lean_object* v_i_195_, lean_object* v_b_196_, lean_object* v___y_197_){
_start:
{
size_t v_sz_boxed_198_; size_t v_i_boxed_199_; lean_object* v_res_200_; 
v_sz_boxed_198_ = lean_unbox_usize(v_sz_194_);
lean_dec(v_sz_194_);
v_i_boxed_199_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_192_, v_as_193_, v_sz_boxed_198_, v_i_boxed_199_, v_b_196_);
lean_dec_ref(v_as_193_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t v___x_201_, lean_object* v_inputCtx_202_, lean_object* v_ref_203_, lean_object* v_msg_204_){
_start:
{
uint8_t v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_217_; lean_object* v___x_223_; 
v___x_205_ = 0;
v___x_223_ = l_Lean_Syntax_getPos_x3f(v_ref_203_, v___x_205_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___x_224_;
goto v___jp_216_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v___x_223_);
v___y_217_ = v_val_225_;
goto v___jp_216_;
}
v___jp_206_:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_211_ = l_Lean_FileMap_toPosition(v___y_208_, v___y_210_);
lean_dec(v___y_210_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
v___x_213_ = 2;
v___x_214_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_215_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_215_, 0, v___y_207_);
lean_ctor_set(v___x_215_, 1, v___y_209_);
lean_ctor_set(v___x_215_, 2, v___x_212_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
lean_ctor_set(v___x_215_, 4, v_msg_204_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5, v___x_201_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5 + 1, v___x_213_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*5 + 2, v___x_205_);
return v___x_215_;
}
v___jp_216_:
{
lean_object* v_fileName_218_; lean_object* v_fileMap_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_fileName_218_ = lean_ctor_get(v_inputCtx_202_, 1);
lean_inc_ref(v_fileName_218_);
v_fileMap_219_ = lean_ctor_get(v_inputCtx_202_, 2);
lean_inc_ref(v_fileMap_219_);
lean_dec_ref(v_inputCtx_202_);
lean_inc_ref(v_fileMap_219_);
v___x_220_ = l_Lean_FileMap_toPosition(v_fileMap_219_, v___y_217_);
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v_ref_203_, v___x_205_);
if (lean_obj_tag(v___x_221_) == 0)
{
v___y_207_ = v_fileName_218_;
v___y_208_ = v_fileMap_219_;
v___y_209_ = v___x_220_;
v___y_210_ = v___y_217_;
goto v___jp_206_;
}
else
{
lean_object* v_val_222_; 
lean_dec(v___y_217_);
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref(v___x_221_);
v___y_207_ = v_fileName_218_;
v___y_208_ = v_fileMap_219_;
v___y_209_ = v___x_220_;
v___y_210_ = v_val_222_;
goto v___jp_206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_226_, lean_object* v_inputCtx_227_, lean_object* v_ref_228_, lean_object* v_msg_229_){
_start:
{
uint8_t v___x_7306__boxed_230_; lean_object* v_res_231_; 
v___x_7306__boxed_230_ = lean_unbox(v___x_226_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_7306__boxed_230_, v_inputCtx_227_, v_ref_228_, v_msg_229_);
lean_dec(v_ref_228_);
return v_res_231_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9));
v___x_250_ = l_Lean_MessageData_ofFormat(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15));
v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object* v_inputCtx_277_, lean_object* v_moduleTk_x3f_278_, lean_object* v_as_279_, size_t v_sz_280_, size_t v_i_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_a_285_; uint8_t v___x_289_; 
v___x_289_ = lean_usize_dec_lt(v_i_281_, v_sz_280_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref(v_inputCtx_277_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_b_282_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v_a_292_; uint8_t v___x_293_; 
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4));
v_a_292_ = lean_array_uget_borrowed(v_as_279_, v_i_281_);
lean_inc(v_a_292_);
v___x_293_ = l_Lean_Syntax_isOfKind(v_a_292_, v___x_291_);
if (v___x_293_ == 0)
{
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___y_295_; lean_object* v_messages_296_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v_messages_304_; lean_object* v___y_310_; uint8_t v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___x_334_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v_allTk_x3f_338_; lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v_metaTk_x3f_352_; lean_object* v_pubTk_x3f_364_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_374_ = l_Lean_Syntax_getArg(v_a_292_, v___x_334_);
v___x_375_ = l_Lean_Syntax_isNone(v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
lean_inc(v___x_374_);
v___x_376_ = l_Lean_Syntax_matchesNull(v___x_374_, v___x_349_);
if (v___x_376_ == 0)
{
lean_dec(v___x_374_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = l_Lean_Syntax_getArg(v___x_374_, v___x_334_);
lean_dec(v___x_374_);
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22));
lean_inc(v___x_377_);
v___x_379_ = l_Lean_Syntax_isOfKind(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec(v___x_377_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = l_Lean_Syntax_getArg(v___x_377_, v___x_334_);
lean_dec(v___x_377_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v_pubTk_x3f_364_ = v___x_381_;
goto v___jp_363_;
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec(v___x_374_);
v___x_382_ = lean_box(0);
v_pubTk_x3f_364_ = v___x_382_;
goto v___jp_363_;
}
v___jp_294_:
{
if (lean_obj_tag(v___y_295_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_val_297_ = lean_ctor_get(v___y_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref(v___y_295_);
v___x_298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7);
lean_inc_ref(v_inputCtx_277_);
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_297_, v___x_298_);
lean_dec(v_val_297_);
v___x_300_ = l_Lean_MessageLog_add(v___x_299_, v_messages_296_);
v_a_285_ = v___x_300_;
goto v___jp_284_;
}
else
{
lean_dec(v___y_295_);
v_a_285_ = v_messages_296_;
goto v___jp_284_;
}
}
v___jp_301_:
{
if (lean_obj_tag(v___y_302_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_val_305_ = lean_ctor_get(v___y_302_, 0);
lean_inc(v_val_305_);
lean_dec_ref(v___y_302_);
v___x_306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_277_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_305_, v___x_306_);
lean_dec(v_val_305_);
v___x_308_ = l_Lean_MessageLog_add(v___x_307_, v_messages_304_);
v___y_295_ = v___y_303_;
v_messages_296_ = v___x_308_;
goto v___jp_294_;
}
else
{
lean_dec(v___y_302_);
v___y_295_ = v___y_303_;
v_messages_296_ = v_messages_304_;
goto v___jp_294_;
}
}
v___jp_309_:
{
if (lean_obj_tag(v___y_312_) == 1)
{
if (lean_obj_tag(v___y_313_) == 0)
{
lean_dec_ref(v___y_312_);
lean_dec(v___y_310_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___y_313_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___y_313_, 0);
lean_dec(v_unused_333_);
v___x_315_ = v___y_313_;
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___y_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
if (v___y_311_ == 0)
{
lean_del_object(v___x_315_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_310_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v_val_317_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___y_312_);
v___x_318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_310_, v___y_311_);
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
v___x_321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12));
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
v___x_323_ = lean_string_append(v___x_322_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13));
v___x_325_ = lean_string_append(v___x_323_, v___x_324_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 3);
lean_ctor_set(v___x_315_, 0, v___x_325_);
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_MessageData_ofFormat(v___x_327_);
lean_inc_ref(v_inputCtx_277_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_317_, v___x_328_);
lean_dec(v_val_317_);
v___x_330_ = l_Lean_MessageLog_add(v___x_329_, v_b_282_);
v_a_285_ = v___x_330_;
goto v___jp_284_;
}
}
}
}
}
else
{
lean_dec(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_310_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
}
v___jp_335_:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(5u);
v___x_340_ = l_Lean_Syntax_getArg(v_a_292_, v___x_339_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_340_, v___x_334_);
if (v___x_341_ == 0)
{
lean_dec(v_allTk_x3f_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = l_Lean_Syntax_getArg(v_a_292_, v___x_342_);
v___x_344_ = l_Lean_TSyntax_getId(v___x_343_);
lean_dec(v___x_343_);
if (lean_obj_tag(v_moduleTk_x3f_278_) == 0)
{
if (v___x_341_ == 0)
{
lean_dec(v___y_336_);
v___y_310_ = v___x_344_;
v___y_311_ = v___x_341_;
v___y_312_ = v_allTk_x3f_338_;
v___y_313_ = v___y_337_;
goto v___jp_309_;
}
else
{
lean_dec(v___x_344_);
if (lean_obj_tag(v___y_337_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_val_345_ = lean_ctor_get(v___y_337_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___y_337_);
v___x_346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
lean_inc_ref(v_inputCtx_277_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_345_, v___x_346_);
lean_dec(v_val_345_);
v___x_348_ = l_Lean_MessageLog_add(v___x_347_, v_b_282_);
v___y_302_ = v___y_336_;
v___y_303_ = v_allTk_x3f_338_;
v_messages_304_ = v___x_348_;
goto v___jp_301_;
}
else
{
lean_dec(v___y_337_);
v___y_302_ = v___y_336_;
v___y_303_ = v_allTk_x3f_338_;
v_messages_304_ = v_b_282_;
goto v___jp_301_;
}
}
}
else
{
lean_dec(v___y_336_);
v___y_310_ = v___x_344_;
v___y_311_ = v___x_341_;
v___y_312_ = v_allTk_x3f_338_;
v___y_313_ = v___y_337_;
goto v___jp_309_;
}
}
}
v___jp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = l_Lean_Syntax_getArg(v_a_292_, v___x_353_);
v___x_355_ = l_Lean_Syntax_isNone(v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
lean_inc(v___x_354_);
v___x_356_ = l_Lean_Syntax_matchesNull(v___x_354_, v___x_349_);
if (v___x_356_ == 0)
{
lean_dec(v___x_354_);
lean_dec(v_metaTk_x3f_352_);
lean_dec(v___y_351_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = l_Lean_Syntax_getArg(v___x_354_, v___x_334_);
lean_dec(v___x_354_);
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18));
lean_inc(v___x_357_);
v___x_359_ = l_Lean_Syntax_isOfKind(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_dec(v___x_357_);
lean_dec(v_metaTk_x3f_352_);
lean_dec(v___y_351_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Syntax_getArg(v___x_357_, v___x_334_);
lean_dec(v___x_357_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___y_336_ = v_metaTk_x3f_352_;
v___y_337_ = v___y_351_;
v_allTk_x3f_338_ = v___x_361_;
goto v___jp_335_;
}
}
}
else
{
lean_object* v___x_362_; 
lean_dec(v___x_354_);
v___x_362_ = lean_box(0);
v___y_336_ = v_metaTk_x3f_352_;
v___y_337_ = v___y_351_;
v_allTk_x3f_338_ = v___x_362_;
goto v___jp_335_;
}
}
v___jp_363_:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = l_Lean_Syntax_getArg(v_a_292_, v___x_349_);
v___x_366_ = l_Lean_Syntax_isNone(v___x_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
lean_inc(v___x_365_);
v___x_367_ = l_Lean_Syntax_matchesNull(v___x_365_, v___x_349_);
if (v___x_367_ == 0)
{
lean_dec(v___x_365_);
lean_dec(v_pubTk_x3f_364_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = l_Lean_Syntax_getArg(v___x_365_, v___x_334_);
lean_dec(v___x_365_);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20));
lean_inc(v___x_368_);
v___x_370_ = l_Lean_Syntax_isOfKind(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v___x_368_);
lean_dec(v_pubTk_x3f_364_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Lean_Syntax_getArg(v___x_368_, v___x_334_);
lean_dec(v___x_368_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___y_351_ = v_pubTk_x3f_364_;
v_metaTk_x3f_352_ = v___x_372_;
goto v___jp_350_;
}
}
}
else
{
lean_object* v___x_373_; 
lean_dec(v___x_365_);
v___x_373_ = lean_box(0);
v___y_351_ = v_pubTk_x3f_364_;
v_metaTk_x3f_352_ = v___x_373_;
goto v___jp_350_;
}
}
}
}
v___jp_284_:
{
size_t v___x_286_; size_t v___x_287_; 
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_add(v_i_281_, v___x_286_);
v_i_281_ = v___x_287_;
v_b_282_ = v_a_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* v_inputCtx_383_, lean_object* v_moduleTk_x3f_384_, lean_object* v_as_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_391_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_383_, v_moduleTk_x3f_384_, v_as_385_, v_sz_boxed_390_, v_i_boxed_391_, v_b_388_);
lean_dec_ref(v_as_385_);
lean_dec(v_moduleTk_x3f_384_);
return v_res_392_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(32u);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3(void){
_start:
{
size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__2, &l_Lean_Parser_parseHeader___closed__2_once, _init_l_Lean_Parser_parseHeader___closed__2);
v___x_403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_399_);
lean_ctor_set(v___x_403_, 3, v___x_399_);
lean_ctor_set_usize(v___x_403_, 4, v___x_398_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_NameSet_empty;
v___x_405_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__3, &l_Lean_Parser_parseHeader___closed__3_once, _init_l_Lean_Parser_parseHeader___closed__3);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_ctor_set(v___x_406_, 2, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* v_inputCtx_419_){
_start:
{
uint32_t v___x_421_; lean_object* v___x_422_; 
v___x_421_ = 0;
v___x_422_ = lean_mk_empty_environment(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_550_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_550_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_550_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_550_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_fn_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_548_; 
v___x_427_ = l_Lean_Parser_Module_header;
v_fn_428_ = lean_ctor_get(v___x_427_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_427_, 0);
lean_dec(v_unused_549_);
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_548_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_fn_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_548_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_inputString_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_stxStack_443_; lean_object* v_pos_444_; lean_object* v_errorMsg_445_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v___y_467_; lean_object* v_messages_468_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; size_t v___y_482_; lean_object* v___x_497_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; size_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v_moduleTk_x3f_505_; lean_object* v___y_515_; uint8_t v___x_545_; 
v_inputString_432_ = lean_ctor_get(v_inputCtx_419_, 0);
lean_inc(v_a_423_);
v___x_433_ = l_Lean_Parser_getTokenTable(v_a_423_);
v___x_434_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_435_, 0, v___x_434_);
lean_closure_set(v___x_435_, 1, v_fn_428_);
v___x_436_ = l_Lean_Parser_Module_updateTokens(v___x_433_);
v___x_437_ = l_Lean_Options_empty;
v___x_438_ = lean_box(0);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_440_, 0, v_a_423_);
lean_ctor_set(v___x_440_, 1, v___x_437_);
lean_ctor_set(v___x_440_, 2, v___x_438_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
v___x_441_ = l_Lean_Parser_mkParserState(v_inputString_432_);
lean_inc_ref(v_inputCtx_419_);
v___x_442_ = l_Lean_Parser_ParserFn_run(v___x_435_, v_inputCtx_419_, v___x_440_, v___x_436_, v___x_441_);
v_stxStack_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_stxStack_443_);
v_pos_444_ = lean_ctor_get(v___x_442_, 2);
lean_inc(v_pos_444_);
v_errorMsg_445_ = lean_ctor_get(v___x_442_, 4);
lean_inc(v_errorMsg_445_);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_443_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_443_);
lean_dec_ref(v_stxStack_443_);
v___y_515_ = v___x_546_;
goto v___jp_514_;
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v_stxStack_443_);
v___x_547_ = lean_box(0);
v___y_515_ = v___x_547_;
goto v___jp_514_;
}
v___jp_446_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_451_, 0, v_pos_444_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___y_448_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1 + 1, v___y_450_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___y_447_);
lean_ctor_set(v___x_430_, 0, v___x_451_);
v___x_453_ = v___x_430_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___y_447_);
v___x_453_ = v_reuseFailAlloc_458_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___y_449_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_454_);
v___x_456_ = v___x_425_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
v___jp_459_:
{
if (v___y_461_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = 1;
v___y_447_ = v___y_460_;
v___y_448_ = v___y_463_;
v___y_449_ = v___y_462_;
v___y_450_ = v___x_464_;
goto v___jp_446_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
v___y_447_ = v___y_460_;
v___y_448_ = v___y_463_;
v___y_449_ = v___y_462_;
v___y_450_ = v___x_465_;
goto v___jp_446_;
}
}
v___jp_466_:
{
lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_469_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_467_);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
lean_inc(v_snd_471_);
lean_dec_ref(v___x_469_);
v___x_472_ = lean_box(0);
v___x_473_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_445_, v___x_472_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 1;
v___x_475_ = lean_unbox(v_snd_471_);
lean_dec(v_snd_471_);
v___y_460_ = v_messages_468_;
v___y_461_ = v___x_475_;
v___y_462_ = v_fst_470_;
v___y_463_ = v___x_474_;
goto v___jp_459_;
}
else
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 0;
v___x_477_ = lean_unbox(v_snd_471_);
lean_dec(v_snd_471_);
v___y_460_ = v_messages_468_;
v___y_461_ = v___x_477_;
v___y_462_ = v_fst_470_;
v___y_463_ = v___x_476_;
goto v___jp_459_;
}
}
v___jp_478_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; size_t v_sz_486_; lean_object* v___x_487_; 
v___x_483_ = lean_unsigned_to_nat(2u);
v___x_484_ = l_Lean_Syntax_getArg(v___y_481_, v___x_483_);
v___x_485_ = l_Lean_Syntax_getArgs(v___x_484_);
lean_dec(v___x_484_);
v_sz_486_ = lean_array_size(v___x_485_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_419_, v___y_479_, v___x_485_, v_sz_486_, v___y_482_, v___y_480_);
lean_dec_ref(v___x_485_);
lean_dec(v___y_479_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref(v___x_487_);
v___y_467_ = v___y_481_;
v_messages_468_ = v_a_488_;
goto v___jp_466_;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v___y_481_);
lean_dec(v_errorMsg_445_);
lean_dec(v_pos_444_);
lean_del_object(v___x_430_);
lean_del_object(v___x_425_);
v_a_489_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_487_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
v___jp_498_:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = l_Lean_Syntax_getArg(v___y_499_, v___x_506_);
v___x_508_ = l_Lean_Syntax_isNone(v___x_507_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
lean_inc(v___x_507_);
v___x_509_ = l_Lean_Syntax_matchesNull(v___x_507_, v___x_506_);
if (v___x_509_ == 0)
{
lean_dec(v___x_507_);
lean_dec(v_moduleTk_x3f_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v_inputCtx_419_);
v___y_467_ = v___y_499_;
v_messages_468_ = v___y_500_;
goto v___jp_466_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = l_Lean_Syntax_getArg(v___x_507_, v___x_497_);
lean_dec(v___x_507_);
v___x_511_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
v___x_512_ = l_Lean_Name_mkStr4(v___y_501_, v___y_503_, v___y_504_, v___x_511_);
v___x_513_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_512_);
lean_dec(v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_moduleTk_x3f_505_);
lean_dec_ref(v_inputCtx_419_);
v___y_467_ = v___y_499_;
v_messages_468_ = v___y_500_;
goto v___jp_466_;
}
else
{
v___y_479_ = v_moduleTk_x3f_505_;
v___y_480_ = v___y_500_;
v___y_481_ = v___y_499_;
v___y_482_ = v___y_502_;
goto v___jp_478_;
}
}
}
else
{
lean_dec(v___x_507_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v___y_501_);
v___y_479_ = v_moduleTk_x3f_505_;
v___y_480_ = v___y_500_;
v___y_481_ = v___y_499_;
v___y_482_ = v___y_502_;
goto v___jp_478_;
}
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_516_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_517_ = l_Lean_Parser_ParserState_allErrors(v___x_442_);
v_sz_518_ = lean_array_size(v___x_517_);
v___x_519_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_419_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_419_, v___x_517_, v_sz_518_, v___x_519_, v___x_516_);
lean_dec_ref(v___x_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_525_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_515_);
v___x_526_ = l_Lean_Syntax_isOfKind(v___y_515_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_inputCtx_419_);
v___y_467_ = v___y_515_;
v_messages_468_ = v_a_521_;
goto v___jp_466_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = l_Lean_Syntax_getArg(v___y_515_, v___x_497_);
v___x_528_ = l_Lean_Syntax_isNone(v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_527_);
v___x_530_ = l_Lean_Syntax_matchesNull(v___x_527_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v___x_527_);
lean_dec_ref(v_inputCtx_419_);
v___y_467_ = v___y_515_;
v_messages_468_ = v_a_521_;
goto v___jp_466_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = l_Lean_Syntax_getArg(v___x_527_, v___x_497_);
lean_dec(v___x_527_);
v___x_532_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_531_);
v___x_533_ = l_Lean_Syntax_isOfKind(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
lean_dec_ref(v_inputCtx_419_);
v___y_467_ = v___y_515_;
v_messages_468_ = v_a_521_;
goto v___jp_466_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Lean_Syntax_getArg(v___x_531_, v___x_497_);
lean_dec(v___x_531_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___y_499_ = v___y_515_;
v___y_500_ = v_a_521_;
v___y_501_ = v___x_522_;
v___y_502_ = v___x_519_;
v___y_503_ = v___x_523_;
v___y_504_ = v___x_524_;
v_moduleTk_x3f_505_ = v___x_535_;
goto v___jp_498_;
}
}
}
else
{
lean_object* v___x_536_; 
lean_dec(v___x_527_);
v___x_536_ = lean_box(0);
v___y_499_ = v___y_515_;
v___y_500_ = v_a_521_;
v___y_501_ = v___x_522_;
v___y_502_ = v___x_519_;
v___y_503_ = v___x_523_;
v___y_504_ = v___x_524_;
v_moduleTk_x3f_505_ = v___x_536_;
goto v___jp_498_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v___y_515_);
lean_dec(v_errorMsg_445_);
lean_dec(v_pos_444_);
lean_del_object(v___x_430_);
lean_del_object(v___x_425_);
lean_dec_ref(v_inputCtx_419_);
v_a_537_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_520_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_520_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec_ref(v_inputCtx_419_);
v_a_551_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_422_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_422_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Parser_parseHeader(v_inputCtx_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_569_, lean_object* v_pos_570_){
_start:
{
lean_object* v___y_572_; lean_object* v_inputString_582_; lean_object* v_endPos_583_; uint8_t v___x_584_; 
v_inputString_582_ = lean_ctor_get(v_inputCtx_569_, 0);
v_endPos_583_ = lean_ctor_get(v_inputCtx_569_, 3);
v___x_584_ = lean_nat_dec_le(v_pos_570_, v_endPos_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc(v_endPos_583_);
lean_inc(v_pos_570_);
lean_inc_ref(v_inputString_582_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_inputString_582_);
lean_ctor_set(v___x_585_, 1, v_pos_570_);
lean_ctor_set(v___x_585_, 2, v_endPos_583_);
v___y_572_ = v___x_585_;
goto v___jp_571_;
}
else
{
lean_object* v___x_586_; 
lean_inc_n(v_pos_570_, 2);
lean_inc_ref(v_inputString_582_);
v___x_586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_586_, 0, v_inputString_582_);
lean_ctor_set(v___x_586_, 1, v_pos_570_);
lean_ctor_set(v___x_586_, 2, v_pos_570_);
v___y_572_ = v___x_586_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_atom_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_inc(v_pos_570_);
lean_inc_ref(v___y_572_);
v___x_573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_573_, 0, v___y_572_);
lean_ctor_set(v___x_573_, 1, v_pos_570_);
lean_ctor_set(v___x_573_, 2, v___y_572_);
lean_ctor_set(v___x_573_, 3, v_pos_570_);
v___x_574_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_575_, 0, v___x_573_);
lean_ctor_set(v_atom_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_array_push(v___x_578_, v_atom_575_);
v___x_580_ = lean_box(2);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_576_);
lean_ctor_set(v___x_581_, 2, v___x_579_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_587_, lean_object* v_pos_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_587_, v_pos_588_);
lean_dec_ref(v_inputCtx_587_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_601_){
_start:
{
uint8_t v___y_603_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_601_);
v___x_607_ = l_Lean_Syntax_isOfKind(v_s_601_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_601_);
v___x_609_ = l_Lean_Syntax_isOfKind(v_s_601_, v___x_608_);
v___y_603_ = v___x_609_;
goto v___jp_602_;
}
else
{
v___y_603_ = v___x_607_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_605_ = l_Lean_Syntax_isOfKind(v_s_601_, v___x_604_);
return v___x_605_;
}
else
{
lean_dec(v_s_601_);
return v___y_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* v_s_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Lean_Parser_isTerminalCommand(v_s_610_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2(void){
_start:
{
uint32_t v___x_617_; lean_object* v___x_618_; 
v___x_617_ = 32;
v___x_618_ = l_Char_utf8Size(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_619_, lean_object* v_pmctx_620_, lean_object* v_pos_621_){
_start:
{
lean_object* v_inputString_622_; lean_object* v_env_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_s_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_s_632_; lean_object* v_errorMsg_633_; 
v_inputString_622_ = lean_ctor_get(v_inputCtx_619_, 0);
v_env_623_ = lean_ctor_get(v_pmctx_620_, 0);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_626_ = l_Lean_Parser_SyntaxStack_empty;
v___x_627_ = l_Lean_Parser_initCacheForInput(v_inputString_622_);
v___x_628_ = lean_box(0);
lean_inc(v_pos_621_);
v_s_629_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_629_, 0, v___x_626_);
lean_ctor_set(v_s_629_, 1, v___x_624_);
lean_ctor_set(v_s_629_, 2, v_pos_621_);
lean_ctor_set(v_s_629_, 3, v___x_627_);
lean_ctor_set(v_s_629_, 4, v___x_628_);
lean_ctor_set(v_s_629_, 5, v___x_625_);
v___x_630_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_623_);
v___x_631_ = l_Lean_Parser_getTokenTable(v_env_623_);
v_s_632_ = l_Lean_Parser_ParserFn_run(v___x_630_, v_inputCtx_619_, v_pmctx_620_, v___x_631_, v_s_629_);
v_errorMsg_633_ = lean_ctor_get(v_s_632_, 4);
lean_inc(v_errorMsg_633_);
if (lean_obj_tag(v_errorMsg_633_) == 0)
{
lean_object* v_pos_634_; 
lean_dec(v_pos_621_);
v_pos_634_ = lean_ctor_get(v_s_632_, 2);
lean_inc(v_pos_634_);
lean_dec_ref(v_s_632_);
return v_pos_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v_errorMsg_633_);
lean_dec_ref(v_s_632_);
v___x_635_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
v___x_636_ = lean_nat_add(v_pos_621_, v___x_635_);
lean_dec(v_pos_621_);
return v___x_636_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_642_ = l_Lean_Parser_categoryParser(v___x_641_, v___x_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_645_; lean_object* v_fn_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v_fn_646_ = lean_ctor_get(v___x_645_, 1);
lean_inc_ref(v_fn_646_);
v___x_647_ = lean_apply_2(v_fn_646_, v_a_643_, v_a_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_648_, lean_object* v_as_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_b_652_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_653_ == 0)
{
lean_dec_ref(v_inputCtx_648_);
return v_b_652_;
}
else
{
lean_object* v_a_654_; lean_object* v_snd_655_; lean_object* v_fst_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_659_; lean_object* v___x_660_; size_t v___x_661_; size_t v___x_662_; 
v_a_654_ = lean_array_uget_borrowed(v_as_649_, v_i_651_);
v_snd_655_ = lean_ctor_get(v_a_654_, 1);
v_fst_656_ = lean_ctor_get(v_a_654_, 0);
v_fst_657_ = lean_ctor_get(v_snd_655_, 0);
v_snd_658_ = lean_ctor_get(v_snd_655_, 1);
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_inc(v_fst_656_);
lean_inc_ref(v_inputCtx_648_);
v___x_659_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_648_, v_fst_656_, v_fst_657_, v_snd_658_);
v___x_660_ = l_Lean_MessageLog_add(v___x_659_, v_b_652_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_add(v_i_651_, v___x_661_);
v_i_651_ = v___x_662_;
v_b_652_ = v___x_660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_664_, lean_object* v_as_665_, lean_object* v_sz_666_, lean_object* v_i_667_, lean_object* v_b_668_){
_start:
{
size_t v_sz_boxed_669_; size_t v_i_boxed_670_; lean_object* v_res_671_; 
v_sz_boxed_669_ = lean_unbox_usize(v_sz_666_);
lean_dec(v_sz_666_);
v_i_boxed_670_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_664_, v_as_665_, v_sz_boxed_669_, v_i_boxed_670_, v_b_668_);
lean_dec_ref(v_as_665_);
return v_res_671_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_p_674_; 
v___x_672_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_673_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v_p_674_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_674_, 0, v___x_673_);
lean_closure_set(v_p_674_, 1, v___x_672_);
return v_p_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_675_, lean_object* v_pmctx_676_, lean_object* v_b_677_){
_start:
{
lean_object* v_snd_678_; lean_object* v_snd_679_; lean_object* v_fst_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_782_; 
v_snd_678_ = lean_ctor_get(v_b_677_, 1);
lean_inc(v_snd_678_);
v_snd_679_ = lean_ctor_get(v_snd_678_, 1);
lean_inc(v_snd_679_);
v_fst_680_ = lean_ctor_get(v_b_677_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_b_677_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v_b_677_, 1);
lean_dec(v_unused_783_);
v___x_682_ = v_b_677_;
v_isShared_683_ = v_isSharedCheck_782_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_fst_680_);
lean_dec(v_b_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_782_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fst_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_780_; 
v_fst_684_ = lean_ctor_get(v_snd_678_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_snd_678_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_snd_678_, 1);
lean_dec(v_unused_781_);
v___x_686_ = v_snd_678_;
v_isShared_687_ = v_isSharedCheck_780_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_fst_684_);
lean_dec(v_snd_678_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_780_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_779_; 
v_fst_688_ = lean_ctor_get(v_snd_679_, 0);
v_snd_689_ = lean_ctor_get(v_snd_679_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_snd_679_);
if (v_isSharedCheck_779_ == 0)
{
v___x_691_ = v_snd_679_;
v_isShared_692_ = v_isSharedCheck_779_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_snd_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_779_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_675_, v_fst_680_);
if (v___x_693_ == 0)
{
lean_object* v_env_694_; lean_object* v_inputString_695_; lean_object* v_p_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_s_704_; lean_object* v_stxStack_705_; lean_object* v_pos_706_; lean_object* v_errorMsg_707_; lean_object* v_recoveredErrors_708_; uint8_t v_recovering_709_; lean_object* v___y_711_; lean_object* v_messages_712_; size_t v_sz_724_; size_t v___x_725_; lean_object* v___x_726_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_744_; lean_object* v_pos_745_; uint8_t v___y_750_; uint8_t v___x_766_; 
v_env_694_ = lean_ctor_get(v_pmctx_676_, 0);
v_inputString_695_ = lean_ctor_get(v_inputCtx_675_, 0);
v_p_696_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0);
lean_inc_ref(v_env_694_);
v___x_697_ = l_Lean_Parser_getTokenTable(v_env_694_);
v___x_698_ = l_Lean_Parser_SyntaxStack_empty;
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l_Lean_Parser_initCacheForInput(v_inputString_695_);
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_680_);
v___x_703_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_703_, 0, v___x_698_);
lean_ctor_set(v___x_703_, 1, v___x_699_);
lean_ctor_set(v___x_703_, 2, v_fst_680_);
lean_ctor_set(v___x_703_, 3, v___x_700_);
lean_ctor_set(v___x_703_, 4, v___x_701_);
lean_ctor_set(v___x_703_, 5, v___x_702_);
lean_inc_ref(v_pmctx_676_);
lean_inc_ref(v_inputCtx_675_);
v_s_704_ = l_Lean_Parser_ParserFn_run(v_p_696_, v_inputCtx_675_, v_pmctx_676_, v___x_697_, v___x_703_);
v_stxStack_705_ = lean_ctor_get(v_s_704_, 0);
lean_inc_ref(v_stxStack_705_);
v_pos_706_ = lean_ctor_get(v_s_704_, 2);
lean_inc(v_pos_706_);
v_errorMsg_707_ = lean_ctor_get(v_s_704_, 4);
lean_inc(v_errorMsg_707_);
v_recoveredErrors_708_ = lean_ctor_get(v_s_704_, 5);
lean_inc_ref(v_recoveredErrors_708_);
lean_dec_ref(v_s_704_);
v_recovering_709_ = 1;
v_sz_724_ = lean_array_size(v_recoveredErrors_708_);
v___x_725_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_675_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_675_, v_recoveredErrors_708_, v_sz_724_, v___x_725_, v_fst_688_);
lean_dec_ref(v_recoveredErrors_708_);
v___x_766_ = lean_unbox(v_fst_684_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = lean_unbox(v_fst_684_);
v___y_750_ = v___x_767_;
goto v___jp_749_;
}
else
{
uint8_t v___x_768_; 
v___x_768_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_705_);
if (v___x_768_ == 0)
{
goto v___jp_759_;
}
else
{
if (v___x_693_ == 0)
{
v___y_750_ = v___x_693_;
goto v___jp_749_;
}
else
{
goto v___jp_759_;
}
}
}
v___jp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_messages_712_);
v___x_714_ = v___x_691_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_messages_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_689_);
v___x_714_ = v_reuseFailAlloc_723_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_box(v_recovering_709_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_714_);
lean_ctor_set(v___x_686_, 0, v___x_715_);
v___x_717_ = v___x_686_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_714_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_717_);
lean_ctor_set(v___x_682_, 0, v___y_711_);
v___x_719_ = v___x_682_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___y_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v_b_677_ = v___x_719_;
goto _start;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_inc_ref(v_stxStack_705_);
lean_inc_ref(v_inputCtx_675_);
v___x_731_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_675_, v_pos_706_, v_stxStack_705_, v___y_729_);
v___x_732_ = l_Lean_MessageLog_add(v___x_731_, v___x_726_);
if (v___y_728_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_del_object(v___x_691_);
lean_dec(v_snd_689_);
lean_del_object(v___x_686_);
lean_del_object(v___x_682_);
lean_dec_ref(v_pmctx_676_);
lean_dec_ref(v_inputCtx_675_);
v___x_733_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_705_);
lean_dec_ref(v_stxStack_705_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_box(v_recovering_709_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v___y_730_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
return v___x_737_;
}
else
{
lean_dec_ref(v_stxStack_705_);
v___y_711_ = v___y_730_;
v_messages_712_ = v___x_732_;
goto v___jp_710_;
}
}
v___jp_738_:
{
uint8_t v___x_742_; 
v___x_742_ = lean_unbox(v_fst_684_);
lean_dec(v_fst_684_);
if (v___x_742_ == 0)
{
v___y_728_ = v___y_741_;
v___y_729_ = v___y_739_;
v___y_730_ = v___y_740_;
goto v___jp_727_;
}
else
{
if (v___y_741_ == 0)
{
v___y_728_ = v___y_741_;
v___y_729_ = v___y_739_;
v___y_730_ = v___y_740_;
goto v___jp_727_;
}
else
{
lean_dec_ref(v___y_739_);
lean_dec(v_pos_706_);
lean_dec_ref(v_stxStack_705_);
v___y_711_ = v___y_740_;
v_messages_712_ = v___x_726_;
goto v___jp_710_;
}
}
}
v___jp_743_:
{
uint8_t v___x_746_; 
v___x_746_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_705_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_705_);
v___x_748_ = l_Lean_Syntax_getPos_x3f(v___x_747_, v___x_746_);
lean_dec(v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
v___y_739_ = v___y_744_;
v___y_740_ = v_pos_745_;
v___y_741_ = v_recovering_709_;
goto v___jp_738_;
}
else
{
lean_dec_ref(v___x_748_);
v___y_739_ = v___y_744_;
v___y_740_ = v_pos_745_;
v___y_741_ = v___x_746_;
goto v___jp_738_;
}
}
else
{
v___y_739_ = v___y_744_;
v___y_740_ = v_pos_745_;
v___y_741_ = v_recovering_709_;
goto v___jp_738_;
}
}
v___jp_749_:
{
if (lean_obj_tag(v_errorMsg_707_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_691_);
lean_dec(v_snd_689_);
lean_del_object(v___x_686_);
lean_dec(v_fst_684_);
lean_del_object(v___x_682_);
lean_dec(v_fst_680_);
lean_dec_ref(v_pmctx_676_);
lean_dec_ref(v_inputCtx_675_);
v___x_751_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_705_);
lean_dec_ref(v_stxStack_705_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_726_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_box(v___y_750_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_pos_706_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
else
{
lean_object* v_val_756_; uint8_t v___x_757_; 
v_val_756_ = lean_ctor_get(v_errorMsg_707_, 0);
lean_inc(v_val_756_);
lean_dec_ref(v_errorMsg_707_);
v___x_757_ = lean_nat_dec_eq(v_pos_706_, v_fst_680_);
lean_dec(v_fst_680_);
if (v___x_757_ == 0)
{
lean_inc(v_pos_706_);
v___y_744_ = v_val_756_;
v_pos_745_ = v_pos_706_;
goto v___jp_743_;
}
else
{
lean_object* v___x_758_; 
lean_inc(v_pos_706_);
lean_inc_ref(v_pmctx_676_);
lean_inc_ref(v_inputCtx_675_);
v___x_758_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_675_, v_pmctx_676_, v_pos_706_);
v___y_744_ = v_val_756_;
v_pos_745_ = v___x_758_;
goto v___jp_743_;
}
}
}
v___jp_759_:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_705_);
v___x_761_ = l_Lean_Syntax_isAntiquot(v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
v___y_750_ = v___x_761_;
goto v___jp_749_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_errorMsg_707_);
lean_dec_ref(v_stxStack_705_);
lean_del_object(v___x_691_);
lean_del_object(v___x_686_);
lean_del_object(v___x_682_);
lean_dec(v_fst_680_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_726_);
lean_ctor_set(v___x_762_, 1, v_snd_689_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_fst_684_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_pos_706_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v_b_677_ = v___x_764_;
goto _start;
}
}
}
else
{
lean_object* v_stx_769_; lean_object* v___x_771_; 
lean_dec(v_snd_689_);
lean_dec_ref(v_pmctx_676_);
lean_inc(v_fst_680_);
v_stx_769_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_675_, v_fst_680_);
lean_dec_ref(v_inputCtx_675_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_stx_769_);
v___x_771_ = v___x_691_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_stx_769_);
v___x_771_ = v_reuseFailAlloc_778_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_771_);
v___x_773_ = v___x_686_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_773_);
v___x_775_ = v___x_682_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_784_, lean_object* v_pmctx_785_, lean_object* v_mps_786_, lean_object* v_messages_787_){
_start:
{
lean_object* v_pos_788_; uint8_t v_recovering_789_; uint8_t v_hasLeading_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_830_; 
v_pos_788_ = lean_ctor_get(v_mps_786_, 0);
v_recovering_789_ = lean_ctor_get_uint8(v_mps_786_, sizeof(void*)*1);
v_hasLeading_790_ = lean_ctor_get_uint8(v_mps_786_, sizeof(void*)*1 + 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_mps_786_);
if (v_isSharedCheck_830_ == 0)
{
v___x_792_ = v_mps_786_;
v_isShared_793_ = v_isSharedCheck_830_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_pos_788_);
lean_dec(v_mps_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_830_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_stx_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_snd_800_; lean_object* v_snd_801_; lean_object* v_fst_802_; lean_object* v_fst_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_828_; 
v_stx_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_messages_787_);
lean_ctor_set(v___x_795_, 1, v_stx_794_);
v___x_796_ = lean_box(v_recovering_789_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_pos_788_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(v_inputCtx_784_, v_pmctx_785_, v___x_798_);
v_snd_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_snd_800_);
v_snd_801_ = lean_ctor_get(v_snd_800_, 1);
lean_inc(v_snd_801_);
v_fst_802_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_802_);
lean_dec_ref(v___x_799_);
v_fst_803_ = lean_ctor_get(v_snd_800_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_snd_800_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_snd_800_, 1);
lean_dec(v_unused_829_);
v___x_805_ = v_snd_800_;
v_isShared_806_ = v_isSharedCheck_828_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_fst_803_);
lean_dec(v_snd_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_828_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_827_; 
v_fst_807_ = lean_ctor_get(v_snd_801_, 0);
v_snd_808_ = lean_ctor_get(v_snd_801_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_snd_801_);
if (v_isSharedCheck_827_ == 0)
{
v___x_810_ = v_snd_801_;
v_isShared_811_ = v_isSharedCheck_827_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_inc(v_fst_807_);
lean_dec(v_snd_801_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_827_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_stx_813_; 
if (v_hasLeading_790_ == 0)
{
v_stx_813_ = v_snd_808_;
goto v___jp_812_;
}
else
{
lean_object* v___x_825_; lean_object* v_fst_826_; 
v___x_825_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_808_);
v_fst_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_fst_826_);
lean_dec_ref(v___x_825_);
v_stx_813_ = v_fst_826_;
goto v___jp_812_;
}
v___jp_812_:
{
uint8_t v___x_814_; lean_object* v___x_816_; 
v___x_814_ = 0;
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_fst_802_);
v___x_816_ = v___x_792_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_fst_802_);
v___x_816_ = v_reuseFailAlloc_824_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
uint8_t v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_unbox(v_fst_803_);
lean_dec(v_fst_803_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_817_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1 + 1, v___x_814_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_fst_807_);
lean_ctor_set(v___x_810_, 0, v___x_816_);
v___x_819_ = v___x_810_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_fst_807_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_819_);
lean_ctor_set(v___x_805_, 0, v_stx_813_);
v___x_821_ = v___x_805_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_stx_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_putStr_834_; lean_object* v___x_835_; 
v___x_833_ = lean_get_stdout();
v_putStr_834_ = lean_ctor_get(v___x_833_, 4);
lean_inc_ref(v_putStr_834_);
lean_dec_ref(v___x_833_);
v___x_835_ = lean_apply_2(v_putStr_834_, v_s_831_, lean_box(0));
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_839_){
_start:
{
uint32_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = 10;
v___x_842_ = lean_string_push(v_s_839_, v___x_841_);
v___x_843_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_847_, lean_object* v_msg_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = l_Lean_Message_toString(v_msg_848_, v___y_847_);
v___x_851_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_852_, lean_object* v_msg_853_, lean_object* v___y_854_){
_start:
{
uint8_t v___y_3322__boxed_855_; lean_object* v_res_856_; 
v___y_3322__boxed_855_ = lean_unbox(v___y_852_);
v_res_856_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_3322__boxed_855_, v_msg_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_857_, lean_object* v_as_858_, size_t v_i_859_, size_t v_stop_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_eq(v_i_859_, v_stop_860_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_array_uget_borrowed(v_as_858_, v_i_859_);
lean_inc_ref(v_f_857_);
lean_inc(v___x_864_);
v___x_865_ = lean_apply_2(v_f_857_, v___x_864_, lean_box(0));
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; size_t v___x_867_; size_t v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_859_, v___x_867_);
v_i_859_ = v___x_868_;
v_b_861_ = v_a_866_;
goto _start;
}
else
{
lean_dec_ref(v_f_857_);
return v___x_865_;
}
}
else
{
lean_object* v___x_870_; 
lean_dec_ref(v_f_857_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_b_861_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_871_, lean_object* v_as_872_, lean_object* v_i_873_, lean_object* v_stop_874_, lean_object* v_b_875_, lean_object* v___y_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; lean_object* v_res_879_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_874_);
lean_dec(v_stop_874_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_871_, v_as_872_, v_i_boxed_877_, v_stop_boxed_878_, v_b_875_);
lean_dec_ref(v_as_872_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v_cs_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_904_; 
v_cs_883_ = lean_ctor_get(v_x_881_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_904_ == 0)
{
v___x_885_ = v_x_881_;
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_cs_883_);
lean_dec(v_x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_array_get_size(v_cs_883_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_nat_dec_lt(v___x_887_, v___x_888_);
if (v___x_890_ == 0)
{
lean_object* v___x_892_; 
lean_dec_ref(v_cs_883_);
lean_dec_ref(v_f_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_892_ = v___x_885_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_889_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_le(v___x_888_, v___x_888_);
if (v___x_894_ == 0)
{
if (v___x_890_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_cs_883_);
lean_dec_ref(v_f_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_896_ = v___x_885_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_889_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
lean_del_object(v___x_885_);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_888_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_880_, v_cs_883_, v___x_898_, v___x_899_, v___x_889_);
lean_dec_ref(v_cs_883_);
return v___x_900_;
}
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
lean_del_object(v___x_885_);
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_888_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_880_, v_cs_883_, v___x_901_, v___x_902_, v___x_889_);
lean_dec_ref(v_cs_883_);
return v___x_903_;
}
}
}
}
else
{
lean_object* v_vs_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_926_; 
v_vs_905_ = lean_ctor_get(v_x_881_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_926_ == 0)
{
v___x_907_ = v_x_881_;
v_isShared_908_ = v_isSharedCheck_926_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_vs_905_);
lean_dec(v_x_881_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_926_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_vs_905_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; 
lean_dec_ref(v_vs_905_);
lean_dec_ref(v_f_880_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
lean_ctor_set(v___x_907_, 0, v___x_911_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
uint8_t v___x_916_; 
v___x_916_ = lean_nat_dec_le(v___x_910_, v___x_910_);
if (v___x_916_ == 0)
{
if (v___x_912_ == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v_vs_905_);
lean_dec_ref(v_f_880_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
lean_ctor_set(v___x_907_, 0, v___x_911_);
v___x_918_ = v___x_907_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_911_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_907_);
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lean_usize_of_nat(v___x_910_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_880_, v_vs_905_, v___x_920_, v___x_921_, v___x_911_);
lean_dec_ref(v_vs_905_);
return v___x_922_;
}
}
else
{
size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
lean_del_object(v___x_907_);
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_910_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_880_, v_vs_905_, v___x_923_, v___x_924_, v___x_911_);
lean_dec_ref(v_vs_905_);
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_927_, lean_object* v_as_928_, size_t v_i_929_, size_t v_stop_930_, lean_object* v_b_931_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_eq(v_i_929_, v_stop_930_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_array_uget_borrowed(v_as_928_, v_i_929_);
lean_inc(v___x_934_);
lean_inc_ref(v_f_927_);
v___x_935_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_927_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; size_t v___x_937_; size_t v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_929_, v___x_937_);
v_i_929_ = v___x_938_;
v_b_931_ = v_a_936_;
goto _start;
}
else
{
lean_dec_ref(v_f_927_);
return v___x_935_;
}
}
else
{
lean_object* v___x_940_; 
lean_dec_ref(v_f_927_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_931_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_941_, lean_object* v_as_942_, lean_object* v_i_943_, lean_object* v_stop_944_, lean_object* v_b_945_, lean_object* v___y_946_){
_start:
{
size_t v_i_boxed_947_; size_t v_stop_boxed_948_; lean_object* v_res_949_; 
v_i_boxed_947_ = lean_unbox_usize(v_i_943_);
lean_dec(v_i_943_);
v_stop_boxed_948_ = lean_unbox_usize(v_stop_944_);
lean_dec(v_stop_944_);
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_941_, v_as_942_, v_i_boxed_947_, v_stop_boxed_948_, v_b_945_);
lean_dec_ref(v_as_942_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_950_, lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_950_, v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_954_, lean_object* v_t_955_){
_start:
{
lean_object* v_root_957_; lean_object* v_tail_958_; lean_object* v___x_959_; 
v_root_957_ = lean_ctor_get(v_t_955_, 0);
lean_inc_ref(v_root_957_);
v_tail_958_ = lean_ctor_get(v_t_955_, 1);
lean_inc_ref(v_tail_958_);
lean_dec_ref(v_t_955_);
lean_inc_ref(v_f_954_);
v___x_959_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_954_, v_root_957_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_980_; 
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_959_, 0);
lean_dec(v_unused_981_);
v___x_961_ = v___x_959_;
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
else
{
lean_dec(v___x_959_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_array_get_size(v_tail_958_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_nat_dec_lt(v___x_963_, v___x_964_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; 
lean_dec_ref(v_tail_958_);
lean_dec_ref(v_f_954_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_965_);
v___x_968_ = v___x_961_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_965_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
uint8_t v___x_970_; 
v___x_970_ = lean_nat_dec_le(v___x_964_, v___x_964_);
if (v___x_970_ == 0)
{
if (v___x_966_ == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_tail_958_);
lean_dec_ref(v_f_954_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_965_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_965_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; 
lean_del_object(v___x_961_);
v___x_974_ = ((size_t)0ULL);
v___x_975_ = lean_usize_of_nat(v___x_964_);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_954_, v_tail_958_, v___x_974_, v___x_975_, v___x_965_);
lean_dec_ref(v_tail_958_);
return v___x_976_;
}
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
lean_del_object(v___x_961_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_964_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_954_, v_tail_958_, v___x_977_, v___x_978_, v___x_965_);
lean_dec_ref(v_tail_958_);
return v___x_979_;
}
}
}
}
else
{
lean_dec_ref(v_tail_958_);
lean_dec_ref(v_f_954_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_982_, lean_object* v_t_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_982_, v_t_983_);
return v_res_985_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_987_, lean_object* v_x_988_, size_t v_x_989_, size_t v_x_990_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_object* v_cs_992_; lean_object* v___x_993_; size_t v___x_994_; lean_object* v_j_995_; lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v_cs_992_ = lean_ctor_get(v_x_988_, 0);
lean_inc_ref(v_cs_992_);
lean_dec_ref(v_x_988_);
v___x_993_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_994_ = lean_usize_shift_right(v_x_989_, v_x_990_);
v_j_995_ = lean_usize_to_nat(v___x_994_);
v___x_996_ = lean_array_get_borrowed(v___x_993_, v_cs_992_, v_j_995_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_shift_left(v___x_997_, v_x_990_);
v___x_999_ = lean_usize_sub(v___x_998_, v___x_997_);
v___x_1000_ = lean_usize_land(v_x_989_, v___x_999_);
v___x_1001_ = ((size_t)5ULL);
v___x_1002_ = lean_usize_sub(v_x_990_, v___x_1001_);
lean_inc(v___x_996_);
lean_inc_ref(v_f_987_);
v___x_1003_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_987_, v___x_996_, v___x_1000_, v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1025_; 
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1003_, 0);
lean_dec(v_unused_1026_);
v___x_1005_ = v___x_1003_;
v_isShared_1006_ = v_isSharedCheck_1025_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v___x_1003_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1025_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_j_995_, v___x_1007_);
lean_dec(v_j_995_);
v___x_1009_ = lean_array_get_size(v_cs_992_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_nat_dec_lt(v___x_1008_, v___x_1009_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1013_; 
lean_dec(v___x_1008_);
lean_dec_ref(v_cs_992_);
lean_dec_ref(v_f_987_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1010_);
v___x_1013_ = v___x_1005_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1010_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_nat_dec_le(v___x_1009_, v___x_1009_);
if (v___x_1015_ == 0)
{
if (v___x_1011_ == 0)
{
lean_object* v___x_1017_; 
lean_dec(v___x_1008_);
lean_dec_ref(v_cs_992_);
lean_dec_ref(v_f_987_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1010_);
v___x_1017_ = v___x_1005_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1010_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
lean_del_object(v___x_1005_);
v___x_1019_ = lean_usize_of_nat(v___x_1008_);
lean_dec(v___x_1008_);
v___x_1020_ = lean_usize_of_nat(v___x_1009_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_987_, v_cs_992_, v___x_1019_, v___x_1020_, v___x_1010_);
lean_dec_ref(v_cs_992_);
return v___x_1021_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
lean_del_object(v___x_1005_);
v___x_1022_ = lean_usize_of_nat(v___x_1008_);
lean_dec(v___x_1008_);
v___x_1023_ = lean_usize_of_nat(v___x_1009_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_987_, v_cs_992_, v___x_1022_, v___x_1023_, v___x_1010_);
lean_dec_ref(v_cs_992_);
return v___x_1024_;
}
}
}
}
else
{
lean_dec(v_j_995_);
lean_dec_ref(v_cs_992_);
lean_dec_ref(v_f_987_);
return v___x_1003_;
}
}
else
{
lean_object* v_vs_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1048_; 
v_vs_1027_ = lean_ctor_get(v_x_988_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1029_ = v_x_988_;
v_isShared_1030_ = v_isSharedCheck_1048_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_vs_1027_);
lean_dec(v_x_988_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1048_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1031_ = lean_usize_to_nat(v_x_989_);
v___x_1032_ = lean_array_get_size(v_vs_1027_);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1036_; 
lean_dec(v___x_1031_);
lean_dec_ref(v_vs_1027_);
lean_dec_ref(v_f_987_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1033_);
v___x_1036_ = v___x_1029_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_le(v___x_1032_, v___x_1032_);
if (v___x_1038_ == 0)
{
if (v___x_1034_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v___x_1031_);
lean_dec_ref(v_vs_1027_);
lean_dec_ref(v_f_987_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1033_);
v___x_1040_ = v___x_1029_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1033_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
lean_del_object(v___x_1029_);
v___x_1042_ = lean_usize_of_nat(v___x_1031_);
lean_dec(v___x_1031_);
v___x_1043_ = lean_usize_of_nat(v___x_1032_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_987_, v_vs_1027_, v___x_1042_, v___x_1043_, v___x_1033_);
lean_dec_ref(v_vs_1027_);
return v___x_1044_;
}
}
else
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1029_);
v___x_1045_ = lean_usize_of_nat(v___x_1031_);
lean_dec(v___x_1031_);
v___x_1046_ = lean_usize_of_nat(v___x_1032_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_987_, v_vs_1027_, v___x_1045_, v___x_1046_, v___x_1033_);
lean_dec_ref(v_vs_1027_);
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_x_3520__boxed_1054_; size_t v_x_3521__boxed_1055_; lean_object* v_res_1056_; 
v_x_3520__boxed_1054_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_x_3521__boxed_1055_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1049_, v_x_1050_, v_x_3520__boxed_1054_, v_x_3521__boxed_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1057_, lean_object* v_t_1058_, lean_object* v_start_1059_){
_start:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_nat_dec_eq(v_start_1059_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v_root_1063_; lean_object* v_tail_1064_; size_t v_shift_1065_; lean_object* v_tailOff_1066_; uint8_t v___x_1067_; 
v_root_1063_ = lean_ctor_get(v_t_1058_, 0);
lean_inc_ref(v_root_1063_);
v_tail_1064_ = lean_ctor_get(v_t_1058_, 1);
lean_inc_ref(v_tail_1064_);
v_shift_1065_ = lean_ctor_get_usize(v_t_1058_, 4);
v_tailOff_1066_ = lean_ctor_get(v_t_1058_, 3);
lean_inc(v_tailOff_1066_);
lean_dec_ref(v_t_1058_);
v___x_1067_ = lean_nat_dec_le(v_tailOff_1066_, v_start_1059_);
if (v___x_1067_ == 0)
{
size_t v___x_1068_; lean_object* v___x_1069_; 
lean_dec(v_tailOff_1066_);
v___x_1068_ = lean_usize_of_nat(v_start_1059_);
lean_inc_ref(v_f_1057_);
v___x_1069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1057_, v_root_1063_, v___x_1068_, v_shift_1065_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1089_; 
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1069_, 0);
lean_dec(v_unused_1090_);
v___x_1071_ = v___x_1069_;
v_isShared_1072_ = v_isSharedCheck_1089_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v___x_1069_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1089_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_array_get_size(v_tail_1064_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_nat_dec_lt(v___x_1061_, v___x_1073_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1077_; 
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1074_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_nat_dec_le(v___x_1073_, v___x_1073_);
if (v___x_1079_ == 0)
{
if (v___x_1075_ == 0)
{
lean_object* v___x_1081_; 
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1074_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
lean_del_object(v___x_1071_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = lean_usize_of_nat(v___x_1073_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1083_, v___x_1084_, v___x_1074_);
lean_dec_ref(v_tail_1064_);
return v___x_1085_;
}
}
else
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
lean_del_object(v___x_1071_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = lean_usize_of_nat(v___x_1073_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1086_, v___x_1087_, v___x_1074_);
lean_dec_ref(v_tail_1064_);
return v___x_1088_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
return v___x_1069_;
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
lean_dec_ref(v_root_1063_);
v___x_1091_ = lean_nat_sub(v_start_1059_, v_tailOff_1066_);
lean_dec(v_tailOff_1066_);
v___x_1092_ = lean_array_get_size(v_tail_1064_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_lt(v___x_1091_, v___x_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v___x_1091_);
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
return v___x_1095_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_le(v___x_1092_, v___x_1092_);
if (v___x_1096_ == 0)
{
if (v___x_1094_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v___x_1091_);
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1093_);
return v___x_1097_;
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_usize_of_nat(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1099_ = lean_usize_of_nat(v___x_1092_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1098_, v___x_1099_, v___x_1093_);
lean_dec_ref(v_tail_1064_);
return v___x_1100_;
}
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_usize_of_nat(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1102_ = lean_usize_of_nat(v___x_1092_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1101_, v___x_1102_, v___x_1093_);
lean_dec_ref(v_tail_1064_);
return v___x_1103_;
}
}
}
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1057_, v_t_1058_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1105_, lean_object* v_t_1106_, lean_object* v_start_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1105_, v_t_1106_, v_start_1107_);
lean_dec(v_start_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1110_, lean_object* v_f_1111_){
_start:
{
lean_object* v_unreported_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_unreported_1113_ = lean_ctor_get(v_log_1110_, 1);
lean_inc_ref(v_unreported_1113_);
lean_dec_ref(v_log_1110_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1111_, v_unreported_1113_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1116_, lean_object* v_f_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1116_, v_f_1117_);
return v_res_1119_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1122_ = lean_mk_io_user_error(v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1123_, lean_object* v_inputCtx_1124_, lean_object* v_state_1125_, lean_object* v_msgs_1126_, lean_object* v_stxs_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_snd_1134_; lean_object* v_fst_1135_; lean_object* v_fst_1136_; lean_object* v_snd_1137_; uint8_t v___y_1139_; uint8_t v___x_1160_; 
v___x_1129_ = l_Lean_Options_empty;
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_box(0);
lean_inc_ref(v_env_1123_);
v___x_1132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1132_, 0, v_env_1123_);
lean_ctor_set(v___x_1132_, 1, v___x_1129_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
lean_inc_ref(v_inputCtx_1124_);
v___x_1133_ = l_Lean_Parser_parseCommand(v_inputCtx_1124_, v___x_1132_, v_state_1125_, v_msgs_1126_);
v_snd_1134_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_snd_1134_);
v_fst_1135_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_fst_1135_);
lean_dec_ref(v___x_1133_);
v_fst_1136_ = lean_ctor_get(v_snd_1134_, 0);
lean_inc(v_fst_1136_);
v_snd_1137_ = lean_ctor_get(v_snd_1134_, 1);
lean_inc(v_snd_1137_);
lean_dec(v_snd_1134_);
lean_inc(v_fst_1135_);
v___x_1160_ = l_Lean_Parser_isTerminalCommand(v_fst_1135_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_array_push(v_stxs_1127_, v_fst_1135_);
v_state_1125_ = v_fst_1136_;
v_msgs_1126_ = v_snd_1137_;
v_stxs_1127_ = v___x_1161_;
goto _start;
}
else
{
uint8_t v___x_1163_; 
lean_dec(v_fst_1136_);
lean_dec_ref(v_inputCtx_1124_);
lean_dec_ref(v_env_1123_);
v___x_1163_ = l_Lean_MessageLog_hasUnreported(v_snd_1137_);
if (v___x_1163_ == 0)
{
if (v___x_1160_ == 0)
{
lean_dec(v_fst_1135_);
lean_dec_ref(v_stxs_1127_);
v___y_1139_ = v___x_1160_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_snd_1137_);
v___x_1164_ = lean_array_push(v_stxs_1127_, v_fst_1135_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
else
{
uint8_t v___x_1166_; 
lean_dec(v_fst_1135_);
lean_dec_ref(v_stxs_1127_);
v___x_1166_ = 0;
v___y_1139_ = v___x_1166_;
goto v___jp_1138_;
}
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(v___y_1139_);
v___f_1141_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1141_, 0, v___x_1140_);
v___x_1142_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1137_, v___f_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1142_, 0);
lean_dec(v_unused_1151_);
v___x_1144_ = v___x_1142_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v___x_1142_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1142_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1167_, lean_object* v_inputCtx_1168_, lean_object* v_state_1169_, lean_object* v_msgs_1170_, lean_object* v_stxs_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1167_, v_inputCtx_1168_, v_state_1169_, v_msgs_1170_, v_stxs_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1174_, lean_object* v_inputCtx_1175_, lean_object* v_s_1176_, lean_object* v_msgs_1177_, lean_object* v_stxs_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1174_, v_inputCtx_1175_, v_s_1176_, v_msgs_1177_, v_stxs_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1181_, lean_object* v_inputCtx_1182_, lean_object* v_s_1183_, lean_object* v_msgs_1184_, lean_object* v_stxs_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Parser_testParseModuleAux(v_env_1181_, v_inputCtx_1182_, v_s_1183_, v_msgs_1184_, v_stxs_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1196_, lean_object* v_fname_1197_, lean_object* v_contents_1198_){
_start:
{
uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v_inputCtx_1202_; lean_object* v___x_1203_; 
v___x_1200_ = 1;
v___x_1201_ = lean_string_utf8_byte_size(v_contents_1198_);
v_inputCtx_1202_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1198_, v_fname_1197_, v___x_1200_, v___x_1201_);
lean_inc_ref(v_inputCtx_1202_);
v___x_1203_ = l_Lean_Parser_parseHeader(v_inputCtx_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v_snd_1205_; lean_object* v_fst_1206_; lean_object* v_fst_1207_; lean_object* v_snd_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v_snd_1205_ = lean_ctor_get(v_a_1204_, 1);
lean_inc(v_snd_1205_);
v_fst_1206_ = lean_ctor_get(v_a_1204_, 0);
lean_inc(v_fst_1206_);
lean_dec(v_a_1204_);
v_fst_1207_ = lean_ctor_get(v_snd_1205_, 0);
lean_inc(v_fst_1207_);
v_snd_1208_ = lean_ctor_get(v_snd_1205_, 1);
lean_inc(v_snd_1208_);
lean_dec(v_snd_1205_);
v___x_1209_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1210_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1196_, v_inputCtx_1202_, v_fst_1207_, v_snd_1208_, v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1226_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1226_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1226_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1215_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1216_ = l_Lean_mkListNode(v_a_1211_);
v___x_1217_ = lean_unsigned_to_nat(2u);
v___x_1218_ = lean_mk_empty_array_with_capacity(v___x_1217_);
v___x_1219_ = lean_array_push(v___x_1218_, v_fst_1206_);
v___x_1220_ = lean_array_push(v___x_1219_, v___x_1216_);
v___x_1221_ = lean_box(2);
v___x_1222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1215_);
lean_ctor_set(v___x_1222_, 2, v___x_1220_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1222_);
v___x_1224_ = v___x_1213_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_fst_1206_);
v_a_1227_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1210_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1210_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v_inputCtx_1202_);
lean_dec_ref(v_env_1196_);
v_a_1235_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1203_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1203_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1243_, lean_object* v_fname_1244_, lean_object* v_contents_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Parser_testParseModule(v_env_1243_, v_fname_1244_, v_contents_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1248_, lean_object* v_fname_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_IO_FS_readFile(v_fname_1249_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = l_Lean_Parser_testParseModule(v_env_1248_, v_fname_1249_, v_a_1252_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_fname_1249_);
lean_dec_ref(v_env_1248_);
v_a_1254_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1262_, lean_object* v_fname_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Parser_testParseFile(v_env_1262_, v_fname_1263_);
return v_res_1265_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Module(builtin);
}
#ifdef __cplusplus
}
#endif
