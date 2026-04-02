// Lean compiler output
// Module: Lean.Parser.Module
// Imports: public import Lean.Parser.Module.Syntax meta import Lean.Parser.Module.Syntax import Init.While meta import Lean.Parser.Extra
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
v___x_4_ = lean_panic_fn_borrowed(v___x_3_, v_msg_2_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_8_ = ((lean_object*)(l_Lean_Parser_Module_updateTokens___closed__2));
v___x_9_ = lean_unsigned_to_nat(26u);
v___x_10_ = lean_unsigned_to_nat(24u);
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
v___x_73_ = l_Lean_Parser_Error_toString(v___y_66_);
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___x_75_ = l_Lean_MessageData_ofFormat(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_76_, 0, v___y_67_);
lean_ctor_set(v___x_76_, 1, v___y_65_);
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
lean_inc_ref_n(v_fileMap_82_, 2);
lean_dec_ref(v_c_60_);
v___x_83_ = l_Lean_FileMap_toPosition(v_fileMap_82_, v_pos_78_);
lean_dec(v_pos_78_);
if (lean_obj_tag(v_endPos_x3f_79_) == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_fileMap_82_);
v___x_84_ = lean_box(0);
v___y_65_ = v___x_83_;
v___y_66_ = v_e_80_;
v___y_67_ = v_fileName_81_;
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
v___y_65_ = v___x_83_;
v___y_66_ = v_e_80_;
v___y_67_ = v_fileName_81_;
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
v___x_105_ = lean_nat_dec_eq(v_stopPos_104_, v___y_98_);
lean_dec(v_stopPos_104_);
if (v___x_105_ == 0)
{
lean_dec(v_startPos_103_);
v_pos_78_ = v___y_98_;
v_endPos_x3f_79_ = v___y_97_;
v_e_80_ = v_e_100_;
goto v___jp_77_;
}
else
{
lean_dec(v___y_98_);
v_pos_78_ = v_startPos_103_;
v_endPos_x3f_79_ = v___y_97_;
v_e_80_ = v_e_100_;
goto v___jp_77_;
}
}
else
{
lean_dec(v___x_101_);
v_pos_78_ = v___y_98_;
v_endPos_x3f_79_ = v___y_97_;
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
v___y_97_ = v_endPos_x3f_108_;
v___y_98_ = v_pos_107_;
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
v___y_97_ = v_endPos_x3f_108_;
v___y_98_ = v_pos_107_;
v___y_99_ = v___x_114_;
goto v___jp_96_;
}
default: 
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
v___y_97_ = v_endPos_x3f_108_;
v___y_98_ = v_pos_107_;
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
v___x_211_ = l_Lean_FileMap_toPosition(v___y_207_, v___y_210_);
lean_dec(v___y_210_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
v___x_213_ = 2;
v___x_214_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_215_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_215_, 0, v___y_208_);
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
lean_inc_ref_n(v_fileMap_219_, 2);
lean_dec_ref(v_inputCtx_202_);
v___x_220_ = l_Lean_FileMap_toPosition(v_fileMap_219_, v___y_217_);
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v_ref_203_, v___x_205_);
if (lean_obj_tag(v___x_221_) == 0)
{
v___y_207_ = v_fileMap_219_;
v___y_208_ = v_fileName_218_;
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
v___y_207_ = v_fileMap_219_;
v___y_208_ = v_fileName_218_;
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
uint8_t v___x_5643__boxed_230_; lean_object* v_res_231_; 
v___x_5643__boxed_230_ = lean_unbox(v___x_226_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_5643__boxed_230_, v_inputCtx_227_, v_ref_228_, v_msg_229_);
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
lean_object* v___y_295_; lean_object* v_messages_296_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v_messages_304_; lean_object* v___y_310_; lean_object* v___y_311_; uint8_t v___y_312_; lean_object* v___y_313_; lean_object* v___x_334_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v_allTk_x3f_338_; lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v_metaTk_x3f_352_; lean_object* v_pubTk_x3f_364_; lean_object* v___x_374_; uint8_t v___x_375_; 
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
if (lean_obj_tag(v___y_303_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_val_305_ = lean_ctor_get(v___y_303_, 0);
lean_inc(v_val_305_);
lean_dec_ref(v___y_303_);
v___x_306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_277_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_305_, v___x_306_);
lean_dec(v_val_305_);
v___x_308_ = l_Lean_MessageLog_add(v___x_307_, v_messages_304_);
v___y_295_ = v___y_302_;
v_messages_296_ = v___x_308_;
goto v___jp_294_;
}
else
{
lean_dec(v___y_303_);
v___y_295_ = v___y_302_;
v_messages_296_ = v_messages_304_;
goto v___jp_294_;
}
}
v___jp_309_:
{
if (lean_obj_tag(v___y_310_) == 1)
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_dec_ref(v___y_310_);
lean_dec(v___y_313_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___y_311_, 0);
lean_dec(v_unused_333_);
v___x_315_ = v___y_311_;
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___y_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
if (v___y_312_ == 0)
{
lean_del_object(v___x_315_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_313_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v_val_317_ = lean_ctor_get(v___y_310_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___y_310_);
v___x_318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_313_, v___y_312_);
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
lean_dec(v___y_311_);
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
lean_dec(v___y_337_);
v___y_310_ = v_allTk_x3f_338_;
v___y_311_ = v___y_336_;
v___y_312_ = v___x_341_;
v___y_313_ = v___x_344_;
goto v___jp_309_;
}
else
{
lean_dec(v___x_344_);
if (lean_obj_tag(v___y_336_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_val_345_ = lean_ctor_get(v___y_336_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___y_336_);
v___x_346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
lean_inc_ref(v_inputCtx_277_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_293_, v_inputCtx_277_, v_val_345_, v___x_346_);
lean_dec(v_val_345_);
v___x_348_ = l_Lean_MessageLog_add(v___x_347_, v_b_282_);
v___y_302_ = v_allTk_x3f_338_;
v___y_303_ = v___y_337_;
v_messages_304_ = v___x_348_;
goto v___jp_301_;
}
else
{
lean_dec(v___y_336_);
v___y_302_ = v_allTk_x3f_338_;
v___y_303_ = v___y_337_;
v_messages_304_ = v_b_282_;
goto v___jp_301_;
}
}
}
else
{
lean_dec(v___y_337_);
v___y_310_ = v_allTk_x3f_338_;
v___y_311_ = v___y_336_;
v___y_312_ = v___x_341_;
v___y_313_ = v___x_344_;
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
v___y_336_ = v___y_351_;
v___y_337_ = v_metaTk_x3f_352_;
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
v___y_336_ = v___y_351_;
v___y_337_ = v_metaTk_x3f_352_;
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
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_543_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_543_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_543_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_543_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_fn_428_; lean_object* v_inputString_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_stxStack_440_; lean_object* v_pos_441_; lean_object* v_errorMsg_442_; lean_object* v___y_444_; uint8_t v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; lean_object* v___y_462_; lean_object* v_messages_463_; size_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___x_492_; lean_object* v___y_494_; lean_object* v___y_495_; size_t v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_moduleTk_x3f_500_; lean_object* v___y_510_; uint8_t v___x_540_; 
v___x_427_ = l_Lean_Parser_Module_header;
v_fn_428_ = lean_ctor_get(v___x_427_, 1);
v_inputString_429_ = lean_ctor_get(v_inputCtx_419_, 0);
lean_inc(v_a_423_);
v___x_430_ = l_Lean_Parser_getTokenTable(v_a_423_);
v___x_431_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_428_);
v___x_432_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_432_, 0, v___x_431_);
lean_closure_set(v___x_432_, 1, v_fn_428_);
v___x_433_ = l_Lean_Parser_Module_updateTokens(v___x_430_);
v___x_434_ = l_Lean_Options_empty;
v___x_435_ = lean_box(0);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v_a_423_);
lean_ctor_set(v___x_437_, 1, v___x_434_);
lean_ctor_set(v___x_437_, 2, v___x_435_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
v___x_438_ = l_Lean_Parser_mkParserState(v_inputString_429_);
lean_inc_ref(v_inputCtx_419_);
v___x_439_ = l_Lean_Parser_ParserFn_run(v___x_432_, v_inputCtx_419_, v___x_437_, v___x_433_, v___x_438_);
v_stxStack_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc_ref(v_stxStack_440_);
v_pos_441_ = lean_ctor_get(v___x_439_, 2);
lean_inc(v_pos_441_);
v_errorMsg_442_ = lean_ctor_get(v___x_439_, 4);
lean_inc(v_errorMsg_442_);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_540_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_440_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_440_);
lean_dec_ref(v_stxStack_440_);
v___y_510_ = v___x_541_;
goto v___jp_509_;
}
else
{
lean_object* v___x_542_; 
lean_dec_ref(v_stxStack_440_);
v___x_542_ = lean_box(0);
v___y_510_ = v___x_542_;
goto v___jp_509_;
}
v___jp_443_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_448_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_448_, 0, v_pos_441_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___y_445_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1 + 1, v___y_447_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___y_444_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_446_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_450_);
v___x_452_ = v___x_425_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
v___jp_454_:
{
if (v___y_456_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 1;
v___y_444_ = v___y_455_;
v___y_445_ = v___y_458_;
v___y_446_ = v___y_457_;
v___y_447_ = v___x_459_;
goto v___jp_443_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
v___y_444_ = v___y_455_;
v___y_445_ = v___y_458_;
v___y_446_ = v___y_457_;
v___y_447_ = v___x_460_;
goto v___jp_443_;
}
}
v___jp_461_:
{
lean_object* v___x_464_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_464_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_462_);
v_fst_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_fst_465_);
v_snd_466_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v___x_464_);
v___x_467_ = lean_box(0);
v___x_468_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_442_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 1;
v___x_470_ = lean_unbox(v_snd_466_);
lean_dec(v_snd_466_);
v___y_455_ = v_messages_463_;
v___y_456_ = v___x_470_;
v___y_457_ = v_fst_465_;
v___y_458_ = v___x_469_;
goto v___jp_454_;
}
else
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 0;
v___x_472_ = lean_unbox(v_snd_466_);
lean_dec(v_snd_466_);
v___y_455_ = v_messages_463_;
v___y_456_ = v___x_472_;
v___y_457_ = v_fst_465_;
v___y_458_ = v___x_471_;
goto v___jp_454_;
}
}
v___jp_473_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; size_t v_sz_481_; lean_object* v___x_482_; 
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = l_Lean_Syntax_getArg(v___y_475_, v___x_478_);
v___x_480_ = l_Lean_Syntax_getArgs(v___x_479_);
lean_dec(v___x_479_);
v_sz_481_ = lean_array_size(v___x_480_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_419_, v___y_476_, v___x_480_, v_sz_481_, v___y_474_, v___y_477_);
lean_dec_ref(v___x_480_);
lean_dec(v___y_476_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
v___y_462_ = v___y_475_;
v_messages_463_ = v_a_483_;
goto v___jp_461_;
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___y_475_);
lean_dec(v_errorMsg_442_);
lean_dec(v_pos_441_);
lean_del_object(v___x_425_);
v_a_484_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
v___jp_493_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l_Lean_Syntax_getArg(v___y_498_, v___x_501_);
v___x_503_ = l_Lean_Syntax_isNone(v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
lean_inc(v___x_502_);
v___x_504_ = l_Lean_Syntax_matchesNull(v___x_502_, v___x_501_);
if (v___x_504_ == 0)
{
lean_dec(v___x_502_);
lean_dec(v_moduleTk_x3f_500_);
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_498_;
v_messages_463_ = v___y_499_;
goto v___jp_461_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_505_ = l_Lean_Syntax_getArg(v___x_502_, v___x_492_);
lean_dec(v___x_502_);
v___x_506_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_494_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v___y_495_);
v___x_507_ = l_Lean_Name_mkStr4(v___y_495_, v___y_497_, v___y_494_, v___x_506_);
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_505_, v___x_507_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_moduleTk_x3f_500_);
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_498_;
v_messages_463_ = v___y_499_;
goto v___jp_461_;
}
else
{
v___y_474_ = v___y_496_;
v___y_475_ = v___y_498_;
v___y_476_ = v_moduleTk_x3f_500_;
v___y_477_ = v___y_499_;
goto v___jp_473_;
}
}
}
else
{
lean_dec(v___x_502_);
v___y_474_ = v___y_496_;
v___y_475_ = v___y_498_;
v___y_476_ = v_moduleTk_x3f_500_;
v___y_477_ = v___y_499_;
goto v___jp_473_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; 
v___x_511_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_512_ = l_Lean_Parser_ParserState_allErrors(v___x_439_);
v_sz_513_ = lean_array_size(v___x_512_);
v___x_514_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_419_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_419_, v___x_512_, v_sz_513_, v___x_514_, v___x_511_);
lean_dec_ref(v___x_512_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_520_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_510_);
v___x_521_ = l_Lean_Syntax_isOfKind(v___y_510_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_510_;
v_messages_463_ = v_a_516_;
goto v___jp_461_;
}
else
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = l_Lean_Syntax_getArg(v___y_510_, v___x_492_);
v___x_523_ = l_Lean_Syntax_isNone(v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_522_);
v___x_525_ = l_Lean_Syntax_matchesNull(v___x_522_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v___x_522_);
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_510_;
v_messages_463_ = v_a_516_;
goto v___jp_461_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = l_Lean_Syntax_getArg(v___x_522_, v___x_492_);
lean_dec(v___x_522_);
v___x_527_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_526_);
v___x_528_ = l_Lean_Syntax_isOfKind(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_526_);
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_510_;
v_messages_463_ = v_a_516_;
goto v___jp_461_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = l_Lean_Syntax_getArg(v___x_526_, v___x_492_);
lean_dec(v___x_526_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___y_494_ = v___x_519_;
v___y_495_ = v___x_517_;
v___y_496_ = v___x_514_;
v___y_497_ = v___x_518_;
v___y_498_ = v___y_510_;
v___y_499_ = v_a_516_;
v_moduleTk_x3f_500_ = v___x_530_;
goto v___jp_493_;
}
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v___x_522_);
v___x_531_ = lean_box(0);
v___y_494_ = v___x_519_;
v___y_495_ = v___x_517_;
v___y_496_ = v___x_514_;
v___y_497_ = v___x_518_;
v___y_498_ = v___y_510_;
v___y_499_ = v_a_516_;
v_moduleTk_x3f_500_ = v___x_531_;
goto v___jp_493_;
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v___y_510_);
lean_dec(v_errorMsg_442_);
lean_dec(v_pos_441_);
lean_del_object(v___x_425_);
lean_dec_ref(v_inputCtx_419_);
v_a_532_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_515_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_515_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_inputCtx_419_);
v_a_544_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_422_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_422_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Parser_parseHeader(v_inputCtx_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_562_, lean_object* v_pos_563_){
_start:
{
lean_object* v___y_565_; lean_object* v_inputString_575_; lean_object* v_endPos_576_; uint8_t v___x_577_; 
v_inputString_575_ = lean_ctor_get(v_inputCtx_562_, 0);
v_endPos_576_ = lean_ctor_get(v_inputCtx_562_, 3);
v___x_577_ = lean_nat_dec_le(v_pos_563_, v_endPos_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_inc(v_endPos_576_);
lean_inc(v_pos_563_);
lean_inc_ref(v_inputString_575_);
v___x_578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_578_, 0, v_inputString_575_);
lean_ctor_set(v___x_578_, 1, v_pos_563_);
lean_ctor_set(v___x_578_, 2, v_endPos_576_);
v___y_565_ = v___x_578_;
goto v___jp_564_;
}
else
{
lean_object* v___x_579_; 
lean_inc_n(v_pos_563_, 2);
lean_inc_ref(v_inputString_575_);
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v_inputString_575_);
lean_ctor_set(v___x_579_, 1, v_pos_563_);
lean_ctor_set(v___x_579_, 2, v_pos_563_);
v___y_565_ = v___x_579_;
goto v___jp_564_;
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_atom_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc(v_pos_563_);
lean_inc_ref(v___y_565_);
v___x_566_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_566_, 0, v___y_565_);
lean_ctor_set(v___x_566_, 1, v_pos_563_);
lean_ctor_set(v___x_566_, 2, v___y_565_);
lean_ctor_set(v___x_566_, 3, v_pos_563_);
v___x_567_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_568_, 0, v___x_566_);
lean_ctor_set(v_atom_568_, 1, v___x_567_);
v___x_569_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_array_push(v___x_571_, v_atom_568_);
v___x_573_ = lean_box(2);
v___x_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_569_);
lean_ctor_set(v___x_574_, 2, v___x_572_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_580_, lean_object* v_pos_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_580_, v_pos_581_);
lean_dec_ref(v_inputCtx_580_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_594_){
_start:
{
uint8_t v___y_596_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_594_);
v___x_600_ = l_Lean_Syntax_isOfKind(v_s_594_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_594_);
v___x_602_ = l_Lean_Syntax_isOfKind(v_s_594_, v___x_601_);
v___y_596_ = v___x_602_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_600_;
goto v___jp_595_;
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_598_ = l_Lean_Syntax_isOfKind(v_s_594_, v___x_597_);
return v___x_598_;
}
else
{
lean_dec(v_s_594_);
return v___y_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* v_s_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_Parser_isTerminalCommand(v_s_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2(void){
_start:
{
uint32_t v___x_610_; lean_object* v___x_611_; 
v___x_610_ = 32;
v___x_611_ = l_Char_utf8Size(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_612_, lean_object* v_pmctx_613_, lean_object* v_pos_614_){
_start:
{
lean_object* v_inputString_615_; lean_object* v_env_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_s_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_s_625_; lean_object* v_errorMsg_626_; 
v_inputString_615_ = lean_ctor_get(v_inputCtx_612_, 0);
v_env_616_ = lean_ctor_get(v_pmctx_613_, 0);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_619_ = l_Lean_Parser_SyntaxStack_empty;
v___x_620_ = l_Lean_Parser_initCacheForInput(v_inputString_615_);
v___x_621_ = lean_box(0);
lean_inc(v_pos_614_);
v_s_622_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_622_, 0, v___x_619_);
lean_ctor_set(v_s_622_, 1, v___x_617_);
lean_ctor_set(v_s_622_, 2, v_pos_614_);
lean_ctor_set(v_s_622_, 3, v___x_620_);
lean_ctor_set(v_s_622_, 4, v___x_621_);
lean_ctor_set(v_s_622_, 5, v___x_618_);
v___x_623_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_616_);
v___x_624_ = l_Lean_Parser_getTokenTable(v_env_616_);
v_s_625_ = l_Lean_Parser_ParserFn_run(v___x_623_, v_inputCtx_612_, v_pmctx_613_, v___x_624_, v_s_622_);
v_errorMsg_626_ = lean_ctor_get(v_s_625_, 4);
lean_inc(v_errorMsg_626_);
if (lean_obj_tag(v_errorMsg_626_) == 0)
{
lean_object* v_pos_627_; 
lean_dec(v_pos_614_);
v_pos_627_ = lean_ctor_get(v_s_625_, 2);
lean_inc(v_pos_627_);
lean_dec_ref(v_s_625_);
return v_pos_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v_errorMsg_626_);
lean_dec_ref(v_s_625_);
v___x_628_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
v___x_629_ = lean_nat_add(v_pos_614_, v___x_628_);
lean_dec(v_pos_614_);
return v___x_629_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_635_ = l_Lean_Parser_categoryParser(v___x_634_, v___x_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_638_; lean_object* v_fn_639_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v_fn_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_fn_639_);
v___x_640_ = lean_apply_2(v_fn_639_, v_a_636_, v_a_637_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_641_, lean_object* v_as_642_, size_t v_sz_643_, size_t v_i_644_, lean_object* v_b_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_lt(v_i_644_, v_sz_643_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_inputCtx_641_);
return v_b_645_;
}
else
{
lean_object* v_a_647_; lean_object* v_snd_648_; lean_object* v_fst_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; 
v_a_647_ = lean_array_uget_borrowed(v_as_642_, v_i_644_);
v_snd_648_ = lean_ctor_get(v_a_647_, 1);
v_fst_649_ = lean_ctor_get(v_a_647_, 0);
v_fst_650_ = lean_ctor_get(v_snd_648_, 0);
v_snd_651_ = lean_ctor_get(v_snd_648_, 1);
lean_inc(v_snd_651_);
lean_inc(v_fst_650_);
lean_inc(v_fst_649_);
lean_inc_ref(v_inputCtx_641_);
v___x_652_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_641_, v_fst_649_, v_fst_650_, v_snd_651_);
v___x_653_ = l_Lean_MessageLog_add(v___x_652_, v_b_645_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_644_, v___x_654_);
v_i_644_ = v___x_655_;
v_b_645_ = v___x_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_657_, lean_object* v_as_658_, lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_b_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_663_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_657_, v_as_658_, v_sz_boxed_662_, v_i_boxed_663_, v_b_661_);
lean_dec_ref(v_as_658_);
return v_res_664_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_p_667_; 
v___x_665_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_666_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v_p_667_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_667_, 0, v___x_666_);
lean_closure_set(v_p_667_, 1, v___x_665_);
return v_p_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_668_, lean_object* v_pmctx_669_, lean_object* v_b_670_){
_start:
{
lean_object* v_snd_671_; lean_object* v_snd_672_; lean_object* v_fst_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_775_; 
v_snd_671_ = lean_ctor_get(v_b_670_, 1);
lean_inc(v_snd_671_);
v_snd_672_ = lean_ctor_get(v_snd_671_, 1);
lean_inc(v_snd_672_);
v_fst_673_ = lean_ctor_get(v_b_670_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_b_670_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_b_670_, 1);
lean_dec(v_unused_776_);
v___x_675_ = v_b_670_;
v_isShared_676_ = v_isSharedCheck_775_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_fst_673_);
lean_dec(v_b_670_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_775_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_fst_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_773_; 
v_fst_677_ = lean_ctor_get(v_snd_671_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_snd_671_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_snd_671_, 1);
lean_dec(v_unused_774_);
v___x_679_ = v_snd_671_;
v_isShared_680_ = v_isSharedCheck_773_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_fst_677_);
lean_dec(v_snd_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_773_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_772_; 
v_fst_681_ = lean_ctor_get(v_snd_672_, 0);
v_snd_682_ = lean_ctor_get(v_snd_672_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_snd_672_);
if (v_isSharedCheck_772_ == 0)
{
v___x_684_ = v_snd_672_;
v_isShared_685_ = v_isSharedCheck_772_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v_snd_672_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_772_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_668_, v_fst_673_);
if (v___x_686_ == 0)
{
lean_object* v_env_687_; lean_object* v_inputString_688_; lean_object* v_p_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_s_697_; lean_object* v_stxStack_698_; lean_object* v_pos_699_; lean_object* v_errorMsg_700_; lean_object* v_recoveredErrors_701_; uint8_t v_recovering_702_; lean_object* v___y_704_; lean_object* v_messages_705_; size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_737_; lean_object* v_pos_738_; uint8_t v___y_743_; uint8_t v___x_759_; 
v_env_687_ = lean_ctor_get(v_pmctx_669_, 0);
v_inputString_688_ = lean_ctor_get(v_inputCtx_668_, 0);
v_p_689_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0);
lean_inc_ref(v_env_687_);
v___x_690_ = l_Lean_Parser_getTokenTable(v_env_687_);
v___x_691_ = l_Lean_Parser_SyntaxStack_empty;
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_Parser_initCacheForInput(v_inputString_688_);
v___x_694_ = lean_box(0);
v___x_695_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_673_);
v___x_696_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
lean_ctor_set(v___x_696_, 1, v___x_692_);
lean_ctor_set(v___x_696_, 2, v_fst_673_);
lean_ctor_set(v___x_696_, 3, v___x_693_);
lean_ctor_set(v___x_696_, 4, v___x_694_);
lean_ctor_set(v___x_696_, 5, v___x_695_);
lean_inc_ref(v_pmctx_669_);
lean_inc_ref_n(v_inputCtx_668_, 2);
v_s_697_ = l_Lean_Parser_ParserFn_run(v_p_689_, v_inputCtx_668_, v_pmctx_669_, v___x_690_, v___x_696_);
v_stxStack_698_ = lean_ctor_get(v_s_697_, 0);
lean_inc_ref(v_stxStack_698_);
v_pos_699_ = lean_ctor_get(v_s_697_, 2);
lean_inc(v_pos_699_);
v_errorMsg_700_ = lean_ctor_get(v_s_697_, 4);
lean_inc(v_errorMsg_700_);
v_recoveredErrors_701_ = lean_ctor_get(v_s_697_, 5);
lean_inc_ref(v_recoveredErrors_701_);
lean_dec_ref(v_s_697_);
v_recovering_702_ = 1;
v_sz_717_ = lean_array_size(v_recoveredErrors_701_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_668_, v_recoveredErrors_701_, v_sz_717_, v___x_718_, v_fst_681_);
lean_dec_ref(v_recoveredErrors_701_);
v___x_759_ = lean_unbox(v_fst_677_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; 
v___x_760_ = lean_unbox(v_fst_677_);
v___y_743_ = v___x_760_;
goto v___jp_742_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_698_);
if (v___x_761_ == 0)
{
goto v___jp_752_;
}
else
{
if (v___x_686_ == 0)
{
v___y_743_ = v___x_686_;
goto v___jp_742_;
}
else
{
goto v___jp_752_;
}
}
}
v___jp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v_messages_705_);
v___x_707_ = v___x_684_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_messages_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_682_);
v___x_707_ = v_reuseFailAlloc_716_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_box(v_recovering_702_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_707_);
lean_ctor_set(v___x_679_, 0, v___x_708_);
v___x_710_ = v___x_679_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_707_);
v___x_710_ = v_reuseFailAlloc_715_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_710_);
lean_ctor_set(v___x_675_, 0, v___y_704_);
v___x_712_ = v___x_675_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___y_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_714_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_b_670_ = v___x_712_;
goto _start;
}
}
}
}
v___jp_720_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_inc_ref(v_stxStack_698_);
lean_inc_ref(v_inputCtx_668_);
v___x_724_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_668_, v_pos_699_, v_stxStack_698_, v___y_722_);
v___x_725_ = l_Lean_MessageLog_add(v___x_724_, v___x_719_);
if (v___y_721_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_684_);
lean_dec(v_snd_682_);
lean_del_object(v___x_679_);
lean_del_object(v___x_675_);
lean_dec_ref(v_pmctx_669_);
lean_dec_ref(v_inputCtx_668_);
v___x_726_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_698_);
lean_dec_ref(v_stxStack_698_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_box(v_recovering_702_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_723_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
return v___x_730_;
}
else
{
lean_dec_ref(v_stxStack_698_);
v___y_704_ = v___y_723_;
v_messages_705_ = v___x_725_;
goto v___jp_703_;
}
}
v___jp_731_:
{
uint8_t v___x_735_; 
v___x_735_ = lean_unbox(v_fst_677_);
lean_dec(v_fst_677_);
if (v___x_735_ == 0)
{
v___y_721_ = v___y_734_;
v___y_722_ = v___y_732_;
v___y_723_ = v___y_733_;
goto v___jp_720_;
}
else
{
if (v___y_734_ == 0)
{
v___y_721_ = v___y_734_;
v___y_722_ = v___y_732_;
v___y_723_ = v___y_733_;
goto v___jp_720_;
}
else
{
lean_dec_ref(v___y_732_);
lean_dec(v_pos_699_);
lean_dec_ref(v_stxStack_698_);
v___y_704_ = v___y_733_;
v_messages_705_ = v___x_719_;
goto v___jp_703_;
}
}
}
v___jp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_698_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_698_);
v___x_741_ = l_Lean_Syntax_getPos_x3f(v___x_740_, v___x_739_);
lean_dec(v___x_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
v___y_732_ = v___y_737_;
v___y_733_ = v_pos_738_;
v___y_734_ = v_recovering_702_;
goto v___jp_731_;
}
else
{
lean_dec_ref(v___x_741_);
v___y_732_ = v___y_737_;
v___y_733_ = v_pos_738_;
v___y_734_ = v___x_739_;
goto v___jp_731_;
}
}
else
{
v___y_732_ = v___y_737_;
v___y_733_ = v_pos_738_;
v___y_734_ = v_recovering_702_;
goto v___jp_731_;
}
}
v___jp_742_:
{
if (lean_obj_tag(v_errorMsg_700_) == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_del_object(v___x_684_);
lean_dec(v_snd_682_);
lean_del_object(v___x_679_);
lean_dec(v_fst_677_);
lean_del_object(v___x_675_);
lean_dec(v_fst_673_);
lean_dec_ref(v_pmctx_669_);
lean_dec_ref(v_inputCtx_668_);
v___x_744_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_698_);
lean_dec_ref(v_stxStack_698_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_719_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_box(v___y_743_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_pos_699_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_val_749_; uint8_t v___x_750_; 
v_val_749_ = lean_ctor_get(v_errorMsg_700_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v_errorMsg_700_);
v___x_750_ = lean_nat_dec_eq(v_pos_699_, v_fst_673_);
lean_dec(v_fst_673_);
if (v___x_750_ == 0)
{
lean_inc(v_pos_699_);
v___y_737_ = v_val_749_;
v_pos_738_ = v_pos_699_;
goto v___jp_736_;
}
else
{
lean_object* v___x_751_; 
lean_inc(v_pos_699_);
lean_inc_ref(v_pmctx_669_);
lean_inc_ref(v_inputCtx_668_);
v___x_751_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_668_, v_pmctx_669_, v_pos_699_);
v___y_737_ = v_val_749_;
v_pos_738_ = v___x_751_;
goto v___jp_736_;
}
}
}
v___jp_752_:
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_698_);
v___x_754_ = l_Lean_Syntax_isAntiquot(v___x_753_);
lean_dec(v___x_753_);
if (v___x_754_ == 0)
{
v___y_743_ = v___x_754_;
goto v___jp_742_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_errorMsg_700_);
lean_dec_ref(v_stxStack_698_);
lean_del_object(v___x_684_);
lean_del_object(v___x_679_);
lean_del_object(v___x_675_);
lean_dec(v_fst_673_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_719_);
lean_ctor_set(v___x_755_, 1, v_snd_682_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_677_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_pos_699_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v_b_670_ = v___x_757_;
goto _start;
}
}
}
else
{
lean_object* v_stx_762_; lean_object* v___x_764_; 
lean_dec(v_snd_682_);
lean_dec_ref(v_pmctx_669_);
lean_inc(v_fst_673_);
v_stx_762_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_668_, v_fst_673_);
lean_dec_ref(v_inputCtx_668_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_stx_762_);
v___x_764_ = v___x_684_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_stx_762_);
v___x_764_ = v_reuseFailAlloc_771_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_764_);
v___x_766_ = v___x_679_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fst_677_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_766_);
v___x_768_ = v___x_675_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_fst_673_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_777_, lean_object* v_pmctx_778_, lean_object* v_mps_779_, lean_object* v_messages_780_){
_start:
{
lean_object* v_pos_781_; uint8_t v_recovering_782_; uint8_t v_hasLeading_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_823_; 
v_pos_781_ = lean_ctor_get(v_mps_779_, 0);
v_recovering_782_ = lean_ctor_get_uint8(v_mps_779_, sizeof(void*)*1);
v_hasLeading_783_ = lean_ctor_get_uint8(v_mps_779_, sizeof(void*)*1 + 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_mps_779_);
if (v_isSharedCheck_823_ == 0)
{
v___x_785_ = v_mps_779_;
v_isShared_786_ = v_isSharedCheck_823_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_pos_781_);
lean_dec(v_mps_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_823_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_stx_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_snd_793_; lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v_fst_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_821_; 
v_stx_787_ = lean_box(0);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_messages_780_);
lean_ctor_set(v___x_788_, 1, v_stx_787_);
v___x_789_ = lean_box(v_recovering_782_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_pos_781_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(v_inputCtx_777_, v_pmctx_778_, v___x_791_);
v_snd_793_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_snd_793_);
v_snd_794_ = lean_ctor_get(v_snd_793_, 1);
lean_inc(v_snd_794_);
v_fst_795_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_fst_795_);
lean_dec_ref(v___x_792_);
v_fst_796_ = lean_ctor_get(v_snd_793_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_snd_793_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_snd_793_, 1);
lean_dec(v_unused_822_);
v___x_798_ = v_snd_793_;
v_isShared_799_ = v_isSharedCheck_821_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_fst_796_);
lean_dec(v_snd_793_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_821_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_820_; 
v_fst_800_ = lean_ctor_get(v_snd_794_, 0);
v_snd_801_ = lean_ctor_get(v_snd_794_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_820_ == 0)
{
v___x_803_ = v_snd_794_;
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_inc(v_fst_800_);
lean_dec(v_snd_794_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_820_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_stx_806_; 
if (v_hasLeading_783_ == 0)
{
v_stx_806_ = v_snd_801_;
goto v___jp_805_;
}
else
{
lean_object* v___x_818_; lean_object* v_fst_819_; 
v___x_818_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_801_);
v_fst_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_fst_819_);
lean_dec_ref(v___x_818_);
v_stx_806_ = v_fst_819_;
goto v___jp_805_;
}
v___jp_805_:
{
uint8_t v___x_807_; lean_object* v___x_809_; 
v___x_807_ = 0;
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_fst_795_);
v___x_809_ = v___x_785_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fst_795_);
v___x_809_ = v_reuseFailAlloc_817_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
uint8_t v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_unbox(v_fst_796_);
lean_dec(v_fst_796_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_810_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1 + 1, v___x_807_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_fst_800_);
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_812_ = v___x_803_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_fst_800_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_812_);
lean_ctor_set(v___x_798_, 0, v_stx_806_);
v___x_814_ = v___x_798_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_stx_806_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_putStr_827_; lean_object* v___x_828_; 
v___x_826_ = lean_get_stdout();
v_putStr_827_ = lean_ctor_get(v___x_826_, 4);
lean_inc_ref(v_putStr_827_);
lean_dec_ref(v___x_826_);
v___x_828_ = lean_apply_2(v_putStr_827_, v_s_824_, lean_box(0));
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_832_){
_start:
{
uint32_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = 10;
v___x_835_ = lean_string_push(v_s_832_, v___x_834_);
v___x_836_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_840_, lean_object* v_msg_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = l_Lean_Message_toString(v_msg_841_, v___y_840_);
v___x_844_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_845_, lean_object* v_msg_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___y_1564__boxed_848_; lean_object* v_res_849_; 
v___y_1564__boxed_848_ = lean_unbox(v___y_845_);
v_res_849_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_1564__boxed_848_, v_msg_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_850_, lean_object* v_as_851_, size_t v_i_852_, size_t v_stop_853_, lean_object* v_b_854_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_eq(v_i_852_, v_stop_853_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_array_uget_borrowed(v_as_851_, v_i_852_);
lean_inc_ref(v_f_850_);
lean_inc(v___x_857_);
v___x_858_ = lean_apply_2(v_f_850_, v___x_857_, lean_box(0));
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; size_t v___x_860_; size_t v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_852_, v___x_860_);
v_i_852_ = v___x_861_;
v_b_854_ = v_a_859_;
goto _start;
}
else
{
lean_dec_ref(v_f_850_);
return v___x_858_;
}
}
else
{
lean_object* v___x_863_; 
lean_dec_ref(v_f_850_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_b_854_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_864_, lean_object* v_as_865_, lean_object* v_i_866_, lean_object* v_stop_867_, lean_object* v_b_868_, lean_object* v___y_869_){
_start:
{
size_t v_i_boxed_870_; size_t v_stop_boxed_871_; lean_object* v_res_872_; 
v_i_boxed_870_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_stop_boxed_871_ = lean_unbox_usize(v_stop_867_);
lean_dec(v_stop_867_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_864_, v_as_865_, v_i_boxed_870_, v_stop_boxed_871_, v_b_868_);
lean_dec_ref(v_as_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v_cs_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_897_; 
v_cs_876_ = lean_ctor_get(v_x_874_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_897_ == 0)
{
v___x_878_ = v_x_874_;
v_isShared_879_ = v_isSharedCheck_897_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_cs_876_);
lean_dec(v_x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_897_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_array_get_size(v_cs_876_);
v___x_882_ = lean_box(0);
v___x_883_ = lean_nat_dec_lt(v___x_880_, v___x_881_);
if (v___x_883_ == 0)
{
lean_object* v___x_885_; 
lean_dec_ref(v_cs_876_);
lean_dec_ref(v_f_873_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_882_);
v___x_885_ = v___x_878_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_882_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
uint8_t v___x_887_; 
v___x_887_ = lean_nat_dec_le(v___x_881_, v___x_881_);
if (v___x_887_ == 0)
{
if (v___x_883_ == 0)
{
lean_object* v___x_889_; 
lean_dec_ref(v_cs_876_);
lean_dec_ref(v_f_873_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_882_);
v___x_889_ = v___x_878_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_882_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
lean_del_object(v___x_878_);
v___x_891_ = ((size_t)0ULL);
v___x_892_ = lean_usize_of_nat(v___x_881_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_873_, v_cs_876_, v___x_891_, v___x_892_, v___x_882_);
lean_dec_ref(v_cs_876_);
return v___x_893_;
}
}
else
{
size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
lean_del_object(v___x_878_);
v___x_894_ = ((size_t)0ULL);
v___x_895_ = lean_usize_of_nat(v___x_881_);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_873_, v_cs_876_, v___x_894_, v___x_895_, v___x_882_);
lean_dec_ref(v_cs_876_);
return v___x_896_;
}
}
}
}
else
{
lean_object* v_vs_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_919_; 
v_vs_898_ = lean_ctor_get(v_x_874_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_919_ == 0)
{
v___x_900_ = v_x_874_;
v_isShared_901_ = v_isSharedCheck_919_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_vs_898_);
lean_dec(v_x_874_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_919_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_array_get_size(v_vs_898_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_905_ == 0)
{
lean_object* v___x_907_; 
lean_dec_ref(v_vs_898_);
lean_dec_ref(v_f_873_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
lean_ctor_set(v___x_900_, 0, v___x_904_);
v___x_907_ = v___x_900_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
uint8_t v___x_909_; 
v___x_909_ = lean_nat_dec_le(v___x_903_, v___x_903_);
if (v___x_909_ == 0)
{
if (v___x_905_ == 0)
{
lean_object* v___x_911_; 
lean_dec_ref(v_vs_898_);
lean_dec_ref(v_f_873_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
lean_ctor_set(v___x_900_, 0, v___x_904_);
v___x_911_ = v___x_900_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_904_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
lean_del_object(v___x_900_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = lean_usize_of_nat(v___x_903_);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_873_, v_vs_898_, v___x_913_, v___x_914_, v___x_904_);
lean_dec_ref(v_vs_898_);
return v___x_915_;
}
}
else
{
size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
lean_del_object(v___x_900_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_903_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_873_, v_vs_898_, v___x_916_, v___x_917_, v___x_904_);
lean_dec_ref(v_vs_898_);
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_920_, lean_object* v_as_921_, size_t v_i_922_, size_t v_stop_923_, lean_object* v_b_924_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = lean_usize_dec_eq(v_i_922_, v_stop_923_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_array_uget_borrowed(v_as_921_, v_i_922_);
lean_inc(v___x_927_);
lean_inc_ref(v_f_920_);
v___x_928_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_920_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; size_t v___x_930_; size_t v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_922_, v___x_930_);
v_i_922_ = v___x_931_;
v_b_924_ = v_a_929_;
goto _start;
}
else
{
lean_dec_ref(v_f_920_);
return v___x_928_;
}
}
else
{
lean_object* v___x_933_; 
lean_dec_ref(v_f_920_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_b_924_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_934_, lean_object* v_as_935_, lean_object* v_i_936_, lean_object* v_stop_937_, lean_object* v_b_938_, lean_object* v___y_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_937_);
lean_dec(v_stop_937_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_934_, v_as_935_, v_i_boxed_940_, v_stop_boxed_941_, v_b_938_);
lean_dec_ref(v_as_935_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_943_, lean_object* v_x_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_943_, v_x_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_947_, lean_object* v_t_948_){
_start:
{
lean_object* v_root_950_; lean_object* v_tail_951_; lean_object* v___x_952_; 
v_root_950_ = lean_ctor_get(v_t_948_, 0);
lean_inc_ref(v_root_950_);
v_tail_951_ = lean_ctor_get(v_t_948_, 1);
lean_inc_ref(v_tail_951_);
lean_dec_ref(v_t_948_);
lean_inc_ref(v_f_947_);
v___x_952_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_947_, v_root_950_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_973_; 
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_974_);
v___x_954_ = v___x_952_;
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_952_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_973_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_tail_951_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_tail_951_);
lean_dec_ref(v_f_947_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_958_);
v___x_961_ = v___x_954_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_958_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_963_ == 0)
{
if (v___x_959_ == 0)
{
lean_object* v___x_965_; 
lean_dec_ref(v_tail_951_);
lean_dec_ref(v_f_947_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_958_);
v___x_965_ = v___x_954_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_958_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; 
lean_del_object(v___x_954_);
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_957_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_947_, v_tail_951_, v___x_967_, v___x_968_, v___x_958_);
lean_dec_ref(v_tail_951_);
return v___x_969_;
}
}
else
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
lean_del_object(v___x_954_);
v___x_970_ = ((size_t)0ULL);
v___x_971_ = lean_usize_of_nat(v___x_957_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_947_, v_tail_951_, v___x_970_, v___x_971_, v___x_958_);
lean_dec_ref(v_tail_951_);
return v___x_972_;
}
}
}
}
else
{
lean_dec_ref(v_tail_951_);
lean_dec_ref(v_f_947_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_975_, lean_object* v_t_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_975_, v_t_976_);
return v_res_978_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_980_, lean_object* v_x_981_, size_t v_x_982_, size_t v_x_983_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_object* v_cs_985_; lean_object* v___x_986_; size_t v___x_987_; lean_object* v_j_988_; lean_object* v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v_cs_985_ = lean_ctor_get(v_x_981_, 0);
lean_inc_ref(v_cs_985_);
lean_dec_ref(v_x_981_);
v___x_986_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_987_ = lean_usize_shift_right(v_x_982_, v_x_983_);
v_j_988_ = lean_usize_to_nat(v___x_987_);
v___x_989_ = lean_array_get_borrowed(v___x_986_, v_cs_985_, v_j_988_);
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_shift_left(v___x_990_, v_x_983_);
v___x_992_ = lean_usize_sub(v___x_991_, v___x_990_);
v___x_993_ = lean_usize_land(v_x_982_, v___x_992_);
v___x_994_ = ((size_t)5ULL);
v___x_995_ = lean_usize_sub(v_x_983_, v___x_994_);
lean_inc(v___x_989_);
lean_inc_ref(v_f_980_);
v___x_996_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_980_, v___x_989_, v___x_993_, v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1018_; 
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1019_);
v___x_998_ = v___x_996_;
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
else
{
lean_dec(v___x_996_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_add(v_j_988_, v___x_1000_);
lean_dec(v_j_988_);
v___x_1002_ = lean_array_get_size(v_cs_985_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_nat_dec_lt(v___x_1001_, v___x_1002_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1006_; 
lean_dec(v___x_1001_);
lean_dec_ref(v_cs_985_);
lean_dec_ref(v_f_980_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1003_);
v___x_1006_ = v___x_998_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_le(v___x_1002_, v___x_1002_);
if (v___x_1008_ == 0)
{
if (v___x_1004_ == 0)
{
lean_object* v___x_1010_; 
lean_dec(v___x_1001_);
lean_dec_ref(v_cs_985_);
lean_dec_ref(v_f_980_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1003_);
v___x_1010_ = v___x_998_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1003_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
lean_del_object(v___x_998_);
v___x_1012_ = lean_usize_of_nat(v___x_1001_);
lean_dec(v___x_1001_);
v___x_1013_ = lean_usize_of_nat(v___x_1002_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_980_, v_cs_985_, v___x_1012_, v___x_1013_, v___x_1003_);
lean_dec_ref(v_cs_985_);
return v___x_1014_;
}
}
else
{
size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
lean_del_object(v___x_998_);
v___x_1015_ = lean_usize_of_nat(v___x_1001_);
lean_dec(v___x_1001_);
v___x_1016_ = lean_usize_of_nat(v___x_1002_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_980_, v_cs_985_, v___x_1015_, v___x_1016_, v___x_1003_);
lean_dec_ref(v_cs_985_);
return v___x_1017_;
}
}
}
}
else
{
lean_dec(v_j_988_);
lean_dec_ref(v_cs_985_);
lean_dec_ref(v_f_980_);
return v___x_996_;
}
}
else
{
lean_object* v_vs_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1041_; 
v_vs_1020_ = lean_ctor_get(v_x_981_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1022_ = v_x_981_;
v_isShared_1023_ = v_isSharedCheck_1041_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_vs_1020_);
lean_dec(v_x_981_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1041_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_usize_to_nat(v_x_982_);
v___x_1025_ = lean_array_get_size(v_vs_1020_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1029_; 
lean_dec(v___x_1024_);
lean_dec_ref(v_vs_1020_);
lean_dec_ref(v_f_980_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1029_ = v___x_1022_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_nat_dec_le(v___x_1025_, v___x_1025_);
if (v___x_1031_ == 0)
{
if (v___x_1027_ == 0)
{
lean_object* v___x_1033_; 
lean_dec(v___x_1024_);
lean_dec_ref(v_vs_1020_);
lean_dec_ref(v_f_980_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1033_ = v___x_1022_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1026_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
lean_del_object(v___x_1022_);
v___x_1035_ = lean_usize_of_nat(v___x_1024_);
lean_dec(v___x_1024_);
v___x_1036_ = lean_usize_of_nat(v___x_1025_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_980_, v_vs_1020_, v___x_1035_, v___x_1036_, v___x_1026_);
lean_dec_ref(v_vs_1020_);
return v___x_1037_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
lean_del_object(v___x_1022_);
v___x_1038_ = lean_usize_of_nat(v___x_1024_);
lean_dec(v___x_1024_);
v___x_1039_ = lean_usize_of_nat(v___x_1025_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_980_, v_vs_1020_, v___x_1038_, v___x_1039_, v___x_1026_);
lean_dec_ref(v_vs_1020_);
return v___x_1040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_x_1762__boxed_1047_; size_t v_x_1763__boxed_1048_; lean_object* v_res_1049_; 
v_x_1762__boxed_1047_ = lean_unbox_usize(v_x_1044_);
lean_dec(v_x_1044_);
v_x_1763__boxed_1048_ = lean_unbox_usize(v_x_1045_);
lean_dec(v_x_1045_);
v_res_1049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1042_, v_x_1043_, v_x_1762__boxed_1047_, v_x_1763__boxed_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1050_, lean_object* v_t_1051_, lean_object* v_start_1052_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_nat_dec_eq(v_start_1052_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v_root_1056_; lean_object* v_tail_1057_; size_t v_shift_1058_; lean_object* v_tailOff_1059_; uint8_t v___x_1060_; 
v_root_1056_ = lean_ctor_get(v_t_1051_, 0);
lean_inc_ref(v_root_1056_);
v_tail_1057_ = lean_ctor_get(v_t_1051_, 1);
lean_inc_ref(v_tail_1057_);
v_shift_1058_ = lean_ctor_get_usize(v_t_1051_, 4);
v_tailOff_1059_ = lean_ctor_get(v_t_1051_, 3);
lean_inc(v_tailOff_1059_);
lean_dec_ref(v_t_1051_);
v___x_1060_ = lean_nat_dec_le(v_tailOff_1059_, v_start_1052_);
if (v___x_1060_ == 0)
{
size_t v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_tailOff_1059_);
v___x_1061_ = lean_usize_of_nat(v_start_1052_);
lean_inc_ref(v_f_1050_);
v___x_1062_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1050_, v_root_1056_, v___x_1061_, v_shift_1058_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1062_, 0);
lean_dec(v_unused_1083_);
v___x_1064_ = v___x_1062_;
v_isShared_1065_ = v_isSharedCheck_1082_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v___x_1062_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1082_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_array_get_size(v_tail_1057_);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_nat_dec_lt(v___x_1054_, v___x_1066_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1070_; 
lean_dec_ref(v_tail_1057_);
lean_dec_ref(v_f_1050_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1070_ = v___x_1064_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1067_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_nat_dec_le(v___x_1066_, v___x_1066_);
if (v___x_1072_ == 0)
{
if (v___x_1068_ == 0)
{
lean_object* v___x_1074_; 
lean_dec_ref(v_tail_1057_);
lean_dec_ref(v_f_1050_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1074_ = v___x_1064_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1067_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
size_t v___x_1076_; size_t v___x_1077_; lean_object* v___x_1078_; 
lean_del_object(v___x_1064_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = lean_usize_of_nat(v___x_1066_);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1050_, v_tail_1057_, v___x_1076_, v___x_1077_, v___x_1067_);
lean_dec_ref(v_tail_1057_);
return v___x_1078_;
}
}
else
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
lean_del_object(v___x_1064_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = lean_usize_of_nat(v___x_1066_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1050_, v_tail_1057_, v___x_1079_, v___x_1080_, v___x_1067_);
lean_dec_ref(v_tail_1057_);
return v___x_1081_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1057_);
lean_dec_ref(v_f_1050_);
return v___x_1062_;
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
lean_dec_ref(v_root_1056_);
v___x_1084_ = lean_nat_sub(v_start_1052_, v_tailOff_1059_);
lean_dec(v_tailOff_1059_);
v___x_1085_ = lean_array_get_size(v_tail_1057_);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_nat_dec_lt(v___x_1084_, v___x_1085_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v___x_1084_);
lean_dec_ref(v_tail_1057_);
lean_dec_ref(v_f_1050_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
return v___x_1088_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_nat_dec_le(v___x_1085_, v___x_1085_);
if (v___x_1089_ == 0)
{
if (v___x_1087_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v___x_1084_);
lean_dec_ref(v_tail_1057_);
lean_dec_ref(v_f_1050_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1086_);
return v___x_1090_;
}
else
{
size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_usize_of_nat(v___x_1084_);
lean_dec(v___x_1084_);
v___x_1092_ = lean_usize_of_nat(v___x_1085_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1050_, v_tail_1057_, v___x_1091_, v___x_1092_, v___x_1086_);
lean_dec_ref(v_tail_1057_);
return v___x_1093_;
}
}
else
{
size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_usize_of_nat(v___x_1084_);
lean_dec(v___x_1084_);
v___x_1095_ = lean_usize_of_nat(v___x_1085_);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1050_, v_tail_1057_, v___x_1094_, v___x_1095_, v___x_1086_);
lean_dec_ref(v_tail_1057_);
return v___x_1096_;
}
}
}
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1050_, v_t_1051_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1098_, lean_object* v_t_1099_, lean_object* v_start_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1098_, v_t_1099_, v_start_1100_);
lean_dec(v_start_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1103_, lean_object* v_f_1104_){
_start:
{
lean_object* v_unreported_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_unreported_1106_ = lean_ctor_get(v_log_1103_, 1);
lean_inc_ref(v_unreported_1106_);
lean_dec_ref(v_log_1103_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1104_, v_unreported_1106_, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1109_, lean_object* v_f_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1109_, v_f_1110_);
return v_res_1112_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1115_ = lean_mk_io_user_error(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1116_, lean_object* v_inputCtx_1117_, lean_object* v_state_1118_, lean_object* v_msgs_1119_, lean_object* v_stxs_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_snd_1127_; lean_object* v_fst_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; uint8_t v___y_1132_; uint8_t v___x_1153_; 
v___x_1122_ = l_Lean_Options_empty;
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_box(0);
lean_inc_ref(v_env_1116_);
v___x_1125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1125_, 0, v_env_1116_);
lean_ctor_set(v___x_1125_, 1, v___x_1122_);
lean_ctor_set(v___x_1125_, 2, v___x_1123_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
lean_inc_ref(v_inputCtx_1117_);
v___x_1126_ = l_Lean_Parser_parseCommand(v_inputCtx_1117_, v___x_1125_, v_state_1118_, v_msgs_1119_);
v_snd_1127_ = lean_ctor_get(v___x_1126_, 1);
lean_inc(v_snd_1127_);
v_fst_1128_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_n(v_fst_1128_, 2);
lean_dec_ref(v___x_1126_);
v_fst_1129_ = lean_ctor_get(v_snd_1127_, 0);
lean_inc(v_fst_1129_);
v_snd_1130_ = lean_ctor_get(v_snd_1127_, 1);
lean_inc(v_snd_1130_);
lean_dec(v_snd_1127_);
v___x_1153_ = l_Lean_Parser_isTerminalCommand(v_fst_1128_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_array_push(v_stxs_1120_, v_fst_1128_);
v_state_1118_ = v_fst_1129_;
v_msgs_1119_ = v_snd_1130_;
v_stxs_1120_ = v___x_1154_;
goto _start;
}
else
{
uint8_t v___x_1156_; 
lean_dec(v_fst_1129_);
lean_dec_ref(v_inputCtx_1117_);
lean_dec_ref(v_env_1116_);
v___x_1156_ = l_Lean_MessageLog_hasUnreported(v_snd_1130_);
if (v___x_1156_ == 0)
{
if (v___x_1153_ == 0)
{
lean_dec(v_fst_1128_);
lean_dec_ref(v_stxs_1120_);
v___y_1132_ = v___x_1153_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_snd_1130_);
v___x_1157_ = lean_array_push(v_stxs_1120_, v_fst_1128_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
else
{
uint8_t v___x_1159_; 
lean_dec(v_fst_1128_);
lean_dec_ref(v_stxs_1120_);
v___x_1159_ = 0;
v___y_1132_ = v___x_1159_;
goto v___jp_1131_;
}
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_box(v___y_1132_);
v___f_1134_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1134_, 0, v___x_1133_);
v___x_1135_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1130_, v___f_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1144_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1135_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1135_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1160_, lean_object* v_inputCtx_1161_, lean_object* v_state_1162_, lean_object* v_msgs_1163_, lean_object* v_stxs_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1160_, v_inputCtx_1161_, v_state_1162_, v_msgs_1163_, v_stxs_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1167_, lean_object* v_inputCtx_1168_, lean_object* v_s_1169_, lean_object* v_msgs_1170_, lean_object* v_stxs_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1167_, v_inputCtx_1168_, v_s_1169_, v_msgs_1170_, v_stxs_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1174_, lean_object* v_inputCtx_1175_, lean_object* v_s_1176_, lean_object* v_msgs_1177_, lean_object* v_stxs_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Parser_testParseModuleAux(v_env_1174_, v_inputCtx_1175_, v_s_1176_, v_msgs_1177_, v_stxs_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1189_, lean_object* v_fname_1190_, lean_object* v_contents_1191_){
_start:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v_inputCtx_1195_; lean_object* v___x_1196_; 
v___x_1193_ = 1;
v___x_1194_ = lean_string_utf8_byte_size(v_contents_1191_);
v_inputCtx_1195_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1191_, v_fname_1190_, v___x_1193_, v___x_1194_);
lean_inc_ref(v_inputCtx_1195_);
v___x_1196_ = l_Lean_Parser_parseHeader(v_inputCtx_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v_snd_1198_; lean_object* v_fst_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
v_snd_1198_ = lean_ctor_get(v_a_1197_, 1);
lean_inc(v_snd_1198_);
v_fst_1199_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_fst_1199_);
lean_dec(v_a_1197_);
v_fst_1200_ = lean_ctor_get(v_snd_1198_, 0);
lean_inc(v_fst_1200_);
v_snd_1201_ = lean_ctor_get(v_snd_1198_, 1);
lean_inc(v_snd_1201_);
lean_dec(v_snd_1198_);
v___x_1202_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1203_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1189_, v_inputCtx_1195_, v_fst_1200_, v_snd_1201_, v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1219_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1219_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1219_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1208_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1209_ = l_Lean_mkListNode(v_a_1204_);
v___x_1210_ = lean_unsigned_to_nat(2u);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1210_);
v___x_1212_ = lean_array_push(v___x_1211_, v_fst_1199_);
v___x_1213_ = lean_array_push(v___x_1212_, v___x_1209_);
v___x_1214_ = lean_box(2);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1208_);
lean_ctor_set(v___x_1215_, 2, v___x_1213_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1215_);
v___x_1217_ = v___x_1206_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_fst_1199_);
v_a_1220_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1203_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1203_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_inputCtx_1195_);
lean_dec_ref(v_env_1189_);
v_a_1228_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1196_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1196_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1236_, lean_object* v_fname_1237_, lean_object* v_contents_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Parser_testParseModule(v_env_1236_, v_fname_1237_, v_contents_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1241_, lean_object* v_fname_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_IO_FS_readFile(v_fname_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_Parser_testParseModule(v_env_1241_, v_fname_1242_, v_a_1245_);
return v___x_1246_;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_fname_1242_);
lean_dec_ref(v_env_1241_);
v_a_1247_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1244_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1255_, lean_object* v_fname_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Parser_testParseFile(v_env_1255_, v_fname_1256_);
return v_res_1258_;
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
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
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
res = initialize_Lean_Parser_Extra(builtin);
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
