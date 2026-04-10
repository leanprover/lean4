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
lean_object* l_Lean_Parser_withPosition(lean_object*);
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
static lean_once_cell_t l_Lean_Parser_topLevelCommandParserFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_topLevelCommandParserFn___closed__3;
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
v___x_73_ = l_Lean_Parser_Error_toString(v___y_67_);
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___x_75_ = l_Lean_MessageData_ofFormat(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_76_, 0, v___y_65_);
lean_ctor_set(v___x_76_, 1, v___y_66_);
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
v___y_65_ = v_fileName_81_;
v___y_66_ = v___x_83_;
v___y_67_ = v_e_80_;
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
v___y_65_ = v_fileName_81_;
v___y_66_ = v___x_83_;
v___y_67_ = v_e_80_;
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
if (lean_obj_tag(v___y_313_) == 1)
{
if (lean_obj_tag(v___y_312_) == 0)
{
lean_dec_ref(v___y_313_);
lean_dec(v___y_310_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___y_312_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___y_312_, 0);
lean_dec(v_unused_333_);
v___x_315_ = v___y_312_;
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___y_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_332_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
if (v___y_311_ == 0)
{
lean_del_object(v___x_315_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_310_);
v_a_285_ = v_b_282_;
goto v___jp_284_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v_val_317_ = lean_ctor_get(v___y_313_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___y_313_);
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
v___y_312_ = v___y_337_;
v___y_313_ = v_allTk_x3f_338_;
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
v___y_312_ = v___y_337_;
v___y_313_ = v_allTk_x3f_338_;
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
lean_object* v___x_427_; lean_object* v_fn_428_; lean_object* v_inputString_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_stxStack_440_; lean_object* v_pos_441_; lean_object* v_errorMsg_442_; lean_object* v___y_444_; uint8_t v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; lean_object* v___y_462_; lean_object* v_messages_463_; lean_object* v___y_474_; lean_object* v___y_475_; size_t v___y_476_; lean_object* v___y_477_; lean_object* v___x_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; size_t v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_moduleTk_x3f_500_; lean_object* v___y_510_; uint8_t v___x_540_; 
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
v___x_479_ = l_Lean_Syntax_getArg(v___y_477_, v___x_478_);
v___x_480_ = l_Lean_Syntax_getArgs(v___x_479_);
lean_dec(v___x_479_);
v_sz_481_ = lean_array_size(v___x_480_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_419_, v___y_475_, v___x_480_, v_sz_481_, v___y_476_, v___y_474_);
lean_dec_ref(v___x_480_);
lean_dec(v___y_475_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
v___y_462_ = v___y_477_;
v_messages_463_ = v_a_483_;
goto v___jp_461_;
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___y_477_);
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
v___x_502_ = l_Lean_Syntax_getArg(v___y_499_, v___x_501_);
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
v___y_462_ = v___y_499_;
v_messages_463_ = v___y_494_;
goto v___jp_461_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_505_ = l_Lean_Syntax_getArg(v___x_502_, v___x_492_);
lean_dec(v___x_502_);
v___x_506_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_498_);
lean_inc_ref(v___y_495_);
lean_inc_ref(v___y_496_);
v___x_507_ = l_Lean_Name_mkStr4(v___y_496_, v___y_495_, v___y_498_, v___x_506_);
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_505_, v___x_507_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_moduleTk_x3f_500_);
lean_dec_ref(v_inputCtx_419_);
v___y_462_ = v___y_499_;
v_messages_463_ = v___y_494_;
goto v___jp_461_;
}
else
{
v___y_474_ = v___y_494_;
v___y_475_ = v_moduleTk_x3f_500_;
v___y_476_ = v___y_497_;
v___y_477_ = v___y_499_;
goto v___jp_473_;
}
}
}
else
{
lean_dec(v___x_502_);
v___y_474_ = v___y_494_;
v___y_475_ = v_moduleTk_x3f_500_;
v___y_476_ = v___y_497_;
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
v___y_494_ = v_a_516_;
v___y_495_ = v___x_518_;
v___y_496_ = v___x_517_;
v___y_497_ = v___x_514_;
v___y_498_ = v___x_519_;
v___y_499_ = v___y_510_;
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
v___y_494_ = v_a_516_;
v___y_495_ = v___x_518_;
v___y_496_ = v___x_517_;
v___y_497_ = v___x_514_;
v___y_498_ = v___x_519_;
v___y_499_ = v___y_510_;
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
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_637_ = l_Lean_Parser_withPosition(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; lean_object* v_fn_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_641_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_fn_641_);
v___x_642_ = lean_apply_2(v_fn_641_, v_a_638_, v_a_639_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_643_, lean_object* v_as_644_, size_t v_sz_645_, size_t v_i_646_, lean_object* v_b_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_usize_dec_lt(v_i_646_, v_sz_645_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_inputCtx_643_);
return v_b_647_;
}
else
{
lean_object* v_a_649_; lean_object* v_snd_650_; lean_object* v_fst_651_; lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; 
v_a_649_ = lean_array_uget_borrowed(v_as_644_, v_i_646_);
v_snd_650_ = lean_ctor_get(v_a_649_, 1);
v_fst_651_ = lean_ctor_get(v_a_649_, 0);
v_fst_652_ = lean_ctor_get(v_snd_650_, 0);
v_snd_653_ = lean_ctor_get(v_snd_650_, 1);
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_inc(v_fst_651_);
lean_inc_ref(v_inputCtx_643_);
v___x_654_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_643_, v_fst_651_, v_fst_652_, v_snd_653_);
v___x_655_ = l_Lean_MessageLog_add(v___x_654_, v_b_647_);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_646_, v___x_656_);
v_i_646_ = v___x_657_;
v_b_647_ = v___x_655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_659_, lean_object* v_as_660_, lean_object* v_sz_661_, lean_object* v_i_662_, lean_object* v_b_663_){
_start:
{
size_t v_sz_boxed_664_; size_t v_i_boxed_665_; lean_object* v_res_666_; 
v_sz_boxed_664_ = lean_unbox_usize(v_sz_661_);
lean_dec(v_sz_661_);
v_i_boxed_665_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_res_666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_659_, v_as_660_, v_sz_boxed_664_, v_i_boxed_665_, v_b_663_);
lean_dec_ref(v_as_660_);
return v_res_666_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_p_669_; 
v___x_667_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_668_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v_p_669_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_669_, 0, v___x_668_);
lean_closure_set(v_p_669_, 1, v___x_667_);
return v_p_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_670_, lean_object* v_pmctx_671_, lean_object* v_b_672_){
_start:
{
lean_object* v_snd_673_; lean_object* v_snd_674_; lean_object* v_fst_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_777_; 
v_snd_673_ = lean_ctor_get(v_b_672_, 1);
lean_inc(v_snd_673_);
v_snd_674_ = lean_ctor_get(v_snd_673_, 1);
lean_inc(v_snd_674_);
v_fst_675_ = lean_ctor_get(v_b_672_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_b_672_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v_b_672_, 1);
lean_dec(v_unused_778_);
v___x_677_ = v_b_672_;
v_isShared_678_ = v_isSharedCheck_777_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_fst_675_);
lean_dec(v_b_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_777_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_fst_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_775_; 
v_fst_679_ = lean_ctor_get(v_snd_673_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_snd_673_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_snd_673_, 1);
lean_dec(v_unused_776_);
v___x_681_ = v_snd_673_;
v_isShared_682_ = v_isSharedCheck_775_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_fst_679_);
lean_dec(v_snd_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_775_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_774_; 
v_fst_683_ = lean_ctor_get(v_snd_674_, 0);
v_snd_684_ = lean_ctor_get(v_snd_674_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_snd_674_);
if (v_isSharedCheck_774_ == 0)
{
v___x_686_ = v_snd_674_;
v_isShared_687_ = v_isSharedCheck_774_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v_snd_674_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_774_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_670_, v_fst_675_);
if (v___x_688_ == 0)
{
lean_object* v_env_689_; lean_object* v_inputString_690_; lean_object* v_p_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_s_699_; lean_object* v_stxStack_700_; lean_object* v_pos_701_; lean_object* v_errorMsg_702_; lean_object* v_recoveredErrors_703_; uint8_t v_recovering_704_; lean_object* v___y_706_; lean_object* v_messages_707_; size_t v_sz_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_734_; lean_object* v___y_735_; uint8_t v___y_736_; lean_object* v___y_739_; lean_object* v_pos_740_; uint8_t v___y_745_; uint8_t v___x_761_; 
v_env_689_ = lean_ctor_get(v_pmctx_671_, 0);
v_inputString_690_ = lean_ctor_get(v_inputCtx_670_, 0);
v_p_691_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1___closed__0);
lean_inc_ref(v_env_689_);
v___x_692_ = l_Lean_Parser_getTokenTable(v_env_689_);
v___x_693_ = l_Lean_Parser_SyntaxStack_empty;
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Lean_Parser_initCacheForInput(v_inputString_690_);
v___x_696_ = lean_box(0);
v___x_697_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_675_);
v___x_698_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_698_, 0, v___x_693_);
lean_ctor_set(v___x_698_, 1, v___x_694_);
lean_ctor_set(v___x_698_, 2, v_fst_675_);
lean_ctor_set(v___x_698_, 3, v___x_695_);
lean_ctor_set(v___x_698_, 4, v___x_696_);
lean_ctor_set(v___x_698_, 5, v___x_697_);
lean_inc_ref(v_pmctx_671_);
lean_inc_ref_n(v_inputCtx_670_, 2);
v_s_699_ = l_Lean_Parser_ParserFn_run(v_p_691_, v_inputCtx_670_, v_pmctx_671_, v___x_692_, v___x_698_);
v_stxStack_700_ = lean_ctor_get(v_s_699_, 0);
lean_inc_ref(v_stxStack_700_);
v_pos_701_ = lean_ctor_get(v_s_699_, 2);
lean_inc(v_pos_701_);
v_errorMsg_702_ = lean_ctor_get(v_s_699_, 4);
lean_inc(v_errorMsg_702_);
v_recoveredErrors_703_ = lean_ctor_get(v_s_699_, 5);
lean_inc_ref(v_recoveredErrors_703_);
lean_dec_ref(v_s_699_);
v_recovering_704_ = 1;
v_sz_719_ = lean_array_size(v_recoveredErrors_703_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_670_, v_recoveredErrors_703_, v_sz_719_, v___x_720_, v_fst_683_);
lean_dec_ref(v_recoveredErrors_703_);
v___x_761_ = lean_unbox(v_fst_679_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; 
v___x_762_ = lean_unbox(v_fst_679_);
v___y_745_ = v___x_762_;
goto v___jp_744_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_700_);
if (v___x_763_ == 0)
{
goto v___jp_754_;
}
else
{
if (v___x_688_ == 0)
{
v___y_745_ = v___x_688_;
goto v___jp_744_;
}
else
{
goto v___jp_754_;
}
}
}
v___jp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_messages_707_);
v___x_709_ = v___x_686_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_messages_707_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_684_);
v___x_709_ = v_reuseFailAlloc_718_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_box(v_recovering_704_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_709_);
lean_ctor_set(v___x_681_, 0, v___x_710_);
v___x_712_ = v___x_681_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_709_);
v___x_712_ = v_reuseFailAlloc_717_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_712_);
lean_ctor_set(v___x_677_, 0, v___y_706_);
v___x_714_ = v___x_677_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___y_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_716_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_b_672_ = v___x_714_;
goto _start;
}
}
}
}
v___jp_722_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc_ref(v_stxStack_700_);
lean_inc_ref(v_inputCtx_670_);
v___x_726_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_670_, v_pos_701_, v_stxStack_700_, v___y_723_);
v___x_727_ = l_Lean_MessageLog_add(v___x_726_, v___x_721_);
if (v___y_725_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_del_object(v___x_686_);
lean_dec(v_snd_684_);
lean_del_object(v___x_681_);
lean_del_object(v___x_677_);
lean_dec_ref(v_pmctx_671_);
lean_dec_ref(v_inputCtx_670_);
v___x_728_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_700_);
lean_dec_ref(v_stxStack_700_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_box(v_recovering_704_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_729_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___y_724_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
return v___x_732_;
}
else
{
lean_dec_ref(v_stxStack_700_);
v___y_706_ = v___y_724_;
v_messages_707_ = v___x_727_;
goto v___jp_705_;
}
}
v___jp_733_:
{
uint8_t v___x_737_; 
v___x_737_ = lean_unbox(v_fst_679_);
lean_dec(v_fst_679_);
if (v___x_737_ == 0)
{
v___y_723_ = v___y_734_;
v___y_724_ = v___y_735_;
v___y_725_ = v___y_736_;
goto v___jp_722_;
}
else
{
if (v___y_736_ == 0)
{
v___y_723_ = v___y_734_;
v___y_724_ = v___y_735_;
v___y_725_ = v___y_736_;
goto v___jp_722_;
}
else
{
lean_dec_ref(v___y_734_);
lean_dec(v_pos_701_);
lean_dec_ref(v_stxStack_700_);
v___y_706_ = v___y_735_;
v_messages_707_ = v___x_721_;
goto v___jp_705_;
}
}
}
v___jp_738_:
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_700_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_700_);
v___x_743_ = l_Lean_Syntax_getPos_x3f(v___x_742_, v___x_741_);
lean_dec(v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
v___y_734_ = v___y_739_;
v___y_735_ = v_pos_740_;
v___y_736_ = v_recovering_704_;
goto v___jp_733_;
}
else
{
lean_dec_ref(v___x_743_);
v___y_734_ = v___y_739_;
v___y_735_ = v_pos_740_;
v___y_736_ = v___x_741_;
goto v___jp_733_;
}
}
else
{
v___y_734_ = v___y_739_;
v___y_735_ = v_pos_740_;
v___y_736_ = v_recovering_704_;
goto v___jp_733_;
}
}
v___jp_744_:
{
if (lean_obj_tag(v_errorMsg_702_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_del_object(v___x_686_);
lean_dec(v_snd_684_);
lean_del_object(v___x_681_);
lean_dec(v_fst_679_);
lean_del_object(v___x_677_);
lean_dec(v_fst_675_);
lean_dec_ref(v_pmctx_671_);
lean_dec_ref(v_inputCtx_670_);
v___x_746_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_700_);
lean_dec_ref(v_stxStack_700_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_721_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_box(v___y_745_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_pos_701_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
return v___x_750_;
}
else
{
lean_object* v_val_751_; uint8_t v___x_752_; 
v_val_751_ = lean_ctor_get(v_errorMsg_702_, 0);
lean_inc(v_val_751_);
lean_dec_ref(v_errorMsg_702_);
v___x_752_ = lean_nat_dec_eq(v_pos_701_, v_fst_675_);
lean_dec(v_fst_675_);
if (v___x_752_ == 0)
{
lean_inc(v_pos_701_);
v___y_739_ = v_val_751_;
v_pos_740_ = v_pos_701_;
goto v___jp_738_;
}
else
{
lean_object* v___x_753_; 
lean_inc(v_pos_701_);
lean_inc_ref(v_pmctx_671_);
lean_inc_ref(v_inputCtx_670_);
v___x_753_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_670_, v_pmctx_671_, v_pos_701_);
v___y_739_ = v_val_751_;
v_pos_740_ = v___x_753_;
goto v___jp_738_;
}
}
}
v___jp_754_:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_700_);
v___x_756_ = l_Lean_Syntax_isAntiquot(v___x_755_);
lean_dec(v___x_755_);
if (v___x_756_ == 0)
{
v___y_745_ = v___x_756_;
goto v___jp_744_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_errorMsg_702_);
lean_dec_ref(v_stxStack_700_);
lean_del_object(v___x_686_);
lean_del_object(v___x_681_);
lean_del_object(v___x_677_);
lean_dec(v_fst_675_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_721_);
lean_ctor_set(v___x_757_, 1, v_snd_684_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_fst_679_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_pos_701_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v_b_672_ = v___x_759_;
goto _start;
}
}
}
else
{
lean_object* v_stx_764_; lean_object* v___x_766_; 
lean_dec(v_snd_684_);
lean_dec_ref(v_pmctx_671_);
lean_inc(v_fst_675_);
v_stx_764_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_670_, v_fst_675_);
lean_dec_ref(v_inputCtx_670_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_stx_764_);
v___x_766_ = v___x_686_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_fst_683_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_stx_764_);
v___x_766_ = v_reuseFailAlloc_773_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_766_);
v___x_768_ = v___x_681_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_768_);
v___x_770_ = v___x_677_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_675_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_779_, lean_object* v_pmctx_780_, lean_object* v_mps_781_, lean_object* v_messages_782_){
_start:
{
lean_object* v_pos_783_; uint8_t v_recovering_784_; uint8_t v_hasLeading_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_825_; 
v_pos_783_ = lean_ctor_get(v_mps_781_, 0);
v_recovering_784_ = lean_ctor_get_uint8(v_mps_781_, sizeof(void*)*1);
v_hasLeading_785_ = lean_ctor_get_uint8(v_mps_781_, sizeof(void*)*1 + 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_mps_781_);
if (v_isSharedCheck_825_ == 0)
{
v___x_787_ = v_mps_781_;
v_isShared_788_ = v_isSharedCheck_825_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_pos_783_);
lean_dec(v_mps_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_825_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_stx_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_snd_795_; lean_object* v_snd_796_; lean_object* v_fst_797_; lean_object* v_fst_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_823_; 
v_stx_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_messages_782_);
lean_ctor_set(v___x_790_, 1, v_stx_789_);
v___x_791_ = lean_box(v_recovering_784_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_pos_783_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Parser_parseCommand_spec__1(v_inputCtx_779_, v_pmctx_780_, v___x_793_);
v_snd_795_ = lean_ctor_get(v___x_794_, 1);
lean_inc(v_snd_795_);
v_snd_796_ = lean_ctor_get(v_snd_795_, 1);
lean_inc(v_snd_796_);
v_fst_797_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_fst_797_);
lean_dec_ref(v___x_794_);
v_fst_798_ = lean_ctor_get(v_snd_795_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_snd_795_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_snd_795_, 1);
lean_dec(v_unused_824_);
v___x_800_ = v_snd_795_;
v_isShared_801_ = v_isSharedCheck_823_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_fst_798_);
lean_dec(v_snd_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_823_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_822_; 
v_fst_802_ = lean_ctor_get(v_snd_796_, 0);
v_snd_803_ = lean_ctor_get(v_snd_796_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_796_);
if (v_isSharedCheck_822_ == 0)
{
v___x_805_ = v_snd_796_;
v_isShared_806_ = v_isSharedCheck_822_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
lean_dec(v_snd_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_822_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_stx_808_; 
if (v_hasLeading_785_ == 0)
{
v_stx_808_ = v_snd_803_;
goto v___jp_807_;
}
else
{
lean_object* v___x_820_; lean_object* v_fst_821_; 
v___x_820_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_803_);
v_fst_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_fst_821_);
lean_dec_ref(v___x_820_);
v_stx_808_ = v_fst_821_;
goto v___jp_807_;
}
v___jp_807_:
{
uint8_t v___x_809_; lean_object* v___x_811_; 
v___x_809_ = 0;
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_fst_797_);
v___x_811_ = v___x_787_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_797_);
v___x_811_ = v_reuseFailAlloc_819_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
uint8_t v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_unbox(v_fst_798_);
lean_dec(v_fst_798_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v___x_812_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1 + 1, v___x_809_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_fst_802_);
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_814_ = v___x_805_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_fst_802_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_814_);
lean_ctor_set(v___x_800_, 0, v_stx_808_);
v___x_816_ = v___x_800_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_stx_808_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_putStr_829_; lean_object* v___x_830_; 
v___x_828_ = lean_get_stdout();
v_putStr_829_ = lean_ctor_get(v___x_828_, 4);
lean_inc_ref(v_putStr_829_);
lean_dec_ref(v___x_828_);
v___x_830_ = lean_apply_2(v_putStr_829_, v_s_826_, lean_box(0));
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_834_){
_start:
{
uint32_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 10;
v___x_837_ = lean_string_push(v_s_834_, v___x_836_);
v___x_838_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_842_, lean_object* v_msg_843_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = l_Lean_Message_toString(v_msg_843_, v___y_842_);
v___x_846_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_847_, lean_object* v_msg_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___y_1564__boxed_850_; lean_object* v_res_851_; 
v___y_1564__boxed_850_ = lean_unbox(v___y_847_);
v_res_851_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_1564__boxed_850_, v_msg_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_852_, lean_object* v_as_853_, size_t v_i_854_, size_t v_stop_855_, lean_object* v_b_856_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_eq(v_i_854_, v_stop_855_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_array_uget_borrowed(v_as_853_, v_i_854_);
lean_inc_ref(v_f_852_);
lean_inc(v___x_859_);
v___x_860_ = lean_apply_2(v_f_852_, v___x_859_, lean_box(0));
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; size_t v___x_862_; size_t v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_854_, v___x_862_);
v_i_854_ = v___x_863_;
v_b_856_ = v_a_861_;
goto _start;
}
else
{
lean_dec_ref(v_f_852_);
return v___x_860_;
}
}
else
{
lean_object* v___x_865_; 
lean_dec_ref(v_f_852_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_b_856_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_866_, lean_object* v_as_867_, lean_object* v_i_868_, lean_object* v_stop_869_, lean_object* v_b_870_, lean_object* v___y_871_){
_start:
{
size_t v_i_boxed_872_; size_t v_stop_boxed_873_; lean_object* v_res_874_; 
v_i_boxed_872_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_stop_boxed_873_ = lean_unbox_usize(v_stop_869_);
lean_dec(v_stop_869_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_866_, v_as_867_, v_i_boxed_872_, v_stop_boxed_873_, v_b_870_);
lean_dec_ref(v_as_867_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v_cs_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_899_; 
v_cs_878_ = lean_ctor_get(v_x_876_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_899_ == 0)
{
v___x_880_ = v_x_876_;
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_cs_878_);
lean_dec(v_x_876_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_array_get_size(v_cs_878_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_887_; 
lean_dec_ref(v_cs_878_);
lean_dec_ref(v_f_875_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_887_ = v___x_880_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_884_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
uint8_t v___x_889_; 
v___x_889_ = lean_nat_dec_le(v___x_883_, v___x_883_);
if (v___x_889_ == 0)
{
if (v___x_885_ == 0)
{
lean_object* v___x_891_; 
lean_dec_ref(v_cs_878_);
lean_dec_ref(v_f_875_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_891_ = v___x_880_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_884_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_880_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_883_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_875_, v_cs_878_, v___x_893_, v___x_894_, v___x_884_);
lean_dec_ref(v_cs_878_);
return v___x_895_;
}
}
else
{
size_t v___x_896_; size_t v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_880_);
v___x_896_ = ((size_t)0ULL);
v___x_897_ = lean_usize_of_nat(v___x_883_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_875_, v_cs_878_, v___x_896_, v___x_897_, v___x_884_);
lean_dec_ref(v_cs_878_);
return v___x_898_;
}
}
}
}
else
{
lean_object* v_vs_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_921_; 
v_vs_900_ = lean_ctor_get(v_x_876_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_921_ == 0)
{
v___x_902_ = v_x_876_;
v_isShared_903_ = v_isSharedCheck_921_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_vs_900_);
lean_dec(v_x_876_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_921_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_array_get_size(v_vs_900_);
v___x_906_ = lean_box(0);
v___x_907_ = lean_nat_dec_lt(v___x_904_, v___x_905_);
if (v___x_907_ == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_vs_900_);
lean_dec_ref(v_f_875_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 0);
lean_ctor_set(v___x_902_, 0, v___x_906_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_906_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_le(v___x_905_, v___x_905_);
if (v___x_911_ == 0)
{
if (v___x_907_ == 0)
{
lean_object* v___x_913_; 
lean_dec_ref(v_vs_900_);
lean_dec_ref(v_f_875_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 0);
lean_ctor_set(v___x_902_, 0, v___x_906_);
v___x_913_ = v___x_902_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_906_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_902_);
v___x_915_ = ((size_t)0ULL);
v___x_916_ = lean_usize_of_nat(v___x_905_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_875_, v_vs_900_, v___x_915_, v___x_916_, v___x_906_);
lean_dec_ref(v_vs_900_);
return v___x_917_;
}
}
else
{
size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
lean_del_object(v___x_902_);
v___x_918_ = ((size_t)0ULL);
v___x_919_ = lean_usize_of_nat(v___x_905_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_875_, v_vs_900_, v___x_918_, v___x_919_, v___x_906_);
lean_dec_ref(v_vs_900_);
return v___x_920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_922_, lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_, lean_object* v_b_926_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_eq(v_i_924_, v_stop_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_array_uget_borrowed(v_as_923_, v_i_924_);
lean_inc(v___x_929_);
lean_inc_ref(v_f_922_);
v___x_930_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_922_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; size_t v___x_932_; size_t v___x_933_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref(v___x_930_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_924_, v___x_932_);
v_i_924_ = v___x_933_;
v_b_926_ = v_a_931_;
goto _start;
}
else
{
lean_dec_ref(v_f_922_);
return v___x_930_;
}
}
else
{
lean_object* v___x_935_; 
lean_dec_ref(v_f_922_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_b_926_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_936_, lean_object* v_as_937_, lean_object* v_i_938_, lean_object* v_stop_939_, lean_object* v_b_940_, lean_object* v___y_941_){
_start:
{
size_t v_i_boxed_942_; size_t v_stop_boxed_943_; lean_object* v_res_944_; 
v_i_boxed_942_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_stop_boxed_943_ = lean_unbox_usize(v_stop_939_);
lean_dec(v_stop_939_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_936_, v_as_937_, v_i_boxed_942_, v_stop_boxed_943_, v_b_940_);
lean_dec_ref(v_as_937_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_945_, lean_object* v_x_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_945_, v_x_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_949_, lean_object* v_t_950_){
_start:
{
lean_object* v_root_952_; lean_object* v_tail_953_; lean_object* v___x_954_; 
v_root_952_ = lean_ctor_get(v_t_950_, 0);
lean_inc_ref(v_root_952_);
v_tail_953_ = lean_ctor_get(v_t_950_, 1);
lean_inc_ref(v_tail_953_);
lean_dec_ref(v_t_950_);
lean_inc_ref(v_f_949_);
v___x_954_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_949_, v_root_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_976_);
v___x_956_ = v___x_954_;
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
else
{
lean_dec(v___x_954_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_975_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_array_get_size(v_tail_953_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_nat_dec_lt(v___x_958_, v___x_959_);
if (v___x_961_ == 0)
{
lean_object* v___x_963_; 
lean_dec_ref(v_tail_953_);
lean_dec_ref(v_f_949_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_960_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_le(v___x_959_, v___x_959_);
if (v___x_965_ == 0)
{
if (v___x_961_ == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v_tail_953_);
lean_dec_ref(v_f_949_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_967_ = v___x_956_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_960_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
lean_del_object(v___x_956_);
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_959_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_949_, v_tail_953_, v___x_969_, v___x_970_, v___x_960_);
lean_dec_ref(v_tail_953_);
return v___x_971_;
}
}
else
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
lean_del_object(v___x_956_);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = lean_usize_of_nat(v___x_959_);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_949_, v_tail_953_, v___x_972_, v___x_973_, v___x_960_);
lean_dec_ref(v_tail_953_);
return v___x_974_;
}
}
}
}
else
{
lean_dec_ref(v_tail_953_);
lean_dec_ref(v_f_949_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_977_, lean_object* v_t_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_977_, v_t_978_);
return v_res_980_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_982_, lean_object* v_x_983_, size_t v_x_984_, size_t v_x_985_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_object* v_cs_987_; lean_object* v___x_988_; size_t v___x_989_; lean_object* v_j_990_; lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v_cs_987_ = lean_ctor_get(v_x_983_, 0);
lean_inc_ref(v_cs_987_);
lean_dec_ref(v_x_983_);
v___x_988_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_989_ = lean_usize_shift_right(v_x_984_, v_x_985_);
v_j_990_ = lean_usize_to_nat(v___x_989_);
v___x_991_ = lean_array_get_borrowed(v___x_988_, v_cs_987_, v_j_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_shift_left(v___x_992_, v_x_985_);
v___x_994_ = lean_usize_sub(v___x_993_, v___x_992_);
v___x_995_ = lean_usize_land(v_x_984_, v___x_994_);
v___x_996_ = ((size_t)5ULL);
v___x_997_ = lean_usize_sub(v_x_985_, v___x_996_);
lean_inc(v___x_991_);
lean_inc_ref(v_f_982_);
v___x_998_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_982_, v___x_991_, v___x_995_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_998_, 0);
lean_dec(v_unused_1021_);
v___x_1000_ = v___x_998_;
v_isShared_1001_ = v_isSharedCheck_1020_;
goto v_resetjp_999_;
}
else
{
lean_dec(v___x_998_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1020_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_j_990_, v___x_1002_);
lean_dec(v_j_990_);
v___x_1004_ = lean_array_get_size(v_cs_987_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_nat_dec_lt(v___x_1003_, v___x_1004_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v___x_1003_);
lean_dec_ref(v_cs_987_);
lean_dec_ref(v_f_982_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1005_);
v___x_1008_ = v___x_1000_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1005_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_nat_dec_le(v___x_1004_, v___x_1004_);
if (v___x_1010_ == 0)
{
if (v___x_1006_ == 0)
{
lean_object* v___x_1012_; 
lean_dec(v___x_1003_);
lean_dec_ref(v_cs_987_);
lean_dec_ref(v_f_982_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1005_);
v___x_1012_ = v___x_1000_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1005_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
lean_del_object(v___x_1000_);
v___x_1014_ = lean_usize_of_nat(v___x_1003_);
lean_dec(v___x_1003_);
v___x_1015_ = lean_usize_of_nat(v___x_1004_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_982_, v_cs_987_, v___x_1014_, v___x_1015_, v___x_1005_);
lean_dec_ref(v_cs_987_);
return v___x_1016_;
}
}
else
{
size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
lean_del_object(v___x_1000_);
v___x_1017_ = lean_usize_of_nat(v___x_1003_);
lean_dec(v___x_1003_);
v___x_1018_ = lean_usize_of_nat(v___x_1004_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_982_, v_cs_987_, v___x_1017_, v___x_1018_, v___x_1005_);
lean_dec_ref(v_cs_987_);
return v___x_1019_;
}
}
}
}
else
{
lean_dec(v_j_990_);
lean_dec_ref(v_cs_987_);
lean_dec_ref(v_f_982_);
return v___x_998_;
}
}
else
{
lean_object* v_vs_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1043_; 
v_vs_1022_ = lean_ctor_get(v_x_983_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_x_983_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1024_ = v_x_983_;
v_isShared_1025_ = v_isSharedCheck_1043_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_vs_1022_);
lean_dec(v_x_983_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1043_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1026_ = lean_usize_to_nat(v_x_984_);
v___x_1027_ = lean_array_get_size(v_vs_1022_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_nat_dec_lt(v___x_1026_, v___x_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v___x_1026_);
lean_dec_ref(v_vs_1022_);
lean_dec_ref(v_f_982_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1031_ = v___x_1024_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_nat_dec_le(v___x_1027_, v___x_1027_);
if (v___x_1033_ == 0)
{
if (v___x_1029_ == 0)
{
lean_object* v___x_1035_; 
lean_dec(v___x_1026_);
lean_dec_ref(v_vs_1022_);
lean_dec_ref(v_f_982_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1035_ = v___x_1024_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1028_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
lean_del_object(v___x_1024_);
v___x_1037_ = lean_usize_of_nat(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1038_ = lean_usize_of_nat(v___x_1027_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_982_, v_vs_1022_, v___x_1037_, v___x_1038_, v___x_1028_);
lean_dec_ref(v_vs_1022_);
return v___x_1039_;
}
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
lean_del_object(v___x_1024_);
v___x_1040_ = lean_usize_of_nat(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1041_ = lean_usize_of_nat(v___x_1027_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_982_, v_vs_1022_, v___x_1040_, v___x_1041_, v___x_1028_);
lean_dec_ref(v_vs_1022_);
return v___x_1042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_x_1762__boxed_1049_; size_t v_x_1763__boxed_1050_; lean_object* v_res_1051_; 
v_x_1762__boxed_1049_ = lean_unbox_usize(v_x_1046_);
lean_dec(v_x_1046_);
v_x_1763__boxed_1050_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_res_1051_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1044_, v_x_1045_, v_x_1762__boxed_1049_, v_x_1763__boxed_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1052_, lean_object* v_t_1053_, lean_object* v_start_1054_){
_start:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_nat_dec_eq(v_start_1054_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v_root_1058_; lean_object* v_tail_1059_; size_t v_shift_1060_; lean_object* v_tailOff_1061_; uint8_t v___x_1062_; 
v_root_1058_ = lean_ctor_get(v_t_1053_, 0);
lean_inc_ref(v_root_1058_);
v_tail_1059_ = lean_ctor_get(v_t_1053_, 1);
lean_inc_ref(v_tail_1059_);
v_shift_1060_ = lean_ctor_get_usize(v_t_1053_, 4);
v_tailOff_1061_ = lean_ctor_get(v_t_1053_, 3);
lean_inc(v_tailOff_1061_);
lean_dec_ref(v_t_1053_);
v___x_1062_ = lean_nat_dec_le(v_tailOff_1061_, v_start_1054_);
if (v___x_1062_ == 0)
{
size_t v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_tailOff_1061_);
v___x_1063_ = lean_usize_of_nat(v_start_1054_);
lean_inc_ref(v_f_1052_);
v___x_1064_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1052_, v_root_1058_, v___x_1063_, v_shift_1060_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1064_, 0);
lean_dec(v_unused_1085_);
v___x_1066_ = v___x_1064_;
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1064_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_array_get_size(v_tail_1059_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_nat_dec_lt(v___x_1056_, v___x_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v_tail_1059_);
lean_dec_ref(v_f_1052_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1069_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1069_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_nat_dec_le(v___x_1068_, v___x_1068_);
if (v___x_1074_ == 0)
{
if (v___x_1070_ == 0)
{
lean_object* v___x_1076_; 
lean_dec_ref(v_tail_1059_);
lean_dec_ref(v_f_1052_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1069_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1069_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
lean_del_object(v___x_1066_);
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1068_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1052_, v_tail_1059_, v___x_1078_, v___x_1079_, v___x_1069_);
lean_dec_ref(v_tail_1059_);
return v___x_1080_;
}
}
else
{
size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
lean_del_object(v___x_1066_);
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1068_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1052_, v_tail_1059_, v___x_1081_, v___x_1082_, v___x_1069_);
lean_dec_ref(v_tail_1059_);
return v___x_1083_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1059_);
lean_dec_ref(v_f_1052_);
return v___x_1064_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
lean_dec_ref(v_root_1058_);
v___x_1086_ = lean_nat_sub(v_start_1054_, v_tailOff_1061_);
lean_dec(v_tailOff_1061_);
v___x_1087_ = lean_array_get_size(v_tail_1059_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_nat_dec_lt(v___x_1086_, v___x_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v___x_1086_);
lean_dec_ref(v_tail_1059_);
lean_dec_ref(v_f_1052_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
return v___x_1090_;
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_nat_dec_le(v___x_1087_, v___x_1087_);
if (v___x_1091_ == 0)
{
if (v___x_1089_ == 0)
{
lean_object* v___x_1092_; 
lean_dec(v___x_1086_);
lean_dec_ref(v_tail_1059_);
lean_dec_ref(v_f_1052_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1088_);
return v___x_1092_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_usize_of_nat(v___x_1086_);
lean_dec(v___x_1086_);
v___x_1094_ = lean_usize_of_nat(v___x_1087_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1052_, v_tail_1059_, v___x_1093_, v___x_1094_, v___x_1088_);
lean_dec_ref(v_tail_1059_);
return v___x_1095_;
}
}
else
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_usize_of_nat(v___x_1086_);
lean_dec(v___x_1086_);
v___x_1097_ = lean_usize_of_nat(v___x_1087_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1052_, v_tail_1059_, v___x_1096_, v___x_1097_, v___x_1088_);
lean_dec_ref(v_tail_1059_);
return v___x_1098_;
}
}
}
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1052_, v_t_1053_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1100_, lean_object* v_t_1101_, lean_object* v_start_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1100_, v_t_1101_, v_start_1102_);
lean_dec(v_start_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1105_, lean_object* v_f_1106_){
_start:
{
lean_object* v_unreported_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_unreported_1108_ = lean_ctor_get(v_log_1105_, 1);
lean_inc_ref(v_unreported_1108_);
lean_dec_ref(v_log_1105_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1106_, v_unreported_1108_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1111_, lean_object* v_f_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1111_, v_f_1112_);
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1117_ = lean_mk_io_user_error(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1118_, lean_object* v_inputCtx_1119_, lean_object* v_state_1120_, lean_object* v_msgs_1121_, lean_object* v_stxs_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_snd_1129_; lean_object* v_fst_1130_; lean_object* v_fst_1131_; lean_object* v_snd_1132_; uint8_t v___y_1134_; uint8_t v___x_1155_; 
v___x_1124_ = l_Lean_Options_empty;
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_box(0);
lean_inc_ref(v_env_1118_);
v___x_1127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1127_, 0, v_env_1118_);
lean_ctor_set(v___x_1127_, 1, v___x_1124_);
lean_ctor_set(v___x_1127_, 2, v___x_1125_);
lean_ctor_set(v___x_1127_, 3, v___x_1126_);
lean_inc_ref(v_inputCtx_1119_);
v___x_1128_ = l_Lean_Parser_parseCommand(v_inputCtx_1119_, v___x_1127_, v_state_1120_, v_msgs_1121_);
v_snd_1129_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_snd_1129_);
v_fst_1130_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_n(v_fst_1130_, 2);
lean_dec_ref(v___x_1128_);
v_fst_1131_ = lean_ctor_get(v_snd_1129_, 0);
lean_inc(v_fst_1131_);
v_snd_1132_ = lean_ctor_get(v_snd_1129_, 1);
lean_inc(v_snd_1132_);
lean_dec(v_snd_1129_);
v___x_1155_ = l_Lean_Parser_isTerminalCommand(v_fst_1130_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_array_push(v_stxs_1122_, v_fst_1130_);
v_state_1120_ = v_fst_1131_;
v_msgs_1121_ = v_snd_1132_;
v_stxs_1122_ = v___x_1156_;
goto _start;
}
else
{
uint8_t v___x_1158_; 
lean_dec(v_fst_1131_);
lean_dec_ref(v_inputCtx_1119_);
lean_dec_ref(v_env_1118_);
v___x_1158_ = l_Lean_MessageLog_hasUnreported(v_snd_1132_);
if (v___x_1158_ == 0)
{
if (v___x_1155_ == 0)
{
lean_dec(v_fst_1130_);
lean_dec_ref(v_stxs_1122_);
v___y_1134_ = v___x_1155_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_snd_1132_);
v___x_1159_ = lean_array_push(v_stxs_1122_, v_fst_1130_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
else
{
uint8_t v___x_1161_; 
lean_dec(v_fst_1130_);
lean_dec_ref(v_stxs_1122_);
v___x_1161_ = 0;
v___y_1134_ = v___x_1161_;
goto v___jp_1133_;
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_box(v___y_1134_);
v___f_1136_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1136_, 0, v___x_1135_);
v___x_1137_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1132_, v___f_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1145_; 
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1137_, 0);
lean_dec(v_unused_1146_);
v___x_1139_ = v___x_1137_;
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
else
{
lean_dec(v___x_1137_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1137_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1137_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1162_, lean_object* v_inputCtx_1163_, lean_object* v_state_1164_, lean_object* v_msgs_1165_, lean_object* v_stxs_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1162_, v_inputCtx_1163_, v_state_1164_, v_msgs_1165_, v_stxs_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1169_, lean_object* v_inputCtx_1170_, lean_object* v_s_1171_, lean_object* v_msgs_1172_, lean_object* v_stxs_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1169_, v_inputCtx_1170_, v_s_1171_, v_msgs_1172_, v_stxs_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1176_, lean_object* v_inputCtx_1177_, lean_object* v_s_1178_, lean_object* v_msgs_1179_, lean_object* v_stxs_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Parser_testParseModuleAux(v_env_1176_, v_inputCtx_1177_, v_s_1178_, v_msgs_1179_, v_stxs_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1191_, lean_object* v_fname_1192_, lean_object* v_contents_1193_){
_start:
{
uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v_inputCtx_1197_; lean_object* v___x_1198_; 
v___x_1195_ = 1;
v___x_1196_ = lean_string_utf8_byte_size(v_contents_1193_);
v_inputCtx_1197_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1193_, v_fname_1192_, v___x_1195_, v___x_1196_);
lean_inc_ref(v_inputCtx_1197_);
v___x_1198_ = l_Lean_Parser_parseHeader(v_inputCtx_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_snd_1200_; lean_object* v_fst_1201_; lean_object* v_fst_1202_; lean_object* v_snd_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
v_snd_1200_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_snd_1200_);
v_fst_1201_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_fst_1201_);
lean_dec(v_a_1199_);
v_fst_1202_ = lean_ctor_get(v_snd_1200_, 0);
lean_inc(v_fst_1202_);
v_snd_1203_ = lean_ctor_get(v_snd_1200_, 1);
lean_inc(v_snd_1203_);
lean_dec(v_snd_1200_);
v___x_1204_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1205_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1191_, v_inputCtx_1197_, v_fst_1202_, v_snd_1203_, v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1221_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1221_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1221_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1210_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1211_ = l_Lean_mkListNode(v_a_1206_);
v___x_1212_ = lean_unsigned_to_nat(2u);
v___x_1213_ = lean_mk_empty_array_with_capacity(v___x_1212_);
v___x_1214_ = lean_array_push(v___x_1213_, v_fst_1201_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1211_);
v___x_1216_ = lean_box(2);
v___x_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1210_);
lean_ctor_set(v___x_1217_, 2, v___x_1215_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1217_);
v___x_1219_ = v___x_1208_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_fst_1201_);
v_a_1222_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1205_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1205_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_inputCtx_1197_);
lean_dec_ref(v_env_1191_);
v_a_1230_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1198_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1198_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1238_, lean_object* v_fname_1239_, lean_object* v_contents_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Parser_testParseModule(v_env_1238_, v_fname_1239_, v_contents_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1243_, lean_object* v_fname_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_IO_FS_readFile(v_fname_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_Parser_testParseModule(v_env_1243_, v_fname_1244_, v_a_1247_);
return v___x_1248_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_fname_1244_);
lean_dec_ref(v_env_1243_);
v_a_1249_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1246_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1257_, lean_object* v_fname_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Parser_testParseFile(v_env_1257_, v_fname_1258_);
return v_res_1260_;
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
