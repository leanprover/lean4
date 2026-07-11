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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
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
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_mk_io_user_error(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_17_, 1);
v___x_18_ = lean_obj_once(&l_Lean_Parser_Module_updateTokens___closed__3, &l_Lean_Parser_Module_updateTokens___closed__3_once, _init_l_Lean_Parser_Module_updateTokens___closed__3);
v___x_19_ = l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; 
v_a_20_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_17_, 1);
return v_a_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object* v_as_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_zero_29_; uint8_t v_isZero_30_; 
v_zero_29_ = lean_unsigned_to_nat(0u);
v_isZero_30_ = lean_nat_dec_eq(v_i_28_, v_zero_29_);
if (v_isZero_30_ == 1)
{
lean_object* v___x_31_; 
lean_dec(v_i_28_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
else
{
lean_object* v_one_32_; lean_object* v_n_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_one_32_ = lean_unsigned_to_nat(1u);
v_n_33_ = lean_nat_sub(v_i_28_, v_one_32_);
lean_dec(v_i_28_);
v___x_34_ = l_Subarray_get___redArg(v_as_27_, v_n_33_);
v___x_35_ = l_Lean_Syntax_getTailInfo(v___x_34_);
lean_dec(v___x_34_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_trailing_36_; lean_object* v___x_37_; 
lean_dec(v_n_33_);
v_trailing_36_ = lean_ctor_get(v___x_35_, 2);
lean_inc_ref(v_trailing_36_);
lean_dec_ref_known(v___x_35_, 4);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v_trailing_36_);
return v___x_37_;
}
else
{
lean_dec(v___x_35_);
v_i_28_ = v_n_33_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object* v_as_39_, lean_object* v_i_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_39_, v_i_40_);
lean_dec_ref(v_as_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object* v_s_42_){
_start:
{
lean_object* v___x_43_; lean_object* v_start_44_; lean_object* v_stop_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_43_ = l_Lean_Parser_SyntaxStack_toSubarray(v_s_42_);
v_start_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_start_44_);
v_stop_45_ = lean_ctor_get(v___x_43_, 2);
lean_inc(v_stop_45_);
v___x_46_ = lean_nat_sub(v_stop_45_, v_start_44_);
lean_dec(v_start_44_);
lean_dec(v_stop_45_);
v___x_47_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v___x_43_, v___x_46_);
lean_dec_ref(v___x_43_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object* v_as_48_, lean_object* v_i_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_48_, v_i_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object* v_as_52_, lean_object* v_i_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(v_as_52_, v_i_53_, v_a_54_);
lean_dec_ref(v_as_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* v_c_61_, lean_object* v_pos_62_, lean_object* v_stk_63_, lean_object* v_e_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v_pos_79_; lean_object* v_endPos_x3f_80_; lean_object* v_e_81_; lean_object* v_unexpectedTk_95_; lean_object* v_expected_96_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v_pos_108_; lean_object* v_endPos_x3f_109_; lean_object* v_endPos_x3f_117_; uint8_t v___x_118_; 
v_unexpectedTk_95_ = lean_ctor_get(v_e_64_, 0);
v_expected_96_ = lean_ctor_get(v_e_64_, 2);
v_endPos_x3f_117_ = lean_box(0);
v___x_118_ = l_Lean_Syntax_isMissing(v_unexpectedTk_95_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_inc(v_expected_96_);
lean_inc(v_unexpectedTk_95_);
lean_dec_ref(v_e_64_);
v___x_119_ = l_Lean_Syntax_getRange_x3f(v_unexpectedTk_95_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_pos_62_);
v_val_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_start_124_; lean_object* v_stop_125_; lean_object* v_endPos_x3f_127_; 
v_start_124_ = lean_ctor_get(v_val_120_, 0);
lean_inc(v_start_124_);
v_stop_125_ = lean_ctor_get(v_val_120_, 1);
lean_inc(v_stop_125_);
lean_dec(v_val_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v_stop_125_);
v_endPos_x3f_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_stop_125_);
v_endPos_x3f_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v_pos_108_ = v_start_124_;
v_endPos_x3f_109_ = v_endPos_x3f_127_;
goto v___jp_107_;
}
}
}
else
{
lean_dec(v___x_119_);
v_pos_108_ = v_pos_62_;
v_endPos_x3f_109_ = v_endPos_x3f_117_;
goto v___jp_107_;
}
}
else
{
lean_dec_ref(v_stk_63_);
v_pos_79_ = v_pos_62_;
v_endPos_x3f_80_ = v_endPos_x3f_117_;
v_e_81_ = v_e_64_;
goto v___jp_78_;
}
v___jp_65_:
{
uint8_t v___x_70_; uint8_t v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = 1;
v___x_71_ = 2;
v___x_72_ = 0;
v___x_73_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_74_ = l_Lean_Parser_Error_toString(v___y_67_);
v___x_75_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = l_Lean_MessageData_ofFormat(v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_77_, 0, v___y_66_);
lean_ctor_set(v___x_77_, 1, v___y_68_);
lean_ctor_set(v___x_77_, 2, v___y_69_);
lean_ctor_set(v___x_77_, 3, v___x_73_);
lean_ctor_set(v___x_77_, 4, v___x_76_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*5, v___x_70_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*5 + 1, v___x_71_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*5 + 2, v___x_72_);
return v___x_77_;
}
v___jp_78_:
{
lean_object* v_fileName_82_; lean_object* v_fileMap_83_; lean_object* v___x_84_; 
v_fileName_82_ = lean_ctor_get(v_c_61_, 1);
lean_inc_ref(v_fileName_82_);
v_fileMap_83_ = lean_ctor_get(v_c_61_, 2);
lean_inc_ref_n(v_fileMap_83_, 2);
lean_dec_ref(v_c_61_);
v___x_84_ = l_Lean_FileMap_toPosition(v_fileMap_83_, v_pos_79_);
lean_dec(v_pos_79_);
if (lean_obj_tag(v_endPos_x3f_80_) == 0)
{
lean_object* v___x_85_; 
lean_dec_ref(v_fileMap_83_);
v___x_85_ = lean_box(0);
v___y_66_ = v_fileName_82_;
v___y_67_ = v_e_81_;
v___y_68_ = v___x_84_;
v___y_69_ = v___x_85_;
goto v___jp_65_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_val_86_ = lean_ctor_get(v_endPos_x3f_80_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_endPos_x3f_80_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v_endPos_x3f_80_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v_endPos_x3f_80_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_FileMap_toPosition(v_fileMap_83_, v_val_86_);
lean_dec(v_val_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
v___y_66_ = v_fileName_82_;
v___y_67_ = v_e_81_;
v___y_68_ = v___x_84_;
v___y_69_ = v___x_92_;
goto v___jp_65_;
}
}
}
}
v___jp_97_:
{
lean_object* v_e_101_; lean_object* v___x_102_; 
v_e_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_e_101_, 0, v_unexpectedTk_95_);
lean_ctor_set(v_e_101_, 1, v___y_100_);
lean_ctor_set(v_e_101_, 2, v_expected_96_);
v___x_102_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(v_stk_63_);
if (lean_obj_tag(v___x_102_) == 1)
{
lean_object* v_val_103_; lean_object* v_startPos_104_; lean_object* v_stopPos_105_; uint8_t v___x_106_; 
v_val_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_102_, 1);
v_startPos_104_ = lean_ctor_get(v_val_103_, 1);
lean_inc(v_startPos_104_);
v_stopPos_105_ = lean_ctor_get(v_val_103_, 2);
lean_inc(v_stopPos_105_);
lean_dec(v_val_103_);
v___x_106_ = lean_nat_dec_eq(v_stopPos_105_, v___y_99_);
lean_dec(v_stopPos_105_);
if (v___x_106_ == 0)
{
lean_dec(v_startPos_104_);
v_pos_79_ = v___y_99_;
v_endPos_x3f_80_ = v___y_98_;
v_e_81_ = v_e_101_;
goto v___jp_78_;
}
else
{
lean_dec(v___y_99_);
v_pos_79_ = v_startPos_104_;
v_endPos_x3f_80_ = v___y_98_;
v_e_81_ = v_e_101_;
goto v___jp_78_;
}
}
else
{
lean_dec(v___x_102_);
v_pos_79_ = v___y_99_;
v_endPos_x3f_80_ = v___y_98_;
v_e_81_ = v_e_101_;
goto v___jp_78_;
}
}
v___jp_107_:
{
switch(lean_obj_tag(v_unexpectedTk_95_))
{
case 3:
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1));
v___y_98_ = v_endPos_x3f_109_;
v___y_99_ = v_pos_108_;
v___y_100_ = v___x_110_;
goto v___jp_97_;
}
case 2:
{
lean_object* v_val_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_val_111_ = lean_ctor_get(v_unexpectedTk_95_, 1);
v___x_112_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2));
v___x_113_ = lean_string_append(v___x_112_, v_val_111_);
v___x_114_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3));
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
v___y_98_ = v_endPos_x3f_109_;
v___y_99_ = v_pos_108_;
v___y_100_ = v___x_115_;
goto v___jp_97_;
}
default: 
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
v___y_98_ = v_endPos_x3f_109_;
v___y_99_ = v_pos_108_;
v___y_100_ = v___x_116_;
goto v___jp_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(lean_object* v_stx_130_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Syntax_getHeadInfo_x3f(v_stx_130_);
if (lean_obj_tag(v___x_135_) == 1)
{
lean_object* v_val_136_; 
v_val_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v___x_135_, 1);
if (lean_obj_tag(v_val_136_) == 0)
{
lean_object* v_leading_137_; lean_object* v_pos_138_; lean_object* v_trailing_139_; lean_object* v_endPos_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_162_; 
v_leading_137_ = lean_ctor_get(v_val_136_, 0);
v_pos_138_ = lean_ctor_get(v_val_136_, 1);
v_trailing_139_ = lean_ctor_get(v_val_136_, 2);
v_endPos_140_ = lean_ctor_get(v_val_136_, 3);
v_isSharedCheck_162_ = !lean_is_exclusive(v_val_136_);
if (v_isSharedCheck_162_ == 0)
{
v___x_142_ = v_val_136_;
v_isShared_143_ = v_isSharedCheck_162_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_endPos_140_);
lean_inc(v_trailing_139_);
lean_inc(v_pos_138_);
lean_inc(v_leading_137_);
lean_dec(v_val_136_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_162_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_str_144_; lean_object* v_stopPos_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_160_; 
v_str_144_ = lean_ctor_get(v_leading_137_, 0);
v_stopPos_145_ = lean_ctor_get(v_leading_137_, 2);
v_isSharedCheck_160_ = !lean_is_exclusive(v_leading_137_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_leading_137_, 1);
lean_dec(v_unused_161_);
v___x_147_ = v_leading_137_;
v_isShared_148_ = v_isSharedCheck_160_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_stopPos_145_);
lean_inc(v_str_144_);
lean_dec(v_leading_137_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_160_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(0u);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_str_144_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_stopPos_145_);
v___x_151_ = v_reuseFailAlloc_159_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_151_);
v___x_153_ = v___x_142_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_pos_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_trailing_139_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_endPos_140_);
v___x_153_ = v_reuseFailAlloc_158_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_Syntax_setHeadInfo(v_stx_130_, v___x_153_);
v___x_155_ = 1;
v___x_156_ = lean_box(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
}
}
}
}
else
{
lean_dec(v_val_136_);
goto v___jp_131_;
}
}
else
{
lean_dec(v___x_135_);
goto v___jp_131_;
}
v___jp_131_:
{
uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = 0;
v___x_133_ = lean_box(v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_stx_130_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 1;
return v___x_165_;
}
else
{
uint8_t v___x_166_; 
lean_dec_ref_known(v_x_164_, 1);
v___x_166_ = 0;
return v___x_166_;
}
}
else
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_167_; 
lean_dec_ref_known(v_x_163_, 1);
v___x_167_ = 0;
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v_val_169_; uint8_t v___x_170_; 
v_val_168_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v_x_163_, 1);
v_val_169_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v_x_164_, 1);
v___x_170_ = l_Lean_Parser_instBEqError_beq(v_val_168_, v_val_169_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_171_, v_x_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object* v_inputCtx_175_, lean_object* v_as_176_, size_t v_sz_177_, size_t v_i_178_, lean_object* v_b_179_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v_inputCtx_175_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_b_179_);
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v_snd_184_; lean_object* v_fst_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_188_; lean_object* v___x_189_; size_t v___x_190_; size_t v___x_191_; 
v_a_183_ = lean_array_uget_borrowed(v_as_176_, v_i_178_);
v_snd_184_ = lean_ctor_get(v_a_183_, 1);
v_fst_185_ = lean_ctor_get(v_a_183_, 0);
v_fst_186_ = lean_ctor_get(v_snd_184_, 0);
v_snd_187_ = lean_ctor_get(v_snd_184_, 1);
lean_inc(v_snd_187_);
lean_inc(v_fst_186_);
lean_inc(v_fst_185_);
lean_inc_ref(v_inputCtx_175_);
v___x_188_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_175_, v_fst_185_, v_fst_186_, v_snd_187_);
v___x_189_ = l_Lean_MessageLog_add(v___x_188_, v_b_179_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_178_, v___x_190_);
v_i_178_ = v___x_191_;
v_b_179_ = v___x_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object* v_inputCtx_193_, lean_object* v_as_194_, lean_object* v_sz_195_, lean_object* v_i_196_, lean_object* v_b_197_, lean_object* v___y_198_){
_start:
{
size_t v_sz_boxed_199_; size_t v_i_boxed_200_; lean_object* v_res_201_; 
v_sz_boxed_199_ = lean_unbox_usize(v_sz_195_);
lean_dec(v_sz_195_);
v_i_boxed_200_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_193_, v_as_194_, v_sz_boxed_199_, v_i_boxed_200_, v_b_197_);
lean_dec_ref(v_as_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t v___x_202_, lean_object* v_inputCtx_203_, lean_object* v_ref_204_, lean_object* v_msg_205_){
_start:
{
uint8_t v___x_206_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_218_; lean_object* v___x_224_; 
v___x_206_ = 0;
v___x_224_ = l_Lean_Syntax_getPos_x3f(v_ref_204_, v___x_206_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_224_, 1);
v___y_218_ = v_val_226_;
goto v___jp_217_;
}
v___jp_207_:
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = l_Lean_FileMap_toPosition(v___y_209_, v___y_211_);
lean_dec(v___y_211_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = 2;
v___x_215_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_216_, 0, v___y_210_);
lean_ctor_set(v___x_216_, 1, v___y_208_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
lean_ctor_set(v___x_216_, 3, v___x_215_);
lean_ctor_set(v___x_216_, 4, v_msg_205_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*5, v___x_202_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*5 + 1, v___x_214_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*5 + 2, v___x_206_);
return v___x_216_;
}
v___jp_217_:
{
lean_object* v_fileName_219_; lean_object* v_fileMap_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_fileName_219_ = lean_ctor_get(v_inputCtx_203_, 1);
lean_inc_ref(v_fileName_219_);
v_fileMap_220_ = lean_ctor_get(v_inputCtx_203_, 2);
lean_inc_ref_n(v_fileMap_220_, 2);
lean_dec_ref(v_inputCtx_203_);
v___x_221_ = l_Lean_FileMap_toPosition(v_fileMap_220_, v___y_218_);
v___x_222_ = l_Lean_Syntax_getTailPos_x3f(v_ref_204_, v___x_206_);
if (lean_obj_tag(v___x_222_) == 0)
{
v___y_208_ = v___x_221_;
v___y_209_ = v_fileMap_220_;
v___y_210_ = v_fileName_219_;
v___y_211_ = v___y_218_;
goto v___jp_207_;
}
else
{
lean_object* v_val_223_; 
lean_dec(v___y_218_);
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_208_ = v___x_221_;
v___y_209_ = v_fileMap_220_;
v___y_210_ = v_fileName_219_;
v___y_211_ = v_val_223_;
goto v___jp_207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_227_, lean_object* v_inputCtx_228_, lean_object* v_ref_229_, lean_object* v_msg_230_){
_start:
{
uint8_t v___x_5618__boxed_231_; lean_object* v_res_232_; 
v___x_5618__boxed_231_ = lean_unbox(v___x_227_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_5618__boxed_231_, v_inputCtx_228_, v_ref_229_, v_msg_230_);
lean_dec(v_ref_229_);
return v_res_232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
v___x_246_ = l_Lean_MessageData_ofFormat(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9));
v___x_251_ = l_Lean_MessageData_ofFormat(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15));
v___x_259_ = l_Lean_MessageData_ofFormat(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object* v_inputCtx_278_, lean_object* v_moduleTk_x3f_279_, lean_object* v_as_280_, size_t v_sz_281_, size_t v_i_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_a_286_; uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_282_, v_sz_281_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec_ref(v_inputCtx_278_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_b_283_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; lean_object* v_a_293_; uint8_t v___x_294_; 
v___x_292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4));
v_a_293_ = lean_array_uget_borrowed(v_as_280_, v_i_282_);
lean_inc(v_a_293_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_a_293_, v___x_292_);
if (v___x_294_ == 0)
{
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___y_296_; lean_object* v_messages_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v_messages_305_; lean_object* v___y_311_; uint8_t v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v_allTk_x3f_339_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v_metaTk_x3f_353_; lean_object* v_pubTk_x3f_365_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_375_ = l_Lean_Syntax_getArg(v_a_293_, v___x_335_);
v___x_376_ = l_Lean_Syntax_isNone(v___x_375_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; 
lean_inc(v___x_375_);
v___x_377_ = l_Lean_Syntax_matchesNull(v___x_375_, v___x_350_);
if (v___x_377_ == 0)
{
lean_dec(v___x_375_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = l_Lean_Syntax_getArg(v___x_375_, v___x_335_);
lean_dec(v___x_375_);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22));
lean_inc(v___x_378_);
v___x_380_ = l_Lean_Syntax_isOfKind(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec(v___x_378_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_Syntax_getArg(v___x_378_, v___x_335_);
lean_dec(v___x_378_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
v_pubTk_x3f_365_ = v___x_382_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec(v___x_375_);
v___x_383_ = lean_box(0);
v_pubTk_x3f_365_ = v___x_383_;
goto v___jp_364_;
}
v___jp_295_:
{
if (lean_obj_tag(v___y_296_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_val_298_ = lean_ctor_get(v___y_296_, 0);
lean_inc(v_val_298_);
lean_dec_ref_known(v___y_296_, 1);
v___x_299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7);
lean_inc_ref(v_inputCtx_278_);
v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_298_, v___x_299_);
lean_dec(v_val_298_);
v___x_301_ = l_Lean_MessageLog_add(v___x_300_, v_messages_297_);
v_a_286_ = v___x_301_;
goto v___jp_285_;
}
else
{
lean_dec(v___y_296_);
v_a_286_ = v_messages_297_;
goto v___jp_285_;
}
}
v___jp_302_:
{
if (lean_obj_tag(v___y_303_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_val_306_ = lean_ctor_get(v___y_303_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___y_303_, 1);
v___x_307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_278_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_306_, v___x_307_);
lean_dec(v_val_306_);
v___x_309_ = l_Lean_MessageLog_add(v___x_308_, v_messages_305_);
v___y_296_ = v___y_304_;
v_messages_297_ = v___x_309_;
goto v___jp_295_;
}
else
{
lean_dec(v___y_303_);
v___y_296_ = v___y_304_;
v_messages_297_ = v_messages_305_;
goto v___jp_295_;
}
}
v___jp_310_:
{
if (lean_obj_tag(v___y_314_) == 1)
{
if (lean_obj_tag(v___y_313_) == 0)
{
lean_dec_ref_known(v___y_314_, 1);
lean_dec(v___y_311_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_333_; 
v_isSharedCheck_333_ = !lean_is_exclusive(v___y_313_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___y_313_, 0);
lean_dec(v_unused_334_);
v___x_316_ = v___y_313_;
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___y_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
if (v___y_312_ == 0)
{
lean_del_object(v___x_316_);
lean_dec_ref_known(v___y_314_, 1);
lean_dec(v___y_311_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_val_318_ = lean_ctor_get(v___y_314_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___y_314_, 1);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_311_, v___y_312_);
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12));
v___x_323_ = lean_string_append(v___x_321_, v___x_322_);
v___x_324_ = lean_string_append(v___x_323_, v___x_320_);
lean_dec_ref(v___x_320_);
v___x_325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 3);
lean_ctor_set(v___x_316_, 0, v___x_326_);
v___x_328_ = v___x_316_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_MessageData_ofFormat(v___x_328_);
lean_inc_ref(v_inputCtx_278_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_318_, v___x_329_);
lean_dec(v_val_318_);
v___x_331_ = l_Lean_MessageLog_add(v___x_330_, v_b_283_);
v_a_286_ = v___x_331_;
goto v___jp_285_;
}
}
}
}
}
else
{
lean_dec(v___y_314_);
lean_dec(v___y_313_);
lean_dec(v___y_311_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
}
v___jp_336_:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(5u);
v___x_341_ = l_Lean_Syntax_getArg(v_a_293_, v___x_340_);
v___x_342_ = l_Lean_Syntax_matchesNull(v___x_341_, v___x_335_);
if (v___x_342_ == 0)
{
lean_dec(v_allTk_x3f_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = l_Lean_Syntax_getArg(v_a_293_, v___x_343_);
v___x_345_ = l_Lean_TSyntax_getId(v___x_344_);
lean_dec(v___x_344_);
if (lean_obj_tag(v_moduleTk_x3f_279_) == 0)
{
if (v___x_342_ == 0)
{
lean_dec(v___y_338_);
v___y_311_ = v___x_345_;
v___y_312_ = v___x_342_;
v___y_313_ = v___y_337_;
v___y_314_ = v_allTk_x3f_339_;
goto v___jp_310_;
}
else
{
lean_dec(v___x_345_);
if (lean_obj_tag(v___y_337_) == 1)
{
lean_object* v_val_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_val_346_ = lean_ctor_get(v___y_337_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___y_337_, 1);
v___x_347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
lean_inc_ref(v_inputCtx_278_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_346_, v___x_347_);
lean_dec(v_val_346_);
v___x_349_ = l_Lean_MessageLog_add(v___x_348_, v_b_283_);
v___y_303_ = v___y_338_;
v___y_304_ = v_allTk_x3f_339_;
v_messages_305_ = v___x_349_;
goto v___jp_302_;
}
else
{
lean_dec(v___y_337_);
v___y_303_ = v___y_338_;
v___y_304_ = v_allTk_x3f_339_;
v_messages_305_ = v_b_283_;
goto v___jp_302_;
}
}
}
else
{
lean_dec(v___y_338_);
v___y_311_ = v___x_345_;
v___y_312_ = v___x_342_;
v___y_313_ = v___y_337_;
v___y_314_ = v_allTk_x3f_339_;
goto v___jp_310_;
}
}
}
v___jp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = lean_unsigned_to_nat(3u);
v___x_355_ = l_Lean_Syntax_getArg(v_a_293_, v___x_354_);
v___x_356_ = l_Lean_Syntax_isNone(v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
lean_inc(v___x_355_);
v___x_357_ = l_Lean_Syntax_matchesNull(v___x_355_, v___x_350_);
if (v___x_357_ == 0)
{
lean_dec(v___x_355_);
lean_dec(v_metaTk_x3f_353_);
lean_dec(v___y_352_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = l_Lean_Syntax_getArg(v___x_355_, v___x_335_);
lean_dec(v___x_355_);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18));
lean_inc(v___x_358_);
v___x_360_ = l_Lean_Syntax_isOfKind(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec(v___x_358_);
lean_dec(v_metaTk_x3f_353_);
lean_dec(v___y_352_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = l_Lean_Syntax_getArg(v___x_358_, v___x_335_);
lean_dec(v___x_358_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___y_337_ = v___y_352_;
v___y_338_ = v_metaTk_x3f_353_;
v_allTk_x3f_339_ = v___x_362_;
goto v___jp_336_;
}
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v___x_355_);
v___x_363_ = lean_box(0);
v___y_337_ = v___y_352_;
v___y_338_ = v_metaTk_x3f_353_;
v_allTk_x3f_339_ = v___x_363_;
goto v___jp_336_;
}
}
v___jp_364_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = l_Lean_Syntax_getArg(v_a_293_, v___x_350_);
v___x_367_ = l_Lean_Syntax_isNone(v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
lean_inc(v___x_366_);
v___x_368_ = l_Lean_Syntax_matchesNull(v___x_366_, v___x_350_);
if (v___x_368_ == 0)
{
lean_dec(v___x_366_);
lean_dec(v_pubTk_x3f_365_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = l_Lean_Syntax_getArg(v___x_366_, v___x_335_);
lean_dec(v___x_366_);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20));
lean_inc(v___x_369_);
v___x_371_ = l_Lean_Syntax_isOfKind(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec(v___x_369_);
lean_dec(v_pubTk_x3f_365_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_Syntax_getArg(v___x_369_, v___x_335_);
lean_dec(v___x_369_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
v___y_352_ = v_pubTk_x3f_365_;
v_metaTk_x3f_353_ = v___x_373_;
goto v___jp_351_;
}
}
}
else
{
lean_object* v___x_374_; 
lean_dec(v___x_366_);
v___x_374_ = lean_box(0);
v___y_352_ = v_pubTk_x3f_365_;
v_metaTk_x3f_353_ = v___x_374_;
goto v___jp_351_;
}
}
}
}
v___jp_285_:
{
size_t v___x_287_; size_t v___x_288_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_282_, v___x_287_);
v_i_282_ = v___x_288_;
v_b_283_ = v_a_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* v_inputCtx_384_, lean_object* v_moduleTk_x3f_385_, lean_object* v_as_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_b_389_, lean_object* v___y_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_392_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_384_, v_moduleTk_x3f_385_, v_as_386_, v_sz_boxed_391_, v_i_boxed_392_, v_b_389_);
lean_dec_ref(v_as_386_);
lean_dec(v_moduleTk_x3f_385_);
return v_res_393_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(32u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3(void){
_start:
{
size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = ((size_t)5ULL);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_unsigned_to_nat(32u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___x_403_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__2, &l_Lean_Parser_parseHeader___closed__2_once, _init_l_Lean_Parser_parseHeader___closed__2);
v___x_404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_400_);
lean_ctor_set(v___x_404_, 3, v___x_400_);
lean_ctor_set_usize(v___x_404_, 4, v___x_399_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_NameSet_empty;
v___x_406_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__3, &l_Lean_Parser_parseHeader___closed__3_once, _init_l_Lean_Parser_parseHeader___closed__3);
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* v_inputCtx_420_){
_start:
{
uint32_t v___x_422_; lean_object* v___x_423_; 
v___x_422_ = 0;
v___x_423_ = l_Lean_mkEmptyEnvironment(v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_537_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_537_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_537_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_537_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v_fn_429_; lean_object* v_inputString_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_stxStack_441_; lean_object* v_pos_442_; lean_object* v_errorMsg_443_; lean_object* v___y_445_; lean_object* v_messages_446_; size_t v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___x_486_; size_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v_moduleTk_x3f_494_; lean_object* v___y_504_; uint8_t v___x_534_; 
v___x_428_ = l_Lean_Parser_Module_header;
v_fn_429_ = lean_ctor_get(v___x_428_, 1);
v_inputString_430_ = lean_ctor_get(v_inputCtx_420_, 0);
lean_inc(v_a_424_);
v___x_431_ = l_Lean_Parser_getTokenTable(v_a_424_);
v___x_432_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_429_);
v___x_433_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_433_, 0, v___x_432_);
lean_closure_set(v___x_433_, 1, v_fn_429_);
v___x_434_ = l_Lean_Parser_Module_updateTokens(v___x_431_);
v___x_435_ = l_Lean_Options_empty;
v___x_436_ = lean_box(0);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_438_, 0, v_a_424_);
lean_ctor_set(v___x_438_, 1, v___x_435_);
lean_ctor_set(v___x_438_, 2, v___x_436_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
v___x_439_ = l_Lean_Parser_mkParserState(v_inputString_430_);
lean_inc_ref(v_inputCtx_420_);
v___x_440_ = l_Lean_Parser_ParserFn_run(v___x_433_, v_inputCtx_420_, v___x_438_, v___x_434_, v___x_439_);
v_stxStack_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc_ref(v_stxStack_441_);
v_pos_442_ = lean_ctor_get(v___x_440_, 2);
lean_inc(v_pos_442_);
v_errorMsg_443_ = lean_ctor_get(v___x_440_, 4);
lean_inc(v_errorMsg_443_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_441_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_441_);
lean_dec_ref(v_stxStack_441_);
v___y_504_ = v___x_535_;
goto v___jp_503_;
}
else
{
lean_object* v___x_536_; 
lean_dec_ref(v_stxStack_441_);
v___x_536_ = lean_box(0);
v___y_504_ = v___x_536_;
goto v___jp_503_;
}
v___jp_444_:
{
lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_466_; 
v___x_447_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_445_);
v_fst_448_ = lean_ctor_get(v___x_447_, 0);
v_snd_449_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_466_ == 0)
{
v___x_451_ = v___x_447_;
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v___x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_453_ = lean_box(0);
v___x_454_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_443_, v___x_453_);
v___x_455_ = lean_bool_not(v___x_454_);
v___x_456_ = lean_unbox(v_snd_449_);
lean_dec(v_snd_449_);
v___x_457_ = lean_bool_not(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_458_, 0, v_pos_442_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_455_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1 + 1, v___x_457_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_messages_446_);
lean_ctor_set(v___x_451_, 0, v___x_458_);
v___x_460_ = v___x_451_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_messages_446_);
v___x_460_ = v_reuseFailAlloc_465_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_fst_448_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_461_);
v___x_463_ = v___x_426_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
v___jp_467_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; size_t v_sz_475_; lean_object* v___x_476_; 
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = l_Lean_Syntax_getArg(v___y_471_, v___x_472_);
v___x_474_ = l_Lean_Syntax_getArgs(v___x_473_);
lean_dec(v___x_473_);
v_sz_475_ = lean_array_size(v___x_474_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_420_, v___y_470_, v___x_474_, v_sz_475_, v___y_468_, v___y_469_);
lean_dec_ref(v___x_474_);
lean_dec(v___y_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v___y_445_ = v___y_471_;
v_messages_446_ = v_a_477_;
goto v___jp_444_;
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v___y_471_);
lean_dec(v_errorMsg_443_);
lean_dec(v_pos_442_);
lean_del_object(v___x_426_);
v_a_478_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_476_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
v___jp_487_:
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = l_Lean_Syntax_getArg(v___y_491_, v___x_495_);
v___x_497_ = l_Lean_Syntax_isNone(v___x_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
lean_inc(v___x_496_);
v___x_498_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_495_);
if (v___x_498_ == 0)
{
lean_dec(v___x_496_);
lean_dec(v_moduleTk_x3f_494_);
lean_dec_ref(v_inputCtx_420_);
v___y_445_ = v___y_491_;
v_messages_446_ = v___y_490_;
goto v___jp_444_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_499_ = l_Lean_Syntax_getArg(v___x_496_, v___x_486_);
lean_dec(v___x_496_);
v___x_500_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_489_);
lean_inc_ref(v___y_492_);
lean_inc_ref(v___y_493_);
v___x_501_ = l_Lean_Name_mkStr4(v___y_493_, v___y_492_, v___y_489_, v___x_500_);
v___x_502_ = l_Lean_Syntax_isOfKind(v___x_499_, v___x_501_);
lean_dec(v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v_moduleTk_x3f_494_);
lean_dec_ref(v_inputCtx_420_);
v___y_445_ = v___y_491_;
v_messages_446_ = v___y_490_;
goto v___jp_444_;
}
else
{
v___y_468_ = v___y_488_;
v___y_469_ = v___y_490_;
v___y_470_ = v_moduleTk_x3f_494_;
v___y_471_ = v___y_491_;
goto v___jp_467_;
}
}
}
else
{
lean_dec(v___x_496_);
v___y_468_ = v___y_488_;
v___y_469_ = v___y_490_;
v___y_470_ = v_moduleTk_x3f_494_;
v___y_471_ = v___y_491_;
goto v___jp_467_;
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; size_t v_sz_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_505_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_506_ = l_Lean_Parser_ParserState_allErrors(v___x_440_);
v_sz_507_ = lean_array_size(v___x_506_);
v___x_508_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_420_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_420_, v___x_506_, v_sz_507_, v___x_508_, v___x_505_);
lean_dec_ref(v___x_506_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_514_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_504_);
v___x_515_ = l_Lean_Syntax_isOfKind(v___y_504_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_inputCtx_420_);
v___y_445_ = v___y_504_;
v_messages_446_ = v_a_510_;
goto v___jp_444_;
}
else
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = l_Lean_Syntax_getArg(v___y_504_, v___x_486_);
v___x_517_ = l_Lean_Syntax_isNone(v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_516_);
v___x_519_ = l_Lean_Syntax_matchesNull(v___x_516_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v___x_516_);
lean_dec_ref(v_inputCtx_420_);
v___y_445_ = v___y_504_;
v_messages_446_ = v_a_510_;
goto v___jp_444_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = l_Lean_Syntax_getArg(v___x_516_, v___x_486_);
lean_dec(v___x_516_);
v___x_521_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_520_);
v___x_522_ = l_Lean_Syntax_isOfKind(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v___x_520_);
lean_dec_ref(v_inputCtx_420_);
v___y_445_ = v___y_504_;
v_messages_446_ = v_a_510_;
goto v___jp_444_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = l_Lean_Syntax_getArg(v___x_520_, v___x_486_);
lean_dec(v___x_520_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
v___y_488_ = v___x_508_;
v___y_489_ = v___x_513_;
v___y_490_ = v_a_510_;
v___y_491_ = v___y_504_;
v___y_492_ = v___x_512_;
v___y_493_ = v___x_511_;
v_moduleTk_x3f_494_ = v___x_524_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v___x_516_);
v___x_525_ = lean_box(0);
v___y_488_ = v___x_508_;
v___y_489_ = v___x_513_;
v___y_490_ = v_a_510_;
v___y_491_ = v___y_504_;
v___y_492_ = v___x_512_;
v___y_493_ = v___x_511_;
v_moduleTk_x3f_494_ = v___x_525_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v___y_504_);
lean_dec(v_errorMsg_443_);
lean_dec(v_pos_442_);
lean_del_object(v___x_426_);
lean_dec_ref(v_inputCtx_420_);
v_a_526_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_509_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_509_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_inputCtx_420_);
v_a_538_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_423_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_423_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Parser_parseHeader(v_inputCtx_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_556_, lean_object* v_pos_557_){
_start:
{
lean_object* v___y_559_; lean_object* v_inputString_569_; lean_object* v_endPos_570_; uint8_t v___x_571_; 
v_inputString_569_ = lean_ctor_get(v_inputCtx_556_, 0);
v_endPos_570_ = lean_ctor_get(v_inputCtx_556_, 3);
v___x_571_ = lean_nat_dec_le(v_pos_557_, v_endPos_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_inc(v_endPos_570_);
lean_inc(v_pos_557_);
lean_inc_ref(v_inputString_569_);
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v_inputString_569_);
lean_ctor_set(v___x_572_, 1, v_pos_557_);
lean_ctor_set(v___x_572_, 2, v_endPos_570_);
v___y_559_ = v___x_572_;
goto v___jp_558_;
}
else
{
lean_object* v___x_573_; 
lean_inc_n(v_pos_557_, 2);
lean_inc_ref(v_inputString_569_);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v_inputString_569_);
lean_ctor_set(v___x_573_, 1, v_pos_557_);
lean_ctor_set(v___x_573_, 2, v_pos_557_);
v___y_559_ = v___x_573_;
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_atom_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc(v_pos_557_);
lean_inc_ref(v___y_559_);
v___x_560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_560_, 0, v___y_559_);
lean_ctor_set(v___x_560_, 1, v_pos_557_);
lean_ctor_set(v___x_560_, 2, v___y_559_);
lean_ctor_set(v___x_560_, 3, v_pos_557_);
v___x_561_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_562_, 0, v___x_560_);
lean_ctor_set(v_atom_562_, 1, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_566_ = lean_array_push(v___x_565_, v_atom_562_);
v___x_567_ = lean_box(2);
v___x_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_563_);
lean_ctor_set(v___x_568_, 2, v___x_566_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_574_, lean_object* v_pos_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_574_, v_pos_575_);
lean_dec_ref(v_inputCtx_574_);
return v_res_576_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_588_){
_start:
{
uint8_t v___y_590_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_588_);
v___x_594_ = l_Lean_Syntax_isOfKind(v_s_588_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_588_);
v___x_596_ = l_Lean_Syntax_isOfKind(v_s_588_, v___x_595_);
v___y_590_ = v___x_596_;
goto v___jp_589_;
}
else
{
v___y_590_ = v___x_594_;
goto v___jp_589_;
}
v___jp_589_:
{
if (v___y_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_592_ = l_Lean_Syntax_isOfKind(v_s_588_, v___x_591_);
return v___x_592_;
}
else
{
lean_dec(v_s_588_);
return v___y_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* v_s_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Lean_Parser_isTerminalCommand(v_s_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2(void){
_start:
{
uint32_t v___x_604_; lean_object* v___x_605_; 
v___x_604_ = 32;
v___x_605_ = l_Char_utf8Size(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_606_, lean_object* v_pmctx_607_, lean_object* v_pos_608_){
_start:
{
lean_object* v_inputString_609_; lean_object* v_env_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_s_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_s_619_; lean_object* v_errorMsg_620_; 
v_inputString_609_ = lean_ctor_get(v_inputCtx_606_, 0);
v_env_610_ = lean_ctor_get(v_pmctx_607_, 0);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_613_ = l_Lean_Parser_SyntaxStack_empty;
v___x_614_ = l_Lean_Parser_initCacheForInput(v_inputString_609_);
v___x_615_ = lean_box(0);
lean_inc(v_pos_608_);
v_s_616_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_616_, 0, v___x_613_);
lean_ctor_set(v_s_616_, 1, v___x_611_);
lean_ctor_set(v_s_616_, 2, v_pos_608_);
lean_ctor_set(v_s_616_, 3, v___x_614_);
lean_ctor_set(v_s_616_, 4, v___x_615_);
lean_ctor_set(v_s_616_, 5, v___x_612_);
v___x_617_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_610_);
v___x_618_ = l_Lean_Parser_getTokenTable(v_env_610_);
v_s_619_ = l_Lean_Parser_ParserFn_run(v___x_617_, v_inputCtx_606_, v_pmctx_607_, v___x_618_, v_s_616_);
v_errorMsg_620_ = lean_ctor_get(v_s_619_, 4);
lean_inc(v_errorMsg_620_);
if (lean_obj_tag(v_errorMsg_620_) == 0)
{
lean_object* v_pos_621_; 
lean_dec(v_pos_608_);
v_pos_621_ = lean_ctor_get(v_s_619_, 2);
lean_inc(v_pos_621_);
lean_dec_ref(v_s_619_);
return v_pos_621_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref_known(v_errorMsg_620_, 1);
lean_dec_ref(v_s_619_);
v___x_622_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
v___x_623_ = lean_nat_add(v_pos_608_, v___x_622_);
lean_dec(v_pos_608_);
return v___x_623_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_629_ = l_Lean_Parser_categoryParser(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_631_ = l_Lean_Parser_withPosition(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; lean_object* v_fn_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_635_ = lean_ctor_get(v___x_634_, 1);
lean_inc_ref(v_fn_635_);
v___x_636_ = lean_apply_2(v_fn_635_, v_a_632_, v_a_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_637_, lean_object* v_as_638_, size_t v_sz_639_, size_t v_i_640_, lean_object* v_b_641_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_640_, v_sz_639_);
if (v___x_642_ == 0)
{
lean_dec_ref(v_inputCtx_637_);
return v_b_641_;
}
else
{
lean_object* v_a_643_; lean_object* v_snd_644_; lean_object* v_fst_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v___x_648_; lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; 
v_a_643_ = lean_array_uget_borrowed(v_as_638_, v_i_640_);
v_snd_644_ = lean_ctor_get(v_a_643_, 1);
v_fst_645_ = lean_ctor_get(v_a_643_, 0);
v_fst_646_ = lean_ctor_get(v_snd_644_, 0);
v_snd_647_ = lean_ctor_get(v_snd_644_, 1);
lean_inc(v_snd_647_);
lean_inc(v_fst_646_);
lean_inc(v_fst_645_);
lean_inc_ref(v_inputCtx_637_);
v___x_648_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_637_, v_fst_645_, v_fst_646_, v_snd_647_);
v___x_649_ = l_Lean_MessageLog_add(v___x_648_, v_b_641_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_640_, v___x_650_);
v_i_640_ = v___x_651_;
v_b_641_ = v___x_649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_653_, lean_object* v_as_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_b_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_659_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_653_, v_as_654_, v_sz_boxed_658_, v_i_boxed_659_, v_b_657_);
lean_dec_ref(v_as_654_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_snd_661_, uint8_t v___x_662_, lean_object* v_inputCtx_663_, lean_object* v_pos_664_, lean_object* v_stxStack_665_, lean_object* v_val_666_, lean_object* v___x_667_, lean_object* v_fst_668_, lean_object* v_____r_669_, lean_object* v_pos_670_){
_start:
{
lean_object* v_messages_672_; uint8_t v___y_679_; uint8_t v___y_689_; uint8_t v___x_691_; 
v___x_691_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_665_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_665_);
v___x_693_ = l_Lean_Syntax_getPos_x3f(v___x_692_, v___x_691_);
lean_dec(v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
v___y_689_ = v___x_662_;
goto v___jp_688_;
}
else
{
lean_dec_ref_known(v___x_693_, 1);
v___y_689_ = v___x_691_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___x_662_;
goto v___jp_688_;
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_messages_672_);
lean_ctor_set(v___x_673_, 1, v_snd_661_);
v___x_674_ = lean_box(v___x_662_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_pos_670_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc_ref(v_stxStack_665_);
v___x_680_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_663_, v_pos_664_, v_stxStack_665_, v_val_666_);
v___x_681_ = l_Lean_MessageLog_add(v___x_680_, v___x_667_);
if (v___y_679_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_snd_661_);
v___x_682_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_665_);
lean_dec_ref(v_stxStack_665_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_box(v___x_662_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_pos_670_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
else
{
lean_dec_ref(v_stxStack_665_);
v_messages_672_ = v___x_681_;
goto v___jp_671_;
}
}
v___jp_688_:
{
uint8_t v___x_690_; 
v___x_690_ = lean_unbox(v_fst_668_);
if (v___x_690_ == 0)
{
v___y_679_ = v___y_689_;
goto v___jp_678_;
}
else
{
if (v___y_689_ == 0)
{
v___y_679_ = v___y_689_;
goto v___jp_678_;
}
else
{
lean_dec_ref(v_val_666_);
lean_dec_ref(v_stxStack_665_);
lean_dec(v_pos_664_);
lean_dec_ref(v_inputCtx_663_);
v_messages_672_ = v___x_667_;
goto v___jp_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_snd_694_, lean_object* v___x_695_, lean_object* v_inputCtx_696_, lean_object* v_pos_697_, lean_object* v_stxStack_698_, lean_object* v_val_699_, lean_object* v___x_700_, lean_object* v_fst_701_, lean_object* v_____r_702_, lean_object* v_pos_703_){
_start:
{
uint8_t v___x_2285__boxed_704_; lean_object* v_res_705_; 
v___x_2285__boxed_704_ = lean_unbox(v___x_695_);
v_res_705_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_694_, v___x_2285__boxed_704_, v_inputCtx_696_, v_pos_697_, v_stxStack_698_, v_val_699_, v___x_700_, v_fst_701_, v_____r_702_, v_pos_703_);
lean_dec(v_fst_701_);
return v_res_705_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_707_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_708_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_708_, 0, v___x_707_);
lean_closure_set(v___x_708_, 1, v___x_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_709_, lean_object* v_pmctx_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___y_713_; lean_object* v_snd_717_; lean_object* v_snd_718_; lean_object* v_fst_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_795_; 
v_snd_717_ = lean_ctor_get(v_a_711_, 1);
lean_inc(v_snd_717_);
v_snd_718_ = lean_ctor_get(v_snd_717_, 1);
lean_inc(v_snd_718_);
v_fst_719_ = lean_ctor_get(v_a_711_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_a_711_, 1);
lean_dec(v_unused_796_);
v___x_721_ = v_a_711_;
v_isShared_722_ = v_isSharedCheck_795_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_fst_719_);
lean_dec(v_a_711_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_795_;
goto v_resetjp_720_;
}
v___jp_712_:
{
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v_a_714_; 
lean_dec_ref(v_pmctx_710_);
lean_dec_ref(v_inputCtx_709_);
v_a_714_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___y_713_, 1);
return v_a_714_;
}
else
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___y_713_, 1);
v_a_711_ = v_a_715_;
goto _start;
}
}
v_resetjp_720_:
{
lean_object* v_fst_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_793_; 
v_fst_723_ = lean_ctor_get(v_snd_717_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_snd_717_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_snd_717_, 1);
lean_dec(v_unused_794_);
v___x_725_ = v_snd_717_;
v_isShared_726_ = v_isSharedCheck_793_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_fst_723_);
lean_dec(v_snd_717_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_793_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_792_; 
v_fst_727_ = lean_ctor_get(v_snd_718_, 0);
v_snd_728_ = lean_ctor_get(v_snd_718_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_snd_718_);
if (v_isSharedCheck_792_ == 0)
{
v___x_730_ = v_snd_718_;
v_isShared_731_ = v_isSharedCheck_792_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_dec(v_snd_718_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_792_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_709_, v_fst_719_);
if (v___x_732_ == 0)
{
lean_object* v_env_733_; lean_object* v_inputString_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_stxStack_744_; lean_object* v_pos_745_; lean_object* v_errorMsg_746_; lean_object* v_recoveredErrors_747_; uint8_t v___x_748_; size_t v_sz_749_; size_t v___x_750_; lean_object* v___x_751_; uint8_t v___y_753_; uint8_t v___x_772_; 
v_env_733_ = lean_ctor_get(v_pmctx_710_, 0);
v_inputString_734_ = lean_ctor_get(v_inputCtx_709_, 0);
v___x_735_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_733_);
v___x_736_ = l_Lean_Parser_getTokenTable(v_env_733_);
v___x_737_ = l_Lean_Parser_SyntaxStack_empty;
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_Parser_initCacheForInput(v_inputString_734_);
v___x_740_ = lean_box(0);
v___x_741_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_719_);
v___x_742_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_742_, 0, v___x_737_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
lean_ctor_set(v___x_742_, 2, v_fst_719_);
lean_ctor_set(v___x_742_, 3, v___x_739_);
lean_ctor_set(v___x_742_, 4, v___x_740_);
lean_ctor_set(v___x_742_, 5, v___x_741_);
lean_inc_ref(v_pmctx_710_);
lean_inc_ref_n(v_inputCtx_709_, 2);
v___x_743_ = l_Lean_Parser_ParserFn_run(v___x_735_, v_inputCtx_709_, v_pmctx_710_, v___x_736_, v___x_742_);
v_stxStack_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_stxStack_744_);
v_pos_745_ = lean_ctor_get(v___x_743_, 2);
lean_inc(v_pos_745_);
v_errorMsg_746_ = lean_ctor_get(v___x_743_, 4);
lean_inc(v_errorMsg_746_);
v_recoveredErrors_747_ = lean_ctor_get(v___x_743_, 5);
lean_inc_ref(v_recoveredErrors_747_);
lean_dec_ref(v___x_743_);
v___x_748_ = 1;
v_sz_749_ = lean_array_size(v_recoveredErrors_747_);
v___x_750_ = ((size_t)0ULL);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_709_, v_recoveredErrors_747_, v_sz_749_, v___x_750_, v_fst_727_);
lean_dec_ref(v_recoveredErrors_747_);
v___x_772_ = lean_unbox(v_fst_723_);
if (v___x_772_ == 0)
{
uint8_t v___x_773_; 
v___x_773_ = lean_unbox(v_fst_723_);
v___y_753_ = v___x_773_;
goto v___jp_752_;
}
else
{
uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_774_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_744_);
v___x_775_ = lean_bool_not(v___x_774_);
if (v___x_775_ == 0)
{
v___y_753_ = v___x_775_;
goto v___jp_752_;
}
else
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_744_);
v___x_777_ = l_Lean_Syntax_isAntiquot(v___x_776_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
v___y_753_ = v___x_777_;
goto v___jp_752_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v_errorMsg_746_);
lean_dec_ref(v_stxStack_744_);
lean_del_object(v___x_730_);
lean_del_object(v___x_725_);
lean_del_object(v___x_721_);
lean_dec(v_fst_719_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_751_);
lean_ctor_set(v___x_778_, 1, v_snd_728_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_723_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_pos_745_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v_a_711_ = v___x_780_;
goto _start;
}
}
}
v___jp_752_:
{
if (lean_obj_tag(v_errorMsg_746_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_756_; 
lean_dec(v_snd_728_);
lean_dec(v_fst_723_);
lean_dec(v_fst_719_);
lean_dec_ref(v_pmctx_710_);
lean_dec_ref(v_inputCtx_709_);
v___x_754_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_744_);
lean_dec_ref(v_stxStack_744_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_754_);
lean_ctor_set(v___x_730_, 0, v___x_751_);
v___x_756_ = v___x_730_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_764_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_box(v___y_753_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_756_);
lean_ctor_set(v___x_725_, 0, v___x_757_);
v___x_759_ = v___x_725_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_756_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_759_);
lean_ctor_set(v___x_721_, 0, v_pos_745_);
v___x_761_ = v___x_721_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_pos_745_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_val_765_; uint8_t v___x_766_; 
lean_del_object(v___x_730_);
lean_del_object(v___x_725_);
lean_del_object(v___x_721_);
v_val_765_ = lean_ctor_get(v_errorMsg_746_, 0);
lean_inc(v_val_765_);
lean_dec_ref_known(v_errorMsg_746_, 1);
v___x_766_ = lean_nat_dec_eq(v_pos_745_, v_fst_719_);
lean_dec(v_fst_719_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_box(0);
lean_inc(v_pos_745_);
lean_inc_ref(v_inputCtx_709_);
v___x_768_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_728_, v___x_748_, v_inputCtx_709_, v_pos_745_, v_stxStack_744_, v_val_765_, v___x_751_, v_fst_723_, v___x_767_, v_pos_745_);
lean_dec(v_fst_723_);
v___y_713_ = v___x_768_;
goto v___jp_712_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc(v_pos_745_);
lean_inc_ref(v_pmctx_710_);
lean_inc_ref_n(v_inputCtx_709_, 2);
v___x_769_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_709_, v_pmctx_710_, v_pos_745_);
v___x_770_ = lean_box(0);
v___x_771_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_728_, v___x_748_, v_inputCtx_709_, v_pos_745_, v_stxStack_744_, v_val_765_, v___x_751_, v_fst_723_, v___x_770_, v___x_769_);
lean_dec(v_fst_723_);
v___y_713_ = v___x_771_;
goto v___jp_712_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v_snd_728_);
lean_dec_ref(v_pmctx_710_);
lean_inc(v_fst_719_);
v___x_782_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_709_, v_fst_719_);
lean_dec_ref(v_inputCtx_709_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_782_);
v___x_784_ = v___x_730_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_791_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_784_);
v___x_786_ = v___x_725_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_723_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_786_);
v___x_788_ = v___x_721_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_719_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_797_, lean_object* v_pmctx_798_, lean_object* v_mps_799_, lean_object* v_messages_800_){
_start:
{
lean_object* v_pos_801_; uint8_t v_recovering_802_; uint8_t v_hasLeading_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_843_; 
v_pos_801_ = lean_ctor_get(v_mps_799_, 0);
v_recovering_802_ = lean_ctor_get_uint8(v_mps_799_, sizeof(void*)*1);
v_hasLeading_803_ = lean_ctor_get_uint8(v_mps_799_, sizeof(void*)*1 + 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_mps_799_);
if (v_isSharedCheck_843_ == 0)
{
v___x_805_ = v_mps_799_;
v_isShared_806_ = v_isSharedCheck_843_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_pos_801_);
lean_dec(v_mps_799_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_843_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_stx_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_snd_813_; lean_object* v_snd_814_; lean_object* v_fst_815_; lean_object* v_fst_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_841_; 
v_stx_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_messages_800_);
lean_ctor_set(v___x_808_, 1, v_stx_807_);
v___x_809_ = lean_box(v_recovering_802_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_pos_801_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_797_, v_pmctx_798_, v___x_811_);
v_snd_813_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_snd_813_);
v_snd_814_ = lean_ctor_get(v_snd_813_, 1);
lean_inc(v_snd_814_);
v_fst_815_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_fst_815_);
lean_dec_ref(v___x_812_);
v_fst_816_ = lean_ctor_get(v_snd_813_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_snd_813_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_snd_813_, 1);
lean_dec(v_unused_842_);
v___x_818_ = v_snd_813_;
v_isShared_819_ = v_isSharedCheck_841_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_fst_816_);
lean_dec(v_snd_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_841_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_840_; 
v_fst_820_ = lean_ctor_get(v_snd_814_, 0);
v_snd_821_ = lean_ctor_get(v_snd_814_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_snd_814_);
if (v_isSharedCheck_840_ == 0)
{
v___x_823_ = v_snd_814_;
v_isShared_824_ = v_isSharedCheck_840_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v_snd_814_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_840_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_stx_826_; 
if (v_hasLeading_803_ == 0)
{
v_stx_826_ = v_snd_821_;
goto v___jp_825_;
}
else
{
lean_object* v___x_838_; lean_object* v_fst_839_; 
v___x_838_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_821_);
v_fst_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_fst_839_);
lean_dec_ref(v___x_838_);
v_stx_826_ = v_fst_839_;
goto v___jp_825_;
}
v___jp_825_:
{
uint8_t v___x_827_; lean_object* v___x_829_; 
v___x_827_ = 0;
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_fst_815_);
v___x_829_ = v___x_805_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fst_815_);
v___x_829_ = v_reuseFailAlloc_837_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
uint8_t v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_unbox(v_fst_816_);
lean_dec(v_fst_816_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___x_830_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1 + 1, v___x_827_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_fst_820_);
lean_ctor_set(v___x_823_, 0, v___x_829_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_fst_820_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_832_);
lean_ctor_set(v___x_818_, 0, v_stx_826_);
v___x_834_ = v___x_818_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_stx_826_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_844_, lean_object* v_pmctx_845_, lean_object* v_inst_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_844_, v_pmctx_845_, v_a_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_putStr_852_; lean_object* v___x_853_; 
v___x_851_ = lean_get_stdout();
v_putStr_852_ = lean_ctor_get(v___x_851_, 4);
lean_inc_ref(v_putStr_852_);
lean_dec_ref(v___x_851_);
v___x_853_ = lean_apply_2(v_putStr_852_, v_s_849_, lean_box(0));
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_857_){
_start:
{
uint32_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 10;
v___x_860_ = lean_string_push(v_s_857_, v___x_859_);
v___x_861_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___x_865_, lean_object* v_msg_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = l_Lean_Message_toString(v_msg_866_, v___x_865_);
v___x_869_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___x_870_, lean_object* v_msg_871_, lean_object* v___y_872_){
_start:
{
uint8_t v___x_1530__boxed_873_; lean_object* v_res_874_; 
v___x_1530__boxed_873_ = lean_unbox(v___x_870_);
v_res_874_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___x_1530__boxed_873_, v_msg_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_875_, lean_object* v_as_876_, size_t v_i_877_, size_t v_stop_878_, lean_object* v_b_879_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_eq(v_i_877_, v_stop_878_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_array_uget_borrowed(v_as_876_, v_i_877_);
lean_inc_ref(v_f_875_);
lean_inc(v___x_882_);
v___x_883_ = lean_apply_2(v_f_875_, v___x_882_, lean_box(0));
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; size_t v___x_885_; size_t v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_877_, v___x_885_);
v_i_877_ = v___x_886_;
v_b_879_ = v_a_884_;
goto _start;
}
else
{
lean_dec_ref(v_f_875_);
return v___x_883_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec_ref(v_f_875_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_b_879_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_889_, lean_object* v_as_890_, lean_object* v_i_891_, lean_object* v_stop_892_, lean_object* v_b_893_, lean_object* v___y_894_){
_start:
{
size_t v_i_boxed_895_; size_t v_stop_boxed_896_; lean_object* v_res_897_; 
v_i_boxed_895_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_stop_boxed_896_ = lean_unbox_usize(v_stop_892_);
lean_dec(v_stop_892_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_889_, v_as_890_, v_i_boxed_895_, v_stop_boxed_896_, v_b_893_);
lean_dec_ref(v_as_890_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_898_, lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v_cs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_922_; 
v_cs_901_ = lean_ctor_get(v_x_899_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_899_);
if (v_isSharedCheck_922_ == 0)
{
v___x_903_ = v_x_899_;
v_isShared_904_ = v_isSharedCheck_922_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_cs_901_);
lean_dec(v_x_899_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_922_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_array_get_size(v_cs_901_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_nat_dec_lt(v___x_905_, v___x_906_);
if (v___x_908_ == 0)
{
lean_object* v___x_910_; 
lean_dec_ref(v_cs_901_);
lean_dec_ref(v_f_898_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_907_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_907_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
uint8_t v___x_912_; 
v___x_912_ = lean_nat_dec_le(v___x_906_, v___x_906_);
if (v___x_912_ == 0)
{
if (v___x_908_ == 0)
{
lean_object* v___x_914_; 
lean_dec_ref(v_cs_901_);
lean_dec_ref(v_f_898_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_907_);
v___x_914_ = v___x_903_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_907_);
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
size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
lean_del_object(v___x_903_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_906_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_898_, v_cs_901_, v___x_916_, v___x_917_, v___x_907_);
lean_dec_ref(v_cs_901_);
return v___x_918_;
}
}
else
{
size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
lean_del_object(v___x_903_);
v___x_919_ = ((size_t)0ULL);
v___x_920_ = lean_usize_of_nat(v___x_906_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_898_, v_cs_901_, v___x_919_, v___x_920_, v___x_907_);
lean_dec_ref(v_cs_901_);
return v___x_921_;
}
}
}
}
else
{
lean_object* v_vs_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_944_; 
v_vs_923_ = lean_ctor_get(v_x_899_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_x_899_);
if (v_isSharedCheck_944_ == 0)
{
v___x_925_ = v_x_899_;
v_isShared_926_ = v_isSharedCheck_944_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_vs_923_);
lean_dec(v_x_899_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_944_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v_vs_923_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_930_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v_vs_923_);
lean_dec_ref(v_f_898_);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 0);
lean_ctor_set(v___x_925_, 0, v___x_929_);
v___x_932_ = v___x_925_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_929_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
uint8_t v___x_934_; 
v___x_934_ = lean_nat_dec_le(v___x_928_, v___x_928_);
if (v___x_934_ == 0)
{
if (v___x_930_ == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v_vs_923_);
lean_dec_ref(v_f_898_);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 0);
lean_ctor_set(v___x_925_, 0, v___x_929_);
v___x_936_ = v___x_925_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_929_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_925_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = lean_usize_of_nat(v___x_928_);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_898_, v_vs_923_, v___x_938_, v___x_939_, v___x_929_);
lean_dec_ref(v_vs_923_);
return v___x_940_;
}
}
else
{
size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_925_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = lean_usize_of_nat(v___x_928_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_898_, v_vs_923_, v___x_941_, v___x_942_, v___x_929_);
lean_dec_ref(v_vs_923_);
return v___x_943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_945_, lean_object* v_as_946_, size_t v_i_947_, size_t v_stop_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_eq(v_i_947_, v_stop_948_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_array_uget_borrowed(v_as_946_, v_i_947_);
lean_inc(v___x_952_);
lean_inc_ref(v_f_945_);
v___x_953_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_945_, v___x_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; size_t v___x_955_; size_t v___x_956_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_947_, v___x_955_);
v_i_947_ = v___x_956_;
v_b_949_ = v_a_954_;
goto _start;
}
else
{
lean_dec_ref(v_f_945_);
return v___x_953_;
}
}
else
{
lean_object* v___x_958_; 
lean_dec_ref(v_f_945_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_949_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_959_, lean_object* v_as_960_, lean_object* v_i_961_, lean_object* v_stop_962_, lean_object* v_b_963_, lean_object* v___y_964_){
_start:
{
size_t v_i_boxed_965_; size_t v_stop_boxed_966_; lean_object* v_res_967_; 
v_i_boxed_965_ = lean_unbox_usize(v_i_961_);
lean_dec(v_i_961_);
v_stop_boxed_966_ = lean_unbox_usize(v_stop_962_);
lean_dec(v_stop_962_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_959_, v_as_960_, v_i_boxed_965_, v_stop_boxed_966_, v_b_963_);
lean_dec_ref(v_as_960_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_968_, lean_object* v_x_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_968_, v_x_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_972_, lean_object* v_t_973_){
_start:
{
lean_object* v_root_975_; lean_object* v_tail_976_; lean_object* v___x_977_; 
v_root_975_ = lean_ctor_get(v_t_973_, 0);
lean_inc_ref(v_root_975_);
v_tail_976_ = lean_ctor_get(v_t_973_, 1);
lean_inc_ref(v_tail_976_);
lean_dec_ref(v_t_973_);
lean_inc_ref(v_f_972_);
v___x_977_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_972_, v_root_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_998_; 
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_999_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_998_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_998_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_tail_976_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_984_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_tail_976_);
lean_dec_ref(v_f_972_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_983_);
v___x_986_ = v___x_979_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_983_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_le(v___x_982_, v___x_982_);
if (v___x_988_ == 0)
{
if (v___x_984_ == 0)
{
lean_object* v___x_990_; 
lean_dec_ref(v_tail_976_);
lean_dec_ref(v_f_972_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_983_);
v___x_990_ = v___x_979_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_983_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
lean_del_object(v___x_979_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = lean_usize_of_nat(v___x_982_);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_972_, v_tail_976_, v___x_992_, v___x_993_, v___x_983_);
lean_dec_ref(v_tail_976_);
return v___x_994_;
}
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
lean_del_object(v___x_979_);
v___x_995_ = ((size_t)0ULL);
v___x_996_ = lean_usize_of_nat(v___x_982_);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_972_, v_tail_976_, v___x_995_, v___x_996_, v___x_983_);
lean_dec_ref(v_tail_976_);
return v___x_997_;
}
}
}
}
else
{
lean_dec_ref(v_tail_976_);
lean_dec_ref(v_f_972_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_1000_, lean_object* v_t_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1000_, v_t_1001_);
return v_res_1003_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_1005_, lean_object* v_x_1006_, size_t v_x_1007_, size_t v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_cs_1010_; lean_object* v___x_1011_; size_t v___x_1012_; lean_object* v_j_1013_; lean_object* v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v_cs_1010_ = lean_ctor_get(v_x_1006_, 0);
lean_inc_ref(v_cs_1010_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1011_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_1012_ = lean_usize_shift_right(v_x_1007_, v_x_1008_);
v_j_1013_ = lean_usize_to_nat(v___x_1012_);
v___x_1014_ = lean_array_get_borrowed(v___x_1011_, v_cs_1010_, v_j_1013_);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_shift_left(v___x_1015_, v_x_1008_);
v___x_1017_ = lean_usize_sub(v___x_1016_, v___x_1015_);
v___x_1018_ = lean_usize_land(v_x_1007_, v___x_1017_);
v___x_1019_ = ((size_t)5ULL);
v___x_1020_ = lean_usize_sub(v_x_1008_, v___x_1019_);
lean_inc(v___x_1014_);
lean_inc_ref(v_f_1005_);
v___x_1021_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1005_, v___x_1014_, v___x_1018_, v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1021_, 0);
lean_dec(v_unused_1044_);
v___x_1023_ = v___x_1021_;
v_isShared_1024_ = v_isSharedCheck_1043_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v___x_1021_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1043_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_j_1013_, v___x_1025_);
lean_dec(v_j_1013_);
v___x_1027_ = lean_array_get_size(v_cs_1010_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_nat_dec_lt(v___x_1026_, v___x_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v___x_1026_);
lean_dec_ref(v_cs_1010_);
lean_dec_ref(v_f_1005_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1028_);
v___x_1031_ = v___x_1023_;
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
lean_dec_ref(v_cs_1010_);
lean_dec_ref(v_f_1005_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1028_);
v___x_1035_ = v___x_1023_;
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
lean_del_object(v___x_1023_);
v___x_1037_ = lean_usize_of_nat(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1038_ = lean_usize_of_nat(v___x_1027_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1005_, v_cs_1010_, v___x_1037_, v___x_1038_, v___x_1028_);
lean_dec_ref(v_cs_1010_);
return v___x_1039_;
}
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
lean_del_object(v___x_1023_);
v___x_1040_ = lean_usize_of_nat(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1041_ = lean_usize_of_nat(v___x_1027_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1005_, v_cs_1010_, v___x_1040_, v___x_1041_, v___x_1028_);
lean_dec_ref(v_cs_1010_);
return v___x_1042_;
}
}
}
}
else
{
lean_dec(v_j_1013_);
lean_dec_ref(v_cs_1010_);
lean_dec_ref(v_f_1005_);
return v___x_1021_;
}
}
else
{
lean_object* v_vs_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1066_; 
v_vs_1045_ = lean_ctor_get(v_x_1006_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1047_ = v_x_1006_;
v_isShared_1048_ = v_isSharedCheck_1066_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_vs_1045_);
lean_dec(v_x_1006_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1066_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1049_ = lean_usize_to_nat(v_x_1007_);
v___x_1050_ = lean_array_get_size(v_vs_1045_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v___x_1049_);
lean_dec_ref(v_vs_1045_);
lean_dec_ref(v_f_1005_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1054_ = v___x_1047_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_le(v___x_1050_, v___x_1050_);
if (v___x_1056_ == 0)
{
if (v___x_1052_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v___x_1049_);
lean_dec_ref(v_vs_1045_);
lean_dec_ref(v_f_1005_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1058_ = v___x_1047_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1051_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
lean_del_object(v___x_1047_);
v___x_1060_ = lean_usize_of_nat(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1061_ = lean_usize_of_nat(v___x_1050_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1005_, v_vs_1045_, v___x_1060_, v___x_1061_, v___x_1051_);
lean_dec_ref(v_vs_1045_);
return v___x_1062_;
}
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1047_);
v___x_1063_ = lean_usize_of_nat(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1064_ = lean_usize_of_nat(v___x_1050_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1005_, v_vs_1045_, v___x_1063_, v___x_1064_, v___x_1051_);
lean_dec_ref(v_vs_1045_);
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
size_t v_x_1728__boxed_1072_; size_t v_x_1729__boxed_1073_; lean_object* v_res_1074_; 
v_x_1728__boxed_1072_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_x_1729__boxed_1073_ = lean_unbox_usize(v_x_1070_);
lean_dec(v_x_1070_);
v_res_1074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1067_, v_x_1068_, v_x_1728__boxed_1072_, v_x_1729__boxed_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1075_, lean_object* v_t_1076_, lean_object* v_start_1077_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_nat_dec_eq(v_start_1077_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v_root_1081_; lean_object* v_tail_1082_; size_t v_shift_1083_; lean_object* v_tailOff_1084_; uint8_t v___x_1085_; 
v_root_1081_ = lean_ctor_get(v_t_1076_, 0);
lean_inc_ref(v_root_1081_);
v_tail_1082_ = lean_ctor_get(v_t_1076_, 1);
lean_inc_ref(v_tail_1082_);
v_shift_1083_ = lean_ctor_get_usize(v_t_1076_, 4);
v_tailOff_1084_ = lean_ctor_get(v_t_1076_, 3);
lean_inc(v_tailOff_1084_);
lean_dec_ref(v_t_1076_);
v___x_1085_ = lean_nat_dec_le(v_tailOff_1084_, v_start_1077_);
if (v___x_1085_ == 0)
{
size_t v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_tailOff_1084_);
v___x_1086_ = lean_usize_of_nat(v_start_1077_);
lean_inc_ref(v_f_1075_);
v___x_1087_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1075_, v_root_1081_, v___x_1086_, v_shift_1083_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1108_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1091_ = lean_array_get_size(v_tail_1082_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_nat_dec_lt(v___x_1079_, v___x_1091_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v_tail_1082_);
lean_dec_ref(v_f_1075_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1095_ = v___x_1089_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_le(v___x_1091_, v___x_1091_);
if (v___x_1097_ == 0)
{
if (v___x_1093_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v_tail_1082_);
lean_dec_ref(v_f_1075_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1099_ = v___x_1089_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1092_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
lean_del_object(v___x_1089_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_of_nat(v___x_1091_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1075_, v_tail_1082_, v___x_1101_, v___x_1102_, v___x_1092_);
lean_dec_ref(v_tail_1082_);
return v___x_1103_;
}
}
else
{
size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
lean_del_object(v___x_1089_);
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = lean_usize_of_nat(v___x_1091_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1075_, v_tail_1082_, v___x_1104_, v___x_1105_, v___x_1092_);
lean_dec_ref(v_tail_1082_);
return v___x_1106_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1082_);
lean_dec_ref(v_f_1075_);
return v___x_1087_;
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
lean_dec_ref(v_root_1081_);
v___x_1109_ = lean_nat_sub(v_start_1077_, v_tailOff_1084_);
lean_dec(v_tailOff_1084_);
v___x_1110_ = lean_array_get_size(v_tail_1082_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_nat_dec_lt(v___x_1109_, v___x_1110_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec(v___x_1109_);
lean_dec_ref(v_tail_1082_);
lean_dec_ref(v_f_1075_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_le(v___x_1110_, v___x_1110_);
if (v___x_1114_ == 0)
{
if (v___x_1112_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v___x_1109_);
lean_dec_ref(v_tail_1082_);
lean_dec_ref(v_f_1075_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1111_);
return v___x_1115_;
}
else
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_usize_of_nat(v___x_1109_);
lean_dec(v___x_1109_);
v___x_1117_ = lean_usize_of_nat(v___x_1110_);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1075_, v_tail_1082_, v___x_1116_, v___x_1117_, v___x_1111_);
lean_dec_ref(v_tail_1082_);
return v___x_1118_;
}
}
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_usize_of_nat(v___x_1109_);
lean_dec(v___x_1109_);
v___x_1120_ = lean_usize_of_nat(v___x_1110_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1075_, v_tail_1082_, v___x_1119_, v___x_1120_, v___x_1111_);
lean_dec_ref(v_tail_1082_);
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1075_, v_t_1076_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1123_, lean_object* v_t_1124_, lean_object* v_start_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1123_, v_t_1124_, v_start_1125_);
lean_dec(v_start_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1128_, lean_object* v_f_1129_){
_start:
{
lean_object* v_unreported_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_unreported_1131_ = lean_ctor_get(v_log_1128_, 1);
lean_inc_ref(v_unreported_1131_);
lean_dec_ref(v_log_1128_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1129_, v_unreported_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1134_, lean_object* v_f_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1134_, v_f_1135_);
return v_res_1137_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1140_ = lean_mk_io_user_error(v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1141_, lean_object* v_inputCtx_1142_, lean_object* v_state_1143_, lean_object* v_msgs_1144_, lean_object* v_stxs_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; lean_object* v_fst_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; uint8_t v___x_1156_; 
v___x_1147_ = l_Lean_Options_empty;
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_box(0);
lean_inc_ref(v_env_1141_);
v___x_1150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1150_, 0, v_env_1141_);
lean_ctor_set(v___x_1150_, 1, v___x_1147_);
lean_ctor_set(v___x_1150_, 2, v___x_1148_);
lean_ctor_set(v___x_1150_, 3, v___x_1149_);
lean_inc_ref(v_inputCtx_1142_);
v___x_1151_ = l_Lean_Parser_parseCommand(v_inputCtx_1142_, v___x_1150_, v_state_1143_, v_msgs_1144_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
v_fst_1153_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_n(v_fst_1153_, 2);
lean_dec_ref(v___x_1151_);
v_fst_1154_ = lean_ctor_get(v_snd_1152_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v_snd_1152_, 1);
lean_inc(v_snd_1155_);
lean_dec(v_snd_1152_);
v___x_1156_ = l_Lean_Parser_isTerminalCommand(v_fst_1153_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_array_push(v_stxs_1145_, v_fst_1153_);
v_state_1143_ = v_fst_1154_;
v_msgs_1144_ = v_snd_1155_;
v_stxs_1145_ = v___x_1157_;
goto _start;
}
else
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
lean_dec(v_fst_1154_);
lean_dec_ref(v_inputCtx_1142_);
lean_dec_ref(v_env_1141_);
v___x_1159_ = l_Lean_MessageLog_hasUnreported(v_snd_1155_);
v___x_1160_ = lean_bool_not(v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; 
lean_dec(v_fst_1153_);
lean_dec_ref(v_stxs_1145_);
v___x_1161_ = lean_box(v___x_1160_);
v___f_1162_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1162_, 0, v___x_1161_);
v___x_1163_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1155_, v___f_1162_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v___x_1163_, 0);
lean_dec(v_unused_1172_);
v___x_1165_ = v___x_1163_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_dec(v___x_1163_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 1);
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1163_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1163_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_snd_1155_);
v___x_1181_ = lean_array_push(v_stxs_1145_, v_fst_1153_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1183_, lean_object* v_inputCtx_1184_, lean_object* v_state_1185_, lean_object* v_msgs_1186_, lean_object* v_stxs_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1183_, v_inputCtx_1184_, v_state_1185_, v_msgs_1186_, v_stxs_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1190_, lean_object* v_inputCtx_1191_, lean_object* v_s_1192_, lean_object* v_msgs_1193_, lean_object* v_stxs_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1190_, v_inputCtx_1191_, v_s_1192_, v_msgs_1193_, v_stxs_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1197_, lean_object* v_inputCtx_1198_, lean_object* v_s_1199_, lean_object* v_msgs_1200_, lean_object* v_stxs_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Parser_testParseModuleAux(v_env_1197_, v_inputCtx_1198_, v_s_1199_, v_msgs_1200_, v_stxs_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1212_, lean_object* v_fname_1213_, lean_object* v_contents_1214_){
_start:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v_inputCtx_1218_; lean_object* v___x_1219_; 
v___x_1216_ = 1;
v___x_1217_ = lean_string_utf8_byte_size(v_contents_1214_);
v_inputCtx_1218_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1214_, v_fname_1213_, v___x_1216_, v___x_1217_);
lean_inc_ref(v_inputCtx_1218_);
v___x_1219_ = l_Lean_Parser_parseHeader(v_inputCtx_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v_snd_1221_; lean_object* v_fst_1222_; lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v_snd_1221_ = lean_ctor_get(v_a_1220_, 1);
lean_inc(v_snd_1221_);
v_fst_1222_ = lean_ctor_get(v_a_1220_, 0);
lean_inc(v_fst_1222_);
lean_dec(v_a_1220_);
v_fst_1223_ = lean_ctor_get(v_snd_1221_, 0);
lean_inc(v_fst_1223_);
v_snd_1224_ = lean_ctor_get(v_snd_1221_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_snd_1221_);
v___x_1225_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1226_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1212_, v_inputCtx_1218_, v_fst_1223_, v_snd_1224_, v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1242_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1231_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1232_ = l_Lean_mkListNode(v_a_1227_);
v___x_1233_ = lean_unsigned_to_nat(2u);
v___x_1234_ = lean_mk_empty_array_with_capacity(v___x_1233_);
v___x_1235_ = lean_array_push(v___x_1234_, v_fst_1222_);
v___x_1236_ = lean_array_push(v___x_1235_, v___x_1232_);
v___x_1237_ = lean_box(2);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1231_);
lean_ctor_set(v___x_1238_, 2, v___x_1236_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1238_);
v___x_1240_ = v___x_1229_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_fst_1222_);
v_a_1243_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1226_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1226_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_inputCtx_1218_);
lean_dec_ref(v_env_1212_);
v_a_1251_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1219_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1219_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1259_, lean_object* v_fname_1260_, lean_object* v_contents_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Parser_testParseModule(v_env_1259_, v_fname_1260_, v_contents_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1264_, lean_object* v_fname_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_IO_FS_readFile(v_fname_1265_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_Lean_Parser_testParseModule(v_env_1264_, v_fname_1265_, v_a_1268_);
return v___x_1269_;
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_fname_1265_);
lean_dec_ref(v_env_1264_);
v_a_1270_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1267_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1267_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1278_, lean_object* v_fname_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Parser_testParseFile(v_env_1278_, v_fname_1279_);
return v_res_1281_;
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
