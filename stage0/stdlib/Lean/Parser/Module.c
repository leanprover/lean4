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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v___x_77_, 0, v___y_68_);
lean_ctor_set(v___x_77_, 1, v___y_66_);
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
v___y_66_ = v___x_84_;
v___y_67_ = v_e_81_;
v___y_68_ = v_fileName_82_;
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
v___y_66_ = v___x_84_;
v___y_67_ = v_e_81_;
v___y_68_ = v_fileName_82_;
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
lean_object* v_val_103_; lean_object* v_startPos_104_; lean_object* v_stopPos_105_; uint8_t v_decide_106_; 
v_val_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_102_, 1);
v_startPos_104_ = lean_ctor_get(v_val_103_, 1);
lean_inc(v_startPos_104_);
v_stopPos_105_ = lean_ctor_get(v_val_103_, 2);
lean_inc(v_stopPos_105_);
lean_dec(v_val_103_);
v_decide_106_ = lean_nat_dec_eq(v_stopPos_105_, v___y_99_);
lean_dec(v_stopPos_105_);
if (v_decide_106_ == 0)
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
v___x_166_ = 0;
return v___x_166_;
}
}
else
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v_val_169_; uint8_t v___x_170_; 
v_val_168_ = lean_ctor_get(v_x_163_, 0);
v_val_169_ = lean_ctor_get(v_x_164_, 0);
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
lean_dec(v_x_172_);
lean_dec(v_x_171_);
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
v___x_212_ = l_Lean_FileMap_toPosition(v___y_210_, v___y_211_);
lean_dec(v___y_211_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = 2;
v___x_215_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_216_, 0, v___y_208_);
lean_ctor_set(v___x_216_, 1, v___y_209_);
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
v___y_208_ = v_fileName_219_;
v___y_209_ = v___x_221_;
v___y_210_ = v_fileMap_220_;
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
v___y_208_ = v_fileName_219_;
v___y_209_ = v___x_221_;
v___y_210_ = v_fileMap_220_;
v___y_211_ = v_val_223_;
goto v___jp_207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_227_, lean_object* v_inputCtx_228_, lean_object* v_ref_229_, lean_object* v_msg_230_){
_start:
{
uint8_t v___x_3064__boxed_231_; lean_object* v_res_232_; 
v___x_3064__boxed_231_ = lean_unbox(v___x_227_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_3064__boxed_231_, v_inputCtx_228_, v_ref_229_, v_msg_230_);
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
lean_object* v___y_296_; lean_object* v_messages_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v_messages_305_; lean_object* v___y_311_; lean_object* v___y_312_; uint8_t v___y_313_; lean_object* v___y_314_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v_allTk_x3f_339_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v_metaTk_x3f_353_; lean_object* v_pubTk_x3f_365_; lean_object* v___x_375_; uint8_t v___x_376_; 
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
if (lean_obj_tag(v___y_304_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_val_306_ = lean_ctor_get(v___y_304_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___y_304_, 1);
v___x_307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_278_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_306_, v___x_307_);
lean_dec(v_val_306_);
v___x_309_ = l_Lean_MessageLog_add(v___x_308_, v_messages_305_);
v___y_296_ = v___y_303_;
v_messages_297_ = v___x_309_;
goto v___jp_295_;
}
else
{
lean_dec(v___y_304_);
v___y_296_ = v___y_303_;
v_messages_297_ = v_messages_305_;
goto v___jp_295_;
}
}
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 1)
{
if (lean_obj_tag(v___y_314_) == 0)
{
lean_dec_ref_known(v___y_311_, 1);
lean_dec(v___y_312_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_333_; 
v_isSharedCheck_333_ = !lean_is_exclusive(v___y_314_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___y_314_, 0);
lean_dec(v_unused_334_);
v___x_316_ = v___y_314_;
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___y_314_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
if (v___y_313_ == 0)
{
lean_del_object(v___x_316_);
lean_dec_ref_known(v___y_311_, 1);
lean_dec(v___y_312_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_val_318_ = lean_ctor_get(v___y_311_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___y_311_, 1);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_312_, v___y_313_);
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
lean_dec(v___y_312_);
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
lean_dec(v___y_337_);
v___y_311_ = v_allTk_x3f_339_;
v___y_312_ = v___x_345_;
v___y_313_ = v___x_342_;
v___y_314_ = v___y_338_;
goto v___jp_310_;
}
else
{
lean_dec(v___x_345_);
if (lean_obj_tag(v___y_338_) == 1)
{
lean_object* v_val_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_val_346_ = lean_ctor_get(v___y_338_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___y_338_, 1);
v___x_347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
lean_inc_ref(v_inputCtx_278_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_346_, v___x_347_);
lean_dec(v_val_346_);
v___x_349_ = l_Lean_MessageLog_add(v___x_348_, v_b_283_);
v___y_303_ = v_allTk_x3f_339_;
v___y_304_ = v___y_337_;
v_messages_305_ = v___x_349_;
goto v___jp_302_;
}
else
{
lean_dec(v___y_338_);
v___y_303_ = v_allTk_x3f_339_;
v___y_304_ = v___y_337_;
v_messages_305_ = v_b_283_;
goto v___jp_302_;
}
}
}
else
{
lean_dec(v___y_337_);
v___y_311_ = v_allTk_x3f_339_;
v___y_312_ = v___x_345_;
v___y_313_ = v___x_342_;
v___y_314_ = v___y_338_;
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
v___y_337_ = v_metaTk_x3f_353_;
v___y_338_ = v___y_352_;
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
v___y_337_ = v_metaTk_x3f_353_;
v___y_338_ = v___y_352_;
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
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_544_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_544_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_544_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_544_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v_fn_429_; lean_object* v_inputString_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_stxStack_441_; lean_object* v_pos_442_; lean_object* v_errorMsg_443_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; uint8_t v___y_448_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; uint8_t v___y_459_; lean_object* v___y_463_; lean_object* v_messages_464_; lean_object* v___y_475_; lean_object* v___y_476_; size_t v___y_477_; lean_object* v___y_478_; lean_object* v___x_493_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; size_t v___y_500_; lean_object* v_moduleTk_x3f_501_; lean_object* v___y_511_; uint8_t v___x_541_; 
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
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_541_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_441_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_441_);
lean_dec_ref(v_stxStack_441_);
v___y_511_ = v___x_542_;
goto v___jp_510_;
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_stxStack_441_);
v___x_543_ = lean_box(0);
v___y_511_ = v___x_543_;
goto v___jp_510_;
}
v___jp_444_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_449_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_449_, 0, v_pos_442_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*1, v___y_447_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*1 + 1, v___y_448_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___y_446_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_445_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_451_);
v___x_453_ = v___x_426_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
v___jp_455_:
{
if (v___y_458_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
v___y_445_ = v___y_456_;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___x_460_;
goto v___jp_444_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
v___y_445_ = v___y_456_;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___x_461_;
goto v___jp_444_;
}
}
v___jp_462_:
{
lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_465_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_463_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___x_465_);
v___x_468_ = lean_box(0);
v___x_469_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_443_, v___x_468_);
lean_dec(v_errorMsg_443_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 1;
v___x_471_ = lean_unbox(v_snd_467_);
lean_dec(v_snd_467_);
v___y_456_ = v_fst_466_;
v___y_457_ = v_messages_464_;
v___y_458_ = v___x_471_;
v___y_459_ = v___x_470_;
goto v___jp_455_;
}
else
{
uint8_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 0;
v___x_473_ = lean_unbox(v_snd_467_);
lean_dec(v_snd_467_);
v___y_456_ = v_fst_466_;
v___y_457_ = v_messages_464_;
v___y_458_ = v___x_473_;
v___y_459_ = v___x_472_;
goto v___jp_455_;
}
}
v___jp_474_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; size_t v_sz_482_; lean_object* v___x_483_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = l_Lean_Syntax_getArg(v___y_476_, v___x_479_);
v___x_481_ = l_Lean_Syntax_getArgs(v___x_480_);
lean_dec(v___x_480_);
v_sz_482_ = lean_array_size(v___x_481_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_420_, v___y_478_, v___x_481_, v_sz_482_, v___y_477_, v___y_475_);
lean_dec_ref(v___x_481_);
lean_dec(v___y_478_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___y_463_ = v___y_476_;
v_messages_464_ = v_a_484_;
goto v___jp_462_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v___y_476_);
lean_dec(v_errorMsg_443_);
lean_dec(v_pos_442_);
lean_del_object(v___x_426_);
v_a_485_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_483_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
v___jp_494_:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = l_Lean_Syntax_getArg(v___y_495_, v___x_502_);
v___x_504_ = l_Lean_Syntax_isNone(v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_inc(v___x_503_);
v___x_505_ = l_Lean_Syntax_matchesNull(v___x_503_, v___x_502_);
if (v___x_505_ == 0)
{
lean_dec(v___x_503_);
lean_dec(v_moduleTk_x3f_501_);
lean_dec_ref(v_inputCtx_420_);
v___y_463_ = v___y_495_;
v_messages_464_ = v___y_496_;
goto v___jp_462_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_506_ = l_Lean_Syntax_getArg(v___x_503_, v___x_493_);
lean_dec(v___x_503_);
v___x_507_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v___y_498_);
v___x_508_ = l_Lean_Name_mkStr4(v___y_498_, v___y_497_, v___y_499_, v___x_507_);
v___x_509_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_508_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v_moduleTk_x3f_501_);
lean_dec_ref(v_inputCtx_420_);
v___y_463_ = v___y_495_;
v_messages_464_ = v___y_496_;
goto v___jp_462_;
}
else
{
v___y_475_ = v___y_496_;
v___y_476_ = v___y_495_;
v___y_477_ = v___y_500_;
v___y_478_ = v_moduleTk_x3f_501_;
goto v___jp_474_;
}
}
}
else
{
lean_dec(v___x_503_);
v___y_475_ = v___y_496_;
v___y_476_ = v___y_495_;
v___y_477_ = v___y_500_;
v___y_478_ = v_moduleTk_x3f_501_;
goto v___jp_474_;
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_512_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_513_ = l_Lean_Parser_ParserState_allErrors(v___x_440_);
v_sz_514_ = lean_array_size(v___x_513_);
v___x_515_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_420_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_420_, v___x_513_, v_sz_514_, v___x_515_, v___x_512_);
lean_dec_ref(v___x_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_521_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_511_);
v___x_522_ = l_Lean_Syntax_isOfKind(v___y_511_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_inputCtx_420_);
v___y_463_ = v___y_511_;
v_messages_464_ = v_a_517_;
goto v___jp_462_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = l_Lean_Syntax_getArg(v___y_511_, v___x_493_);
v___x_524_ = l_Lean_Syntax_isNone(v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_523_);
v___x_526_ = l_Lean_Syntax_matchesNull(v___x_523_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v___x_523_);
lean_dec_ref(v_inputCtx_420_);
v___y_463_ = v___y_511_;
v_messages_464_ = v_a_517_;
goto v___jp_462_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = l_Lean_Syntax_getArg(v___x_523_, v___x_493_);
lean_dec(v___x_523_);
v___x_528_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_527_);
v___x_529_ = l_Lean_Syntax_isOfKind(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v___x_527_);
lean_dec_ref(v_inputCtx_420_);
v___y_463_ = v___y_511_;
v_messages_464_ = v_a_517_;
goto v___jp_462_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = l_Lean_Syntax_getArg(v___x_527_, v___x_493_);
lean_dec(v___x_527_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___y_495_ = v___y_511_;
v___y_496_ = v_a_517_;
v___y_497_ = v___x_519_;
v___y_498_ = v___x_518_;
v___y_499_ = v___x_520_;
v___y_500_ = v___x_515_;
v_moduleTk_x3f_501_ = v___x_531_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v___x_523_);
v___x_532_ = lean_box(0);
v___y_495_ = v___y_511_;
v___y_496_ = v_a_517_;
v___y_497_ = v___x_519_;
v___y_498_ = v___x_518_;
v___y_499_ = v___x_520_;
v___y_500_ = v___x_515_;
v_moduleTk_x3f_501_ = v___x_532_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v___y_511_);
lean_dec(v_errorMsg_443_);
lean_dec(v_pos_442_);
lean_del_object(v___x_426_);
lean_dec_ref(v_inputCtx_420_);
v_a_533_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_516_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_516_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_inputCtx_420_);
v_a_545_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_423_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_423_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Parser_parseHeader(v_inputCtx_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_563_, lean_object* v_pos_564_){
_start:
{
lean_object* v___y_566_; lean_object* v_inputString_576_; lean_object* v_endPos_577_; uint8_t v___x_578_; 
v_inputString_576_ = lean_ctor_get(v_inputCtx_563_, 0);
v_endPos_577_ = lean_ctor_get(v_inputCtx_563_, 3);
v___x_578_ = lean_nat_dec_le(v_pos_564_, v_endPos_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_inc(v_endPos_577_);
lean_inc(v_pos_564_);
lean_inc_ref(v_inputString_576_);
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v_inputString_576_);
lean_ctor_set(v___x_579_, 1, v_pos_564_);
lean_ctor_set(v___x_579_, 2, v_endPos_577_);
v___y_566_ = v___x_579_;
goto v___jp_565_;
}
else
{
lean_object* v___x_580_; 
lean_inc_n(v_pos_564_, 2);
lean_inc_ref(v_inputString_576_);
v___x_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_580_, 0, v_inputString_576_);
lean_ctor_set(v___x_580_, 1, v_pos_564_);
lean_ctor_set(v___x_580_, 2, v_pos_564_);
v___y_566_ = v___x_580_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_atom_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_inc(v_pos_564_);
lean_inc_ref(v___y_566_);
v___x_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_567_, 0, v___y_566_);
lean_ctor_set(v___x_567_, 1, v_pos_564_);
lean_ctor_set(v___x_567_, 2, v___y_566_);
lean_ctor_set(v___x_567_, 3, v_pos_564_);
v___x_568_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_569_, 0, v___x_567_);
lean_ctor_set(v_atom_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
v___x_573_ = lean_array_push(v___x_572_, v_atom_569_);
v___x_574_ = lean_box(2);
v___x_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_570_);
lean_ctor_set(v___x_575_, 2, v___x_573_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_581_, lean_object* v_pos_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_581_, v_pos_582_);
lean_dec_ref(v_inputCtx_581_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_595_){
_start:
{
uint8_t v___y_597_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_595_);
v___x_601_ = l_Lean_Syntax_isOfKind(v_s_595_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_595_);
v___x_603_ = l_Lean_Syntax_isOfKind(v_s_595_, v___x_602_);
v___y_597_ = v___x_603_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_601_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_599_ = l_Lean_Syntax_isOfKind(v_s_595_, v___x_598_);
return v___x_599_;
}
else
{
lean_dec(v_s_595_);
return v___y_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* v_s_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lean_Parser_isTerminalCommand(v_s_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2(void){
_start:
{
uint32_t v___x_611_; lean_object* v___x_612_; 
v___x_611_ = 32;
v___x_612_ = l_Char_utf8Size(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_613_, lean_object* v_pmctx_614_, lean_object* v_pos_615_){
_start:
{
lean_object* v_inputString_616_; lean_object* v_env_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_s_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_s_626_; lean_object* v_errorMsg_627_; 
v_inputString_616_ = lean_ctor_get(v_inputCtx_613_, 0);
v_env_617_ = lean_ctor_get(v_pmctx_614_, 0);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_620_ = l_Lean_Parser_SyntaxStack_empty;
v___x_621_ = l_Lean_Parser_initCacheForInput(v_inputString_616_);
v___x_622_ = lean_box(0);
lean_inc(v_pos_615_);
v_s_623_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_623_, 0, v___x_620_);
lean_ctor_set(v_s_623_, 1, v___x_618_);
lean_ctor_set(v_s_623_, 2, v_pos_615_);
lean_ctor_set(v_s_623_, 3, v___x_621_);
lean_ctor_set(v_s_623_, 4, v___x_622_);
lean_ctor_set(v_s_623_, 5, v___x_619_);
v___x_624_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_617_);
v___x_625_ = l_Lean_Parser_getTokenTable(v_env_617_);
v_s_626_ = l_Lean_Parser_ParserFn_run(v___x_624_, v_inputCtx_613_, v_pmctx_614_, v___x_625_, v_s_623_);
v_errorMsg_627_ = lean_ctor_get(v_s_626_, 4);
lean_inc(v_errorMsg_627_);
if (lean_obj_tag(v_errorMsg_627_) == 0)
{
lean_object* v_pos_628_; 
lean_dec(v_pos_615_);
v_pos_628_ = lean_ctor_get(v_s_626_, 2);
lean_inc(v_pos_628_);
lean_dec_ref(v_s_626_);
return v_pos_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref_known(v_errorMsg_627_, 1);
lean_dec_ref(v_s_626_);
v___x_629_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2);
v___x_630_ = lean_nat_add(v_pos_615_, v___x_629_);
lean_dec(v_pos_615_);
return v___x_630_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_636_ = l_Lean_Parser_categoryParser(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_638_ = l_Lean_Parser_withPosition(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; lean_object* v_fn_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc_ref(v_fn_642_);
v___x_643_ = lean_apply_2(v_fn_642_, v_a_639_, v_a_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_644_, lean_object* v_as_645_, size_t v_sz_646_, size_t v_i_647_, lean_object* v_b_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = lean_usize_dec_lt(v_i_647_, v_sz_646_);
if (v___x_649_ == 0)
{
lean_dec_ref(v_inputCtx_644_);
return v_b_648_;
}
else
{
lean_object* v_a_650_; lean_object* v_snd_651_; lean_object* v_fst_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; 
v_a_650_ = lean_array_uget_borrowed(v_as_645_, v_i_647_);
v_snd_651_ = lean_ctor_get(v_a_650_, 1);
v_fst_652_ = lean_ctor_get(v_a_650_, 0);
v_fst_653_ = lean_ctor_get(v_snd_651_, 0);
v_snd_654_ = lean_ctor_get(v_snd_651_, 1);
lean_inc(v_snd_654_);
lean_inc(v_fst_653_);
lean_inc(v_fst_652_);
lean_inc_ref(v_inputCtx_644_);
v___x_655_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_644_, v_fst_652_, v_fst_653_, v_snd_654_);
v___x_656_ = l_Lean_MessageLog_add(v___x_655_, v_b_648_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_add(v_i_647_, v___x_657_);
v_i_647_ = v___x_658_;
v_b_648_ = v___x_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_660_, lean_object* v_as_661_, lean_object* v_sz_662_, lean_object* v_i_663_, lean_object* v_b_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_662_);
lean_dec(v_sz_662_);
v_i_boxed_666_ = lean_unbox_usize(v_i_663_);
lean_dec(v_i_663_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_660_, v_as_661_, v_sz_boxed_665_, v_i_boxed_666_, v_b_664_);
lean_dec_ref(v_as_661_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_stxStack_668_, uint8_t v___x_669_, lean_object* v_snd_670_, lean_object* v_inputCtx_671_, lean_object* v_pos_672_, lean_object* v_val_673_, lean_object* v___x_674_, lean_object* v_fst_675_, uint8_t v___x_676_, uint8_t v___y_677_, lean_object* v_____r_678_, lean_object* v_pos_679_){
_start:
{
uint8_t v___y_681_; lean_object* v_messages_682_; uint8_t v___y_695_; uint8_t v___y_696_; uint8_t v___y_700_; uint8_t v___x_702_; 
v___x_702_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_668_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_668_);
v___x_704_ = l_Lean_Syntax_getPos_x3f(v___x_703_, v___y_677_);
lean_dec(v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
v___y_700_ = v___x_669_;
goto v___jp_699_;
}
else
{
lean_dec_ref_known(v___x_704_, 1);
v___y_700_ = v___y_677_;
goto v___jp_699_;
}
}
else
{
v___y_700_ = v___x_669_;
goto v___jp_699_;
}
v___jp_680_:
{
if (v___y_681_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_snd_670_);
v___x_683_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_668_);
lean_dec_ref(v_stxStack_668_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_messages_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_box(v___x_669_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_pos_679_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_stxStack_668_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_messages_682_);
lean_ctor_set(v___x_689_, 1, v_snd_670_);
v___x_690_ = lean_box(v___x_669_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_pos_679_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
v___jp_694_:
{
if (v___y_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc_ref(v_stxStack_668_);
v___x_697_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_671_, v_pos_672_, v_stxStack_668_, v_val_673_);
v___x_698_ = l_Lean_MessageLog_add(v___x_697_, v___x_674_);
v___y_681_ = v___y_695_;
v_messages_682_ = v___x_698_;
goto v___jp_680_;
}
else
{
lean_dec_ref(v_val_673_);
lean_dec(v_pos_672_);
lean_dec_ref(v_inputCtx_671_);
v___y_681_ = v___y_695_;
v_messages_682_ = v___x_674_;
goto v___jp_680_;
}
}
v___jp_699_:
{
uint8_t v___x_701_; 
v___x_701_ = lean_unbox(v_fst_675_);
if (v___x_701_ == 0)
{
v___y_695_ = v___y_700_;
v___y_696_ = v___x_676_;
goto v___jp_694_;
}
else
{
v___y_695_ = v___y_700_;
v___y_696_ = v___y_700_;
goto v___jp_694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_stxStack_705_, lean_object* v___x_706_, lean_object* v_snd_707_, lean_object* v_inputCtx_708_, lean_object* v_pos_709_, lean_object* v_val_710_, lean_object* v___x_711_, lean_object* v_fst_712_, lean_object* v___x_713_, lean_object* v___y_714_, lean_object* v_____r_715_, lean_object* v_pos_716_){
_start:
{
uint8_t v___x_1762__boxed_717_; uint8_t v___x_1765__boxed_718_; uint8_t v___y_1766__boxed_719_; lean_object* v_res_720_; 
v___x_1762__boxed_717_ = lean_unbox(v___x_706_);
v___x_1765__boxed_718_ = lean_unbox(v___x_713_);
v___y_1766__boxed_719_ = lean_unbox(v___y_714_);
v_res_720_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_705_, v___x_1762__boxed_717_, v_snd_707_, v_inputCtx_708_, v_pos_709_, v_val_710_, v___x_711_, v_fst_712_, v___x_1765__boxed_718_, v___y_1766__boxed_719_, v_____r_715_, v_pos_716_);
lean_dec(v_fst_712_);
return v_res_720_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_722_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_723_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_723_, 0, v___x_722_);
lean_closure_set(v___x_723_, 1, v___x_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_724_, lean_object* v_pmctx_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___y_728_; lean_object* v_snd_732_; lean_object* v_snd_733_; lean_object* v_fst_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_817_; 
v_snd_732_ = lean_ctor_get(v_a_726_, 1);
lean_inc(v_snd_732_);
v_snd_733_ = lean_ctor_get(v_snd_732_, 1);
lean_inc(v_snd_733_);
v_fst_734_ = lean_ctor_get(v_a_726_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_a_726_, 1);
lean_dec(v_unused_818_);
v___x_736_ = v_a_726_;
v_isShared_737_ = v_isSharedCheck_817_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_fst_734_);
lean_dec(v_a_726_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_817_;
goto v_resetjp_735_;
}
v___jp_727_:
{
if (lean_obj_tag(v___y_728_) == 0)
{
lean_object* v_a_729_; 
lean_dec_ref(v_pmctx_725_);
lean_dec_ref(v_inputCtx_724_);
v_a_729_ = lean_ctor_get(v___y_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___y_728_, 1);
return v_a_729_;
}
else
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___y_728_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___y_728_, 1);
v_a_726_ = v_a_730_;
goto _start;
}
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_815_; 
v_fst_738_ = lean_ctor_get(v_snd_732_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_snd_732_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_snd_732_, 1);
lean_dec(v_unused_816_);
v___x_740_ = v_snd_732_;
v_isShared_741_ = v_isSharedCheck_815_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_fst_738_);
lean_dec(v_snd_732_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_815_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_814_; 
v_fst_742_ = lean_ctor_get(v_snd_733_, 0);
v_snd_743_ = lean_ctor_get(v_snd_733_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_733_);
if (v_isSharedCheck_814_ == 0)
{
v___x_745_ = v_snd_733_;
v_isShared_746_ = v_isSharedCheck_814_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_inc(v_fst_742_);
lean_dec(v_snd_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_814_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_724_, v_fst_734_);
if (v___x_747_ == 0)
{
lean_object* v_env_748_; lean_object* v_inputString_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_stxStack_759_; lean_object* v_pos_760_; lean_object* v_errorMsg_761_; lean_object* v_recoveredErrors_762_; uint8_t v___x_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; uint8_t v___y_768_; uint8_t v___y_801_; uint8_t v___x_802_; 
v_env_748_ = lean_ctor_get(v_pmctx_725_, 0);
v_inputString_749_ = lean_ctor_get(v_inputCtx_724_, 0);
v___x_750_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_748_);
v___x_751_ = l_Lean_Parser_getTokenTable(v_env_748_);
v___x_752_ = l_Lean_Parser_SyntaxStack_empty;
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = l_Lean_Parser_initCacheForInput(v_inputString_749_);
v___x_755_ = lean_box(0);
v___x_756_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_734_);
v___x_757_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_757_, 0, v___x_752_);
lean_ctor_set(v___x_757_, 1, v___x_753_);
lean_ctor_set(v___x_757_, 2, v_fst_734_);
lean_ctor_set(v___x_757_, 3, v___x_754_);
lean_ctor_set(v___x_757_, 4, v___x_755_);
lean_ctor_set(v___x_757_, 5, v___x_756_);
lean_inc_ref(v_pmctx_725_);
lean_inc_ref_n(v_inputCtx_724_, 2);
v___x_758_ = l_Lean_Parser_ParserFn_run(v___x_750_, v_inputCtx_724_, v_pmctx_725_, v___x_751_, v___x_757_);
v_stxStack_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_stxStack_759_);
v_pos_760_ = lean_ctor_get(v___x_758_, 2);
lean_inc(v_pos_760_);
v_errorMsg_761_ = lean_ctor_get(v___x_758_, 4);
lean_inc(v_errorMsg_761_);
v_recoveredErrors_762_ = lean_ctor_get(v___x_758_, 5);
lean_inc_ref(v_recoveredErrors_762_);
lean_dec_ref(v___x_758_);
v___x_763_ = 1;
v_sz_764_ = lean_array_size(v_recoveredErrors_762_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_724_, v_recoveredErrors_762_, v_sz_764_, v___x_765_, v_fst_742_);
lean_dec_ref(v_recoveredErrors_762_);
v___x_802_ = lean_unbox(v_fst_738_);
if (v___x_802_ == 0)
{
v___y_801_ = v___x_747_;
goto v___jp_800_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_759_);
if (v___x_803_ == 0)
{
goto v___jp_797_;
}
else
{
v___y_801_ = v___x_747_;
goto v___jp_800_;
}
}
v___jp_767_:
{
if (v___y_768_ == 0)
{
if (lean_obj_tag(v_errorMsg_761_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_snd_743_);
lean_dec(v_fst_738_);
lean_dec(v_fst_734_);
lean_dec_ref(v_pmctx_725_);
lean_dec_ref(v_inputCtx_724_);
v___x_769_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_759_);
lean_dec_ref(v_stxStack_759_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_769_);
lean_ctor_set(v___x_745_, 0, v___x_766_);
v___x_771_ = v___x_745_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_779_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_box(v___y_768_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_771_);
lean_ctor_set(v___x_740_, 0, v___x_772_);
v___x_774_ = v___x_740_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_771_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_774_);
lean_ctor_set(v___x_736_, 0, v_pos_760_);
v___x_776_ = v___x_736_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_pos_760_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_val_780_; uint8_t v_decide_781_; 
lean_del_object(v___x_745_);
lean_del_object(v___x_740_);
lean_del_object(v___x_736_);
v_val_780_ = lean_ctor_get(v_errorMsg_761_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_errorMsg_761_, 1);
v_decide_781_ = lean_nat_dec_eq(v_pos_760_, v_fst_734_);
lean_dec(v_fst_734_);
if (v_decide_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_box(0);
lean_inc(v_pos_760_);
lean_inc_ref(v_inputCtx_724_);
v___x_783_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_759_, v___x_763_, v_snd_743_, v_inputCtx_724_, v_pos_760_, v_val_780_, v___x_766_, v_fst_738_, v___x_747_, v___y_768_, v___x_782_, v_pos_760_);
lean_dec(v_fst_738_);
v___y_728_ = v___x_783_;
goto v___jp_727_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_inc(v_pos_760_);
lean_inc_ref(v_pmctx_725_);
lean_inc_ref_n(v_inputCtx_724_, 2);
v___x_784_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_724_, v_pmctx_725_, v_pos_760_);
v___x_785_ = lean_box(0);
v___x_786_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_759_, v___x_763_, v_snd_743_, v_inputCtx_724_, v_pos_760_, v_val_780_, v___x_766_, v_fst_738_, v___x_747_, v___y_768_, v___x_785_, v___x_784_);
lean_dec(v_fst_738_);
v___y_728_ = v___x_786_;
goto v___jp_727_;
}
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_errorMsg_761_);
lean_dec_ref(v_stxStack_759_);
lean_dec(v_fst_734_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_766_);
v___x_788_ = v___x_745_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_snd_743_);
v___x_788_ = v_reuseFailAlloc_796_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_788_);
v___x_790_ = v___x_740_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_738_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_790_);
lean_ctor_set(v___x_736_, 0, v_pos_760_);
v___x_792_ = v___x_736_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_pos_760_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_a_726_ = v___x_792_;
goto _start;
}
}
}
}
}
v___jp_797_:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_759_);
v___x_799_ = l_Lean_Syntax_isAntiquot(v___x_798_);
lean_dec(v___x_798_);
v___y_768_ = v___x_799_;
goto v___jp_767_;
}
v___jp_800_:
{
if (v___y_801_ == 0)
{
v___y_768_ = v___x_747_;
goto v___jp_767_;
}
else
{
goto v___jp_797_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v_snd_743_);
lean_dec_ref(v_pmctx_725_);
lean_inc(v_fst_734_);
v___x_804_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_724_, v_fst_734_);
lean_dec_ref(v_inputCtx_724_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_804_);
v___x_806_ = v___x_745_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_742_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_813_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_806_);
v___x_808_ = v___x_740_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_fst_738_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_808_);
v___x_810_ = v___x_736_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_734_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_819_, lean_object* v_pmctx_820_, lean_object* v_mps_821_, lean_object* v_messages_822_){
_start:
{
lean_object* v_pos_823_; uint8_t v_recovering_824_; uint8_t v_hasLeading_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_865_; 
v_pos_823_ = lean_ctor_get(v_mps_821_, 0);
v_recovering_824_ = lean_ctor_get_uint8(v_mps_821_, sizeof(void*)*1);
v_hasLeading_825_ = lean_ctor_get_uint8(v_mps_821_, sizeof(void*)*1 + 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_mps_821_);
if (v_isSharedCheck_865_ == 0)
{
v___x_827_ = v_mps_821_;
v_isShared_828_ = v_isSharedCheck_865_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_pos_823_);
lean_dec(v_mps_821_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_865_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_stx_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_snd_835_; lean_object* v_snd_836_; lean_object* v_fst_837_; lean_object* v_fst_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_863_; 
v_stx_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_messages_822_);
lean_ctor_set(v___x_830_, 1, v_stx_829_);
v___x_831_ = lean_box(v_recovering_824_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_pos_823_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_819_, v_pmctx_820_, v___x_833_);
v_snd_835_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_snd_835_);
v_snd_836_ = lean_ctor_get(v_snd_835_, 1);
lean_inc(v_snd_836_);
v_fst_837_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_fst_837_);
lean_dec_ref(v___x_834_);
v_fst_838_ = lean_ctor_get(v_snd_835_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_snd_835_, 1);
lean_dec(v_unused_864_);
v___x_840_ = v_snd_835_;
v_isShared_841_ = v_isSharedCheck_863_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_fst_838_);
lean_dec(v_snd_835_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_863_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_fst_842_; lean_object* v_snd_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_862_; 
v_fst_842_ = lean_ctor_get(v_snd_836_, 0);
v_snd_843_ = lean_ctor_get(v_snd_836_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_snd_836_);
if (v_isSharedCheck_862_ == 0)
{
v___x_845_ = v_snd_836_;
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_snd_843_);
lean_inc(v_fst_842_);
lean_dec(v_snd_836_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_862_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_stx_848_; 
if (v_hasLeading_825_ == 0)
{
v_stx_848_ = v_snd_843_;
goto v___jp_847_;
}
else
{
lean_object* v___x_860_; lean_object* v_fst_861_; 
v___x_860_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_843_);
v_fst_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_861_);
lean_dec_ref(v___x_860_);
v_stx_848_ = v_fst_861_;
goto v___jp_847_;
}
v___jp_847_:
{
uint8_t v___x_849_; lean_object* v___x_851_; 
v___x_849_ = 0;
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v_fst_837_);
v___x_851_ = v___x_827_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_837_);
v___x_851_ = v_reuseFailAlloc_859_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
uint8_t v___x_852_; lean_object* v___x_854_; 
v___x_852_ = lean_unbox(v_fst_838_);
lean_dec(v_fst_838_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*1, v___x_852_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*1 + 1, v___x_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_fst_842_);
lean_ctor_set(v___x_845_, 0, v___x_851_);
v___x_854_ = v___x_845_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_fst_842_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_854_);
lean_ctor_set(v___x_840_, 0, v_stx_848_);
v___x_856_ = v___x_840_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_stx_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_866_, lean_object* v_pmctx_867_, lean_object* v_inst_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_866_, v_pmctx_867_, v_a_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_871_){
_start:
{
lean_object* v___x_873_; lean_object* v_putStr_874_; lean_object* v___x_875_; 
v___x_873_ = lean_get_stdout();
v_putStr_874_ = lean_ctor_get(v___x_873_, 4);
lean_inc_ref(v_putStr_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = lean_apply_2(v_putStr_874_, v_s_871_, lean_box(0));
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_879_){
_start:
{
uint32_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = 10;
v___x_882_ = lean_string_push(v_s_879_, v___x_881_);
v___x_883_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_887_, lean_object* v_msg_888_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Lean_Message_toString(v_msg_888_, v___y_887_);
v___x_891_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_892_, lean_object* v_msg_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___y_1211__boxed_895_; lean_object* v_res_896_; 
v___y_1211__boxed_895_ = lean_unbox(v___y_892_);
v_res_896_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_1211__boxed_895_, v_msg_893_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_897_, lean_object* v_as_898_, size_t v_i_899_, size_t v_stop_900_, lean_object* v_b_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_eq(v_i_899_, v_stop_900_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_array_uget_borrowed(v_as_898_, v_i_899_);
lean_inc_ref(v_f_897_);
lean_inc(v___x_904_);
v___x_905_ = lean_apply_2(v_f_897_, v___x_904_, lean_box(0));
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; size_t v___x_907_; size_t v___x_908_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_899_, v___x_907_);
v_i_899_ = v___x_908_;
v_b_901_ = v_a_906_;
goto _start;
}
else
{
lean_dec_ref(v_f_897_);
return v___x_905_;
}
}
else
{
lean_object* v___x_910_; 
lean_dec_ref(v_f_897_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v_b_901_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_911_, lean_object* v_as_912_, lean_object* v_i_913_, lean_object* v_stop_914_, lean_object* v_b_915_, lean_object* v___y_916_){
_start:
{
size_t v_i_boxed_917_; size_t v_stop_boxed_918_; lean_object* v_res_919_; 
v_i_boxed_917_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_stop_boxed_918_ = lean_unbox_usize(v_stop_914_);
lean_dec(v_stop_914_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_911_, v_as_912_, v_i_boxed_917_, v_stop_boxed_918_, v_b_915_);
lean_dec_ref(v_as_912_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_cs_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_937_; 
v_cs_923_ = lean_ctor_get(v_x_921_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_937_ == 0)
{
v___x_925_ = v_x_921_;
v_isShared_926_ = v_isSharedCheck_937_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_cs_923_);
lean_dec(v_x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_937_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v_cs_923_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_930_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v_cs_923_);
lean_dec_ref(v_f_920_);
if (v_isShared_926_ == 0)
{
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
size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_925_);
v___x_934_ = ((size_t)0ULL);
v___x_935_ = lean_usize_of_nat(v___x_928_);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_920_, v_cs_923_, v___x_934_, v___x_935_, v___x_929_);
lean_dec_ref(v_cs_923_);
return v___x_936_;
}
}
}
else
{
lean_object* v_vs_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_vs_938_ = lean_ctor_get(v_x_921_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_952_ == 0)
{
v___x_940_ = v_x_921_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_vs_938_);
lean_dec(v_x_921_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_array_get_size(v_vs_938_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
if (v___x_945_ == 0)
{
lean_object* v___x_947_; 
lean_dec_ref(v_vs_938_);
lean_dec_ref(v_f_920_);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 0);
lean_ctor_set(v___x_940_, 0, v___x_944_);
v___x_947_ = v___x_940_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_944_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
lean_del_object(v___x_940_);
v___x_949_ = ((size_t)0ULL);
v___x_950_ = lean_usize_of_nat(v___x_943_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_920_, v_vs_938_, v___x_949_, v___x_950_, v___x_944_);
lean_dec_ref(v_vs_938_);
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_953_, lean_object* v_as_954_, size_t v_i_955_, size_t v_stop_956_, lean_object* v_b_957_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_usize_dec_eq(v_i_955_, v_stop_956_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_array_uget_borrowed(v_as_954_, v_i_955_);
lean_inc(v___x_960_);
lean_inc_ref(v_f_953_);
v___x_961_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_953_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; size_t v___x_963_; size_t v___x_964_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_955_, v___x_963_);
v_i_955_ = v___x_964_;
v_b_957_ = v_a_962_;
goto _start;
}
else
{
lean_dec_ref(v_f_953_);
return v___x_961_;
}
}
else
{
lean_object* v___x_966_; 
lean_dec_ref(v_f_953_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v_b_957_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_967_, lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_, lean_object* v___y_972_){
_start:
{
size_t v_i_boxed_973_; size_t v_stop_boxed_974_; lean_object* v_res_975_; 
v_i_boxed_973_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_974_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_967_, v_as_968_, v_i_boxed_973_, v_stop_boxed_974_, v_b_971_);
lean_dec_ref(v_as_968_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_976_, lean_object* v_x_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_976_, v_x_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_980_, lean_object* v_t_981_){
_start:
{
lean_object* v_root_983_; lean_object* v_tail_984_; lean_object* v___x_985_; 
v_root_983_ = lean_ctor_get(v_t_981_, 0);
lean_inc_ref(v_root_983_);
v_tail_984_ = lean_ctor_get(v_t_981_, 1);
lean_inc_ref(v_tail_984_);
lean_dec_ref(v_t_981_);
lean_inc_ref(v_f_980_);
v___x_985_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_980_, v_root_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_999_; 
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_1000_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get_size(v_tail_984_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_994_; 
lean_dec_ref(v_tail_984_);
lean_dec_ref(v_f_980_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_991_);
v___x_994_ = v___x_987_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_987_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_990_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_980_, v_tail_984_, v___x_996_, v___x_997_, v___x_991_);
lean_dec_ref(v_tail_984_);
return v___x_998_;
}
}
}
else
{
lean_dec_ref(v_tail_984_);
lean_dec_ref(v_f_980_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_1001_, lean_object* v_t_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1001_, v_t_1002_);
return v_res_1004_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_1006_, lean_object* v_x_1007_, size_t v_x_1008_, size_t v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v_cs_1011_; lean_object* v___x_1012_; size_t v___x_1013_; lean_object* v_j_1014_; lean_object* v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v_cs_1011_ = lean_ctor_get(v_x_1007_, 0);
lean_inc_ref(v_cs_1011_);
lean_dec_ref_known(v_x_1007_, 1);
v___x_1012_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_1013_ = lean_usize_shift_right(v_x_1008_, v_x_1009_);
v_j_1014_ = lean_usize_to_nat(v___x_1013_);
v___x_1015_ = lean_array_get_borrowed(v___x_1012_, v_cs_1011_, v_j_1014_);
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_shift_left(v___x_1016_, v_x_1009_);
v___x_1018_ = lean_usize_sub(v___x_1017_, v___x_1016_);
v___x_1019_ = lean_usize_land(v_x_1008_, v___x_1018_);
v___x_1020_ = ((size_t)5ULL);
v___x_1021_ = lean_usize_sub(v_x_1009_, v___x_1020_);
lean_inc(v___x_1015_);
lean_inc_ref(v_f_1006_);
v___x_1022_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1006_, v___x_1015_, v___x_1019_, v___x_1021_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1037_; 
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1038_);
v___x_1024_ = v___x_1022_;
v_isShared_1025_ = v_isSharedCheck_1037_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v___x_1022_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1037_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_j_1014_, v___x_1026_);
lean_dec(v_j_1014_);
v___x_1028_ = lean_array_get_size(v_cs_1011_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1032_; 
lean_dec(v___x_1027_);
lean_dec_ref(v_cs_1011_);
lean_dec_ref(v_f_1006_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1029_);
v___x_1032_ = v___x_1024_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1029_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
lean_del_object(v___x_1024_);
v___x_1034_ = lean_usize_of_nat(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1035_ = lean_usize_of_nat(v___x_1028_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1006_, v_cs_1011_, v___x_1034_, v___x_1035_, v___x_1029_);
lean_dec_ref(v_cs_1011_);
return v___x_1036_;
}
}
}
else
{
lean_dec(v_j_1014_);
lean_dec_ref(v_cs_1011_);
lean_dec_ref(v_f_1006_);
return v___x_1022_;
}
}
else
{
lean_object* v_vs_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1053_; 
v_vs_1039_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1041_ = v_x_1007_;
v_isShared_1042_ = v_isSharedCheck_1053_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_vs_1039_);
lean_dec(v_x_1007_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1053_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1043_ = lean_usize_to_nat(v_x_1008_);
v___x_1044_ = lean_array_get_size(v_vs_1039_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_nat_dec_lt(v___x_1043_, v___x_1044_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1048_; 
lean_dec(v___x_1043_);
lean_dec_ref(v_vs_1039_);
lean_dec_ref(v_f_1006_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1045_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1045_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
lean_del_object(v___x_1041_);
v___x_1050_ = lean_usize_of_nat(v___x_1043_);
lean_dec(v___x_1043_);
v___x_1051_ = lean_usize_of_nat(v___x_1044_);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1006_, v_vs_1039_, v___x_1050_, v___x_1051_, v___x_1045_);
lean_dec_ref(v_vs_1039_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_x_1367__boxed_1059_; size_t v_x_1368__boxed_1060_; lean_object* v_res_1061_; 
v_x_1367__boxed_1059_ = lean_unbox_usize(v_x_1056_);
lean_dec(v_x_1056_);
v_x_1368__boxed_1060_ = lean_unbox_usize(v_x_1057_);
lean_dec(v_x_1057_);
v_res_1061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1054_, v_x_1055_, v_x_1367__boxed_1059_, v_x_1368__boxed_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1062_, lean_object* v_t_1063_, lean_object* v_start_1064_){
_start:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_nat_dec_eq(v_start_1064_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v_root_1068_; lean_object* v_tail_1069_; size_t v_shift_1070_; lean_object* v_tailOff_1071_; uint8_t v___x_1072_; 
v_root_1068_ = lean_ctor_get(v_t_1063_, 0);
lean_inc_ref(v_root_1068_);
v_tail_1069_ = lean_ctor_get(v_t_1063_, 1);
lean_inc_ref(v_tail_1069_);
v_shift_1070_ = lean_ctor_get_usize(v_t_1063_, 4);
v_tailOff_1071_ = lean_ctor_get(v_t_1063_, 3);
lean_inc(v_tailOff_1071_);
lean_dec_ref(v_t_1063_);
v___x_1072_ = lean_nat_dec_le(v_tailOff_1071_, v_start_1064_);
if (v___x_1072_ == 0)
{
size_t v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_tailOff_1071_);
v___x_1073_ = lean_usize_of_nat(v_start_1064_);
lean_inc_ref(v_f_1062_);
v___x_1074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1062_, v_root_1068_, v___x_1073_, v_shift_1070_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1074_, 0);
lean_dec(v_unused_1088_);
v___x_1076_ = v___x_1074_;
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v___x_1074_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_array_get_size(v_tail_1069_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_nat_dec_lt(v___x_1066_, v___x_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1082_; 
lean_dec_ref(v_tail_1069_);
lean_dec_ref(v_f_1062_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1079_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
lean_del_object(v___x_1076_);
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1078_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1062_, v_tail_1069_, v___x_1084_, v___x_1085_, v___x_1079_);
lean_dec_ref(v_tail_1069_);
return v___x_1086_;
}
}
}
else
{
lean_dec_ref(v_tail_1069_);
lean_dec_ref(v_f_1062_);
return v___x_1074_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
lean_dec_ref(v_root_1068_);
v___x_1089_ = lean_nat_sub(v_start_1064_, v_tailOff_1071_);
lean_dec(v_tailOff_1071_);
v___x_1090_ = lean_array_get_size(v_tail_1069_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_nat_dec_lt(v___x_1089_, v___x_1090_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v___x_1089_);
lean_dec_ref(v_tail_1069_);
lean_dec_ref(v_f_1062_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
return v___x_1093_;
}
else
{
size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_usize_of_nat(v___x_1089_);
lean_dec(v___x_1089_);
v___x_1095_ = lean_usize_of_nat(v___x_1090_);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1062_, v_tail_1069_, v___x_1094_, v___x_1095_, v___x_1091_);
lean_dec_ref(v_tail_1069_);
return v___x_1096_;
}
}
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1062_, v_t_1063_);
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
lean_dec_ref_known(v___x_1196_, 1);
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
lean_dec_ref_known(v___x_1244_, 1);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
