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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
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
static const lean_ctor_object l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value;
static const lean_ctor_object l_Lean_Parser_instInhabitedModuleParserState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default___closed__1 = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState_default = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedModuleParserState = (const lean_object*)&l_Lean_Parser_instInhabitedModuleParserState_default___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_setLeadingStart(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "cannot use `public import` without `module`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "cannot use `all` with `public import`; consider using separate `public import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` and `import all "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "` directives in order to import public data into the public scope and private data into the private scope."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_value;
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
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to parse file"};
static const lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_value;
static lean_once_cell_t l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2;
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
v___x_1_ = l_Lean_Data_Trie_empty___redArg();
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object* v_as_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_zero_31_; uint8_t v_isZero_32_; 
v_zero_31_ = lean_unsigned_to_nat(0u);
v_isZero_32_ = lean_nat_dec_eq(v_i_30_, v_zero_31_);
if (v_isZero_32_ == 1)
{
lean_object* v___x_33_; 
lean_dec(v_i_30_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
lean_object* v_one_34_; lean_object* v_n_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_one_34_ = lean_unsigned_to_nat(1u);
v_n_35_ = lean_nat_sub(v_i_30_, v_one_34_);
lean_dec(v_i_30_);
v___x_36_ = l_Subarray_get___redArg(v_as_29_, v_n_35_);
v___x_37_ = l_Lean_Syntax_getTailInfo(v___x_36_);
lean_dec(v___x_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_trailing_38_; lean_object* v___x_39_; 
lean_dec(v_n_35_);
v_trailing_38_ = lean_ctor_get(v___x_37_, 2);
lean_inc_ref(v_trailing_38_);
lean_dec_ref_known(v___x_37_, 4);
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v_trailing_38_);
return v___x_39_;
}
else
{
lean_dec(v___x_37_);
v_i_30_ = v_n_35_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object* v_as_41_, lean_object* v_i_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_41_, v_i_42_);
lean_dec_ref(v_as_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object* v_s_44_){
_start:
{
lean_object* v___x_45_; lean_object* v_start_46_; lean_object* v_stop_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_45_ = l_Lean_Parser_SyntaxStack_toSubarray(v_s_44_);
v_start_46_ = lean_ctor_get(v___x_45_, 1);
v_stop_47_ = lean_ctor_get(v___x_45_, 2);
v___x_48_ = lean_nat_sub(v_stop_47_, v_start_46_);
v___x_49_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v___x_45_, v___x_48_);
lean_dec_ref(v___x_45_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object* v_as_50_, lean_object* v_i_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_50_, v_i_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object* v_as_54_, lean_object* v_i_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(v_as_54_, v_i_55_, v_a_56_);
lean_dec_ref(v_as_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* v_c_63_, lean_object* v_pos_64_, lean_object* v_stk_65_, lean_object* v_e_66_){
_start:
{
lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v_pos_81_; lean_object* v_endPos_x3f_82_; lean_object* v_e_83_; lean_object* v_unexpectedTk_97_; lean_object* v_expected_98_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v_pos_110_; lean_object* v_endPos_x3f_111_; lean_object* v_endPos_x3f_119_; uint8_t v___x_120_; 
v_unexpectedTk_97_ = lean_ctor_get(v_e_66_, 0);
v_expected_98_ = lean_ctor_get(v_e_66_, 2);
v_endPos_x3f_119_ = lean_box(0);
v___x_120_ = l_Lean_Syntax_isMissing(v_unexpectedTk_97_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_inc(v_expected_98_);
lean_inc(v_unexpectedTk_97_);
lean_dec_ref(v_e_66_);
v___x_121_ = l_Lean_Syntax_getRange_x3f(v_unexpectedTk_97_, v___x_120_);
if (lean_obj_tag(v___x_121_) == 1)
{
lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_pos_64_);
v_val_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_start_126_; lean_object* v_stop_127_; lean_object* v_endPos_x3f_129_; 
v_start_126_ = lean_ctor_get(v_val_122_, 0);
lean_inc(v_start_126_);
v_stop_127_ = lean_ctor_get(v_val_122_, 1);
lean_inc(v_stop_127_);
lean_dec(v_val_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_stop_127_);
v_endPos_x3f_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_stop_127_);
v_endPos_x3f_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
v_pos_110_ = v_start_126_;
v_endPos_x3f_111_ = v_endPos_x3f_129_;
goto v___jp_109_;
}
}
}
else
{
lean_dec(v___x_121_);
v_pos_110_ = v_pos_64_;
v_endPos_x3f_111_ = v_endPos_x3f_119_;
goto v___jp_109_;
}
}
else
{
lean_dec_ref(v_stk_65_);
v_pos_81_ = v_pos_64_;
v_endPos_x3f_82_ = v_endPos_x3f_119_;
v_e_83_ = v_e_66_;
goto v___jp_80_;
}
v___jp_67_:
{
uint8_t v___x_72_; uint8_t v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_72_ = 1;
v___x_73_ = 2;
v___x_74_ = 0;
v___x_75_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_76_ = l_Lean_Parser_Error_toString(v___y_69_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
v___x_79_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_79_, 0, v___y_70_);
lean_ctor_set(v___x_79_, 1, v___y_68_);
lean_ctor_set(v___x_79_, 2, v___y_71_);
lean_ctor_set(v___x_79_, 3, v___x_75_);
lean_ctor_set(v___x_79_, 4, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*5, v___x_72_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*5 + 1, v___x_73_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*5 + 2, v___x_74_);
return v___x_79_;
}
v___jp_80_:
{
lean_object* v_fileName_84_; lean_object* v_fileMap_85_; lean_object* v___x_86_; 
v_fileName_84_ = lean_ctor_get(v_c_63_, 1);
lean_inc_ref(v_fileName_84_);
v_fileMap_85_ = lean_ctor_get(v_c_63_, 2);
lean_inc_ref_n(v_fileMap_85_, 2);
lean_dec_ref(v_c_63_);
v___x_86_ = l_Lean_FileMap_toPosition(v_fileMap_85_, v_pos_81_);
lean_dec(v_pos_81_);
if (lean_obj_tag(v_endPos_x3f_82_) == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v_fileMap_85_);
v___x_87_ = lean_box(0);
v___y_68_ = v___x_86_;
v___y_69_ = v_e_83_;
v___y_70_ = v_fileName_84_;
v___y_71_ = v___x_87_;
goto v___jp_67_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_val_88_ = lean_ctor_get(v_endPos_x3f_82_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_endPos_x3f_82_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_endPos_x3f_82_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v_endPos_x3f_82_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Lean_FileMap_toPosition(v_fileMap_85_, v_val_88_);
lean_dec(v_val_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v___y_68_ = v___x_86_;
v___y_69_ = v_e_83_;
v___y_70_ = v_fileName_84_;
v___y_71_ = v___x_94_;
goto v___jp_67_;
}
}
}
}
v___jp_99_:
{
lean_object* v_e_103_; lean_object* v___x_104_; 
v_e_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_e_103_, 0, v_unexpectedTk_97_);
lean_ctor_set(v_e_103_, 1, v___y_102_);
lean_ctor_set(v_e_103_, 2, v_expected_98_);
v___x_104_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(v_stk_65_);
if (lean_obj_tag(v___x_104_) == 1)
{
lean_object* v_val_105_; lean_object* v_startPos_106_; lean_object* v_stopPos_107_; uint8_t v_decide_108_; 
v_val_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v___x_104_, 1);
v_startPos_106_ = lean_ctor_get(v_val_105_, 1);
lean_inc(v_startPos_106_);
v_stopPos_107_ = lean_ctor_get(v_val_105_, 2);
lean_inc(v_stopPos_107_);
lean_dec(v_val_105_);
v_decide_108_ = lean_nat_dec_eq(v_stopPos_107_, v___y_101_);
lean_dec(v_stopPos_107_);
if (v_decide_108_ == 0)
{
lean_dec(v_startPos_106_);
v_pos_81_ = v___y_101_;
v_endPos_x3f_82_ = v___y_100_;
v_e_83_ = v_e_103_;
goto v___jp_80_;
}
else
{
lean_dec(v___y_101_);
v_pos_81_ = v_startPos_106_;
v_endPos_x3f_82_ = v___y_100_;
v_e_83_ = v_e_103_;
goto v___jp_80_;
}
}
else
{
lean_dec(v___x_104_);
v_pos_81_ = v___y_101_;
v_endPos_x3f_82_ = v___y_100_;
v_e_83_ = v_e_103_;
goto v___jp_80_;
}
}
v___jp_109_:
{
switch(lean_obj_tag(v_unexpectedTk_97_))
{
case 3:
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1));
v___y_100_ = v_endPos_x3f_111_;
v___y_101_ = v_pos_110_;
v___y_102_ = v___x_112_;
goto v___jp_99_;
}
case 2:
{
lean_object* v_val_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_val_113_ = lean_ctor_get(v_unexpectedTk_97_, 1);
v___x_114_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2));
v___x_115_ = lean_string_append(v___x_114_, v_val_113_);
v___x_116_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3));
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
v___y_100_ = v_endPos_x3f_111_;
v___y_101_ = v_pos_110_;
v___y_102_ = v___x_117_;
goto v___jp_99_;
}
default: 
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
v___y_100_ = v_endPos_x3f_111_;
v___y_101_ = v_pos_110_;
v___y_102_ = v___x_118_;
goto v___jp_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_setLeadingStart(lean_object* v_stx_132_, lean_object* v_startPos_133_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Syntax_getHeadInfo_x3f(v_stx_132_);
if (lean_obj_tag(v___x_138_) == 1)
{
lean_object* v_val_139_; 
v_val_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v___x_138_, 1);
if (lean_obj_tag(v_val_139_) == 0)
{
lean_object* v_leading_140_; lean_object* v_pos_141_; lean_object* v_trailing_142_; lean_object* v_endPos_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_164_; 
v_leading_140_ = lean_ctor_get(v_val_139_, 0);
v_pos_141_ = lean_ctor_get(v_val_139_, 1);
v_trailing_142_ = lean_ctor_get(v_val_139_, 2);
v_endPos_143_ = lean_ctor_get(v_val_139_, 3);
v_isSharedCheck_164_ = !lean_is_exclusive(v_val_139_);
if (v_isSharedCheck_164_ == 0)
{
v___x_145_ = v_val_139_;
v_isShared_146_ = v_isSharedCheck_164_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_endPos_143_);
lean_inc(v_trailing_142_);
lean_inc(v_pos_141_);
lean_inc(v_leading_140_);
lean_dec(v_val_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_164_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_str_147_; lean_object* v_stopPos_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_162_; 
v_str_147_ = lean_ctor_get(v_leading_140_, 0);
v_stopPos_148_ = lean_ctor_get(v_leading_140_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_leading_140_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v_leading_140_, 1);
lean_dec(v_unused_163_);
v___x_150_ = v_leading_140_;
v_isShared_151_ = v_isSharedCheck_162_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_stopPos_148_);
lean_inc(v_str_147_);
lean_dec(v_leading_140_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_162_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_startPos_133_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_str_147_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_startPos_133_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_stopPos_148_);
v___x_153_ = v_reuseFailAlloc_161_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_153_);
v___x_155_ = v___x_145_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_pos_141_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_trailing_142_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_endPos_143_);
v___x_155_ = v_reuseFailAlloc_160_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = l_Lean_Syntax_setHeadInfo(v_stx_132_, v___x_155_);
v___x_157_ = 1;
v___x_158_ = lean_box(v___x_157_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_156_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
return v___x_159_;
}
}
}
}
}
else
{
lean_dec(v_val_139_);
lean_dec(v_startPos_133_);
goto v___jp_134_;
}
}
else
{
lean_dec(v___x_138_);
lean_dec(v_startPos_133_);
goto v___jp_134_;
}
v___jp_134_:
{
uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = 0;
v___x_136_ = lean_box(v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_stx_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
if (lean_obj_tag(v_x_166_) == 0)
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
}
else
{
if (lean_obj_tag(v_x_166_) == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v_val_171_; uint8_t v___x_172_; 
v_val_170_ = lean_ctor_get(v_x_165_, 0);
v_val_171_ = lean_ctor_get(v_x_166_, 0);
v___x_172_ = l_Lean_Parser_instBEqError_beq(v_val_170_, v_val_171_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec(v_x_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object* v_inputCtx_177_, lean_object* v_as_178_, size_t v_sz_179_, size_t v_i_180_, lean_object* v_b_181_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_180_, v_sz_179_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v_inputCtx_177_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_b_181_);
return v___x_184_;
}
else
{
lean_object* v_a_185_; lean_object* v_snd_186_; lean_object* v_fst_187_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_190_; lean_object* v___x_191_; size_t v___x_192_; size_t v___x_193_; 
v_a_185_ = lean_array_uget_borrowed(v_as_178_, v_i_180_);
v_snd_186_ = lean_ctor_get(v_a_185_, 1);
v_fst_187_ = lean_ctor_get(v_a_185_, 0);
v_fst_188_ = lean_ctor_get(v_snd_186_, 0);
v_snd_189_ = lean_ctor_get(v_snd_186_, 1);
lean_inc(v_snd_189_);
lean_inc(v_fst_188_);
lean_inc(v_fst_187_);
lean_inc_ref(v_inputCtx_177_);
v___x_190_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_177_, v_fst_187_, v_fst_188_, v_snd_189_);
v___x_191_ = l_Lean_MessageLog_add(v___x_190_, v_b_181_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_add(v_i_180_, v___x_192_);
v_i_180_ = v___x_193_;
v_b_181_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(lean_object* v_inputCtx_195_, lean_object* v_as_196_, lean_object* v_sz_197_, lean_object* v_i_198_, lean_object* v_b_199_, lean_object* v___y_200_){
_start:
{
size_t v_sz_boxed_201_; size_t v_i_boxed_202_; lean_object* v_res_203_; 
v_sz_boxed_201_ = lean_unbox_usize(v_sz_197_);
lean_dec(v_sz_197_);
v_i_boxed_202_ = lean_unbox_usize(v_i_198_);
lean_dec(v_i_198_);
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_195_, v_as_196_, v_sz_boxed_201_, v_i_boxed_202_, v_b_199_);
lean_dec_ref(v_as_196_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t v___x_204_, lean_object* v_inputCtx_205_, lean_object* v_ref_206_, lean_object* v_msg_207_){
_start:
{
uint8_t v___x_208_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_220_; lean_object* v___x_226_; 
v___x_208_ = 0;
v___x_226_ = l_Lean_Syntax_getPos_x3f(v_ref_206_, v___x_208_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___y_220_ = v___x_227_;
goto v___jp_219_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
v___y_220_ = v_val_228_;
goto v___jp_219_;
}
v___jp_209_:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_214_ = l_Lean_FileMap_toPosition(v___y_210_, v___y_213_);
lean_dec(v___y_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = 2;
v___x_217_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_218_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_218_, 0, v___y_212_);
lean_ctor_set(v___x_218_, 1, v___y_211_);
lean_ctor_set(v___x_218_, 2, v___x_215_);
lean_ctor_set(v___x_218_, 3, v___x_217_);
lean_ctor_set(v___x_218_, 4, v_msg_207_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5, v___x_204_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5 + 1, v___x_216_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5 + 2, v___x_208_);
return v___x_218_;
}
v___jp_219_:
{
lean_object* v_fileName_221_; lean_object* v_fileMap_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_fileName_221_ = lean_ctor_get(v_inputCtx_205_, 1);
lean_inc_ref(v_fileName_221_);
v_fileMap_222_ = lean_ctor_get(v_inputCtx_205_, 2);
lean_inc_ref_n(v_fileMap_222_, 2);
lean_dec_ref(v_inputCtx_205_);
v___x_223_ = l_Lean_FileMap_toPosition(v_fileMap_222_, v___y_220_);
v___x_224_ = l_Lean_Syntax_getTailPos_x3f(v_ref_206_, v___x_208_);
if (lean_obj_tag(v___x_224_) == 0)
{
v___y_210_ = v_fileMap_222_;
v___y_211_ = v___x_223_;
v___y_212_ = v_fileName_221_;
v___y_213_ = v___y_220_;
goto v___jp_209_;
}
else
{
lean_object* v_val_225_; 
lean_dec(v___y_220_);
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___y_210_ = v_fileMap_222_;
v___y_211_ = v___x_223_;
v___y_212_ = v_fileName_221_;
v___y_213_ = v_val_225_;
goto v___jp_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_229_, lean_object* v_inputCtx_230_, lean_object* v_ref_231_, lean_object* v_msg_232_){
_start:
{
uint8_t v___x_3155__boxed_233_; lean_object* v_res_234_; 
v___x_3155__boxed_233_ = lean_unbox(v___x_229_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_3155__boxed_233_, v_inputCtx_230_, v_ref_231_, v_msg_232_);
lean_dec(v_ref_231_);
return v_res_234_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
v___x_248_ = l_Lean_MessageData_ofFormat(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9));
v___x_253_ = l_Lean_MessageData_ofFormat(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12));
v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object* v_inputCtx_280_, lean_object* v_moduleTk_x3f_281_, lean_object* v_as_282_, size_t v_sz_283_, size_t v_i_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_a_288_; uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref(v_inputCtx_280_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_b_285_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v_a_295_; uint8_t v___x_296_; 
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4));
v_a_295_ = lean_array_uget_borrowed(v_as_282_, v_i_284_);
lean_inc(v_a_295_);
v___x_296_ = l_Lean_Syntax_isOfKind(v_a_295_, v___x_294_);
if (v___x_296_ == 0)
{
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___y_298_; lean_object* v_messages_299_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v_messages_307_; lean_object* v___x_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v_allTk_x3f_316_; lean_object* v___x_347_; lean_object* v___y_349_; lean_object* v_metaTk_x3f_350_; lean_object* v_pubTk_x3f_362_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_372_ = l_Lean_Syntax_getArg(v_a_295_, v___x_312_);
v___x_373_ = l_Lean_Syntax_isNone(v___x_372_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
lean_inc(v___x_372_);
v___x_374_ = l_Lean_Syntax_matchesNull(v___x_372_, v___x_347_);
if (v___x_374_ == 0)
{
lean_dec(v___x_372_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_Syntax_getArg(v___x_372_, v___x_312_);
lean_dec(v___x_372_);
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22));
lean_inc(v___x_375_);
v___x_377_ = l_Lean_Syntax_isOfKind(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec(v___x_375_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_Syntax_getArg(v___x_375_, v___x_312_);
lean_dec(v___x_375_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v_pubTk_x3f_362_ = v___x_379_;
goto v___jp_361_;
}
}
}
else
{
lean_object* v___x_380_; 
lean_dec(v___x_372_);
v___x_380_ = lean_box(0);
v_pubTk_x3f_362_ = v___x_380_;
goto v___jp_361_;
}
v___jp_297_:
{
if (lean_obj_tag(v___y_298_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_val_300_ = lean_ctor_get(v___y_298_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___y_298_, 1);
v___x_301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7);
lean_inc_ref(v_inputCtx_280_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_296_, v_inputCtx_280_, v_val_300_, v___x_301_);
lean_dec(v_val_300_);
v___x_303_ = l_Lean_MessageLog_add(v___x_302_, v_messages_299_);
v_a_288_ = v___x_303_;
goto v___jp_287_;
}
else
{
lean_dec(v___y_298_);
v_a_288_ = v_messages_299_;
goto v___jp_287_;
}
}
v___jp_304_:
{
if (lean_obj_tag(v___y_306_) == 1)
{
lean_object* v_val_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_val_308_ = lean_ctor_get(v___y_306_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___y_306_, 1);
v___x_309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_280_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_296_, v_inputCtx_280_, v_val_308_, v___x_309_);
lean_dec(v_val_308_);
v___x_311_ = l_Lean_MessageLog_add(v___x_310_, v_messages_307_);
v___y_298_ = v___y_305_;
v_messages_299_ = v___x_311_;
goto v___jp_297_;
}
else
{
lean_dec(v___y_306_);
v___y_298_ = v___y_305_;
v_messages_299_ = v_messages_307_;
goto v___jp_297_;
}
}
v___jp_313_:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(5u);
v___x_318_ = l_Lean_Syntax_getArg(v_a_295_, v___x_317_);
v___x_319_ = l_Lean_Syntax_matchesNull(v___x_318_, v___x_312_);
if (v___x_319_ == 0)
{
lean_dec(v_allTk_x3f_316_);
lean_dec(v___y_315_);
lean_dec(v___y_314_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
if (lean_obj_tag(v_moduleTk_x3f_281_) == 0)
{
if (lean_obj_tag(v___y_314_) == 1)
{
lean_object* v_val_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_val_320_ = lean_ctor_get(v___y_314_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___y_314_, 1);
v___x_321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13);
lean_inc_ref(v_inputCtx_280_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_296_, v_inputCtx_280_, v_val_320_, v___x_321_);
lean_dec(v_val_320_);
v___x_323_ = l_Lean_MessageLog_add(v___x_322_, v_b_285_);
v___y_305_ = v_allTk_x3f_316_;
v___y_306_ = v___y_315_;
v_messages_307_ = v___x_323_;
goto v___jp_304_;
}
else
{
lean_dec(v___y_314_);
v___y_305_ = v_allTk_x3f_316_;
v___y_306_ = v___y_315_;
v_messages_307_ = v_b_285_;
goto v___jp_304_;
}
}
else
{
lean_dec(v___y_315_);
if (lean_obj_tag(v_allTk_x3f_316_) == 1)
{
if (lean_obj_tag(v___y_314_) == 0)
{
lean_dec_ref_known(v_allTk_x3f_316_, 1);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v_val_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_345_; 
v_val_324_ = lean_ctor_get(v_allTk_x3f_316_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v_allTk_x3f_316_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v___y_314_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v___y_314_, 0);
lean_dec(v_unused_346_);
v___x_326_ = v___y_314_;
v_isShared_327_ = v_isSharedCheck_345_;
goto v_resetjp_325_;
}
else
{
lean_dec(v___y_314_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_345_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = l_Lean_Syntax_getArg(v_a_295_, v___x_328_);
v___x_330_ = l_Lean_TSyntax_getId(v___x_329_);
lean_dec(v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14));
v___x_332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_330_, v___x_319_);
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15));
v___x_335_ = lean_string_append(v___x_333_, v___x_334_);
v___x_336_ = lean_string_append(v___x_335_, v___x_332_);
lean_dec_ref(v___x_332_);
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16));
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 3);
lean_ctor_set(v___x_326_, 0, v___x_338_);
v___x_340_ = v___x_326_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = l_Lean_MessageData_ofFormat(v___x_340_);
lean_inc_ref(v_inputCtx_280_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_296_, v_inputCtx_280_, v_val_324_, v___x_341_);
lean_dec(v_val_324_);
v___x_343_ = l_Lean_MessageLog_add(v___x_342_, v_b_285_);
v_a_288_ = v___x_343_;
goto v___jp_287_;
}
}
}
}
else
{
lean_dec(v_allTk_x3f_316_);
lean_dec(v___y_314_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
}
}
}
v___jp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_unsigned_to_nat(3u);
v___x_352_ = l_Lean_Syntax_getArg(v_a_295_, v___x_351_);
v___x_353_ = l_Lean_Syntax_isNone(v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
lean_inc(v___x_352_);
v___x_354_ = l_Lean_Syntax_matchesNull(v___x_352_, v___x_347_);
if (v___x_354_ == 0)
{
lean_dec(v___x_352_);
lean_dec(v_metaTk_x3f_350_);
lean_dec(v___y_349_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = l_Lean_Syntax_getArg(v___x_352_, v___x_312_);
lean_dec(v___x_352_);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18));
lean_inc(v___x_355_);
v___x_357_ = l_Lean_Syntax_isOfKind(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v___x_355_);
lean_dec(v_metaTk_x3f_350_);
lean_dec(v___y_349_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Syntax_getArg(v___x_355_, v___x_312_);
lean_dec(v___x_355_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
v___y_314_ = v___y_349_;
v___y_315_ = v_metaTk_x3f_350_;
v_allTk_x3f_316_ = v___x_359_;
goto v___jp_313_;
}
}
}
else
{
lean_object* v___x_360_; 
lean_dec(v___x_352_);
v___x_360_ = lean_box(0);
v___y_314_ = v___y_349_;
v___y_315_ = v_metaTk_x3f_350_;
v_allTk_x3f_316_ = v___x_360_;
goto v___jp_313_;
}
}
v___jp_361_:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = l_Lean_Syntax_getArg(v_a_295_, v___x_347_);
v___x_364_ = l_Lean_Syntax_isNone(v___x_363_);
if (v___x_364_ == 0)
{
uint8_t v___x_365_; 
lean_inc(v___x_363_);
v___x_365_ = l_Lean_Syntax_matchesNull(v___x_363_, v___x_347_);
if (v___x_365_ == 0)
{
lean_dec(v___x_363_);
lean_dec(v_pubTk_x3f_362_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = l_Lean_Syntax_getArg(v___x_363_, v___x_312_);
lean_dec(v___x_363_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20));
lean_inc(v___x_366_);
v___x_368_ = l_Lean_Syntax_isOfKind(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_dec(v___x_366_);
lean_dec(v_pubTk_x3f_362_);
v_a_288_ = v_b_285_;
goto v___jp_287_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_Syntax_getArg(v___x_366_, v___x_312_);
lean_dec(v___x_366_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___y_349_ = v_pubTk_x3f_362_;
v_metaTk_x3f_350_ = v___x_370_;
goto v___jp_348_;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v___x_363_);
v___x_371_ = lean_box(0);
v___y_349_ = v_pubTk_x3f_362_;
v_metaTk_x3f_350_ = v___x_371_;
goto v___jp_348_;
}
}
}
}
v___jp_287_:
{
size_t v___x_289_; size_t v___x_290_; 
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_add(v_i_284_, v___x_289_);
v_i_284_ = v___x_290_;
v_b_285_ = v_a_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* v_inputCtx_381_, lean_object* v_moduleTk_x3f_382_, lean_object* v_as_383_, lean_object* v_sz_384_, lean_object* v_i_385_, lean_object* v_b_386_, lean_object* v___y_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_384_);
lean_dec(v_sz_384_);
v_i_boxed_389_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_381_, v_moduleTk_x3f_382_, v_as_383_, v_sz_boxed_388_, v_i_boxed_389_, v_b_386_);
lean_dec_ref(v_as_383_);
lean_dec(v_moduleTk_x3f_382_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(32u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3(void){
_start:
{
size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_unsigned_to_nat(32u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__2, &l_Lean_Parser_parseHeader___closed__2_once, _init_l_Lean_Parser_parseHeader___closed__2);
v___x_401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_397_);
lean_ctor_set(v___x_401_, 3, v___x_397_);
lean_ctor_set_usize(v___x_401_, 4, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = l_Lean_NameSet_empty;
v___x_403_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__3, &l_Lean_Parser_parseHeader___closed__3_once, _init_l_Lean_Parser_parseHeader___closed__3);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* v_inputCtx_417_, lean_object* v_startPos_418_){
_start:
{
lean_object* v___x_420_; uint32_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = 0;
v___x_422_ = l_Lean_mkEmptyEnvironment(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_555_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_555_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_555_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_555_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_fn_428_; lean_object* v_inputString_429_; lean_object* v___x_430_; lean_object* v_stxStack_431_; lean_object* v_lhsPrec_432_; lean_object* v_cache_433_; lean_object* v_errorMsg_434_; lean_object* v_recoveredErrors_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_553_; 
v___x_427_ = l_Lean_Parser_Module_header;
v_fn_428_ = lean_ctor_get(v___x_427_, 1);
v_inputString_429_ = lean_ctor_get(v_inputCtx_417_, 0);
v___x_430_ = l_Lean_Parser_mkParserState(v_inputString_429_);
v_stxStack_431_ = lean_ctor_get(v___x_430_, 0);
v_lhsPrec_432_ = lean_ctor_get(v___x_430_, 1);
v_cache_433_ = lean_ctor_get(v___x_430_, 3);
v_errorMsg_434_ = lean_ctor_get(v___x_430_, 4);
v_recoveredErrors_435_ = lean_ctor_get(v___x_430_, 5);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v___x_430_, 2);
lean_dec(v_unused_554_);
v___x_437_ = v___x_430_;
v_isShared_438_ = v_isSharedCheck_553_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_recoveredErrors_435_);
lean_inc(v_errorMsg_434_);
lean_inc(v_cache_433_);
lean_inc(v_lhsPrec_432_);
lean_inc(v_stxStack_431_);
lean_dec(v___x_430_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_553_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
lean_inc(v_a_423_);
v___x_439_ = l_Lean_Parser_getTokenTable(v_a_423_);
v___x_440_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_428_);
v___x_441_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_441_, 0, v___x_440_);
lean_closure_set(v___x_441_, 1, v_fn_428_);
v___x_442_ = l_Lean_Parser_Module_updateTokens(v___x_439_);
v___x_443_ = l_Lean_Options_empty;
v___x_444_ = lean_box(0);
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_446_, 0, v_a_423_);
lean_ctor_set(v___x_446_, 1, v___x_443_);
lean_ctor_set(v___x_446_, 2, v___x_444_);
lean_ctor_set(v___x_446_, 3, v___x_445_);
lean_inc(v_startPos_418_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 2, v_startPos_418_);
v___x_448_ = v___x_437_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_stxStack_431_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_lhsPrec_432_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_startPos_418_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_cache_433_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_errorMsg_434_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v_recoveredErrors_435_);
v___x_448_ = v_reuseFailAlloc_552_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v_stxStack_450_; lean_object* v_pos_451_; lean_object* v_errorMsg_452_; uint8_t v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; uint8_t v___y_468_; lean_object* v___y_472_; lean_object* v_messages_473_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; size_t v___y_487_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; size_t v___y_508_; lean_object* v_moduleTk_x3f_509_; lean_object* v___y_519_; uint8_t v___x_549_; 
lean_inc_ref(v_inputCtx_417_);
v___x_449_ = l_Lean_Parser_ParserFn_run(v___x_441_, v_inputCtx_417_, v___x_446_, v___x_442_, v___x_448_);
v_stxStack_450_ = lean_ctor_get(v___x_449_, 0);
v_pos_451_ = lean_ctor_get(v___x_449_, 2);
lean_inc(v_pos_451_);
v_errorMsg_452_ = lean_ctor_get(v___x_449_, 4);
lean_inc(v_errorMsg_452_);
v___x_549_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_450_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_450_);
v___y_519_ = v___x_550_;
goto v___jp_518_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
v___y_519_ = v___x_551_;
goto v___jp_518_;
}
v___jp_453_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_458_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_458_, 0, v_pos_451_);
lean_ctor_set(v___x_458_, 1, v___y_457_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*2, v___y_454_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___y_456_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___y_455_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_460_);
v___x_462_ = v___x_425_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
v___jp_464_:
{
if (v___y_465_ == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_startPos_418_);
v___y_454_ = v___y_468_;
v___y_455_ = v___y_467_;
v___y_456_ = v___y_466_;
v___y_457_ = v___x_469_;
goto v___jp_453_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_startPos_418_);
v___x_470_ = lean_box(0);
v___y_454_ = v___y_468_;
v___y_455_ = v___y_467_;
v___y_456_ = v___y_466_;
v___y_457_ = v___x_470_;
goto v___jp_453_;
}
}
v___jp_471_:
{
lean_object* v___x_474_; lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
lean_inc(v_startPos_418_);
v___x_474_ = l___private_Lean_Parser_Module_0__Lean_Parser_setLeadingStart(v___y_472_, v_startPos_418_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_fst_475_);
v_snd_476_ = lean_ctor_get(v___x_474_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v___x_474_);
v___x_477_ = lean_box(0);
v___x_478_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_452_, v___x_477_);
lean_dec(v_errorMsg_452_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 1;
v___x_480_ = lean_unbox(v_snd_476_);
lean_dec(v_snd_476_);
v___y_465_ = v___x_480_;
v___y_466_ = v_messages_473_;
v___y_467_ = v_fst_475_;
v___y_468_ = v___x_479_;
goto v___jp_464_;
}
else
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 0;
v___x_482_ = lean_unbox(v_snd_476_);
lean_dec(v_snd_476_);
v___y_465_ = v___x_482_;
v___y_466_ = v_messages_473_;
v___y_467_ = v_fst_475_;
v___y_468_ = v___x_481_;
goto v___jp_464_;
}
}
v___jp_483_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; size_t v_sz_491_; lean_object* v___x_492_; 
v___x_488_ = lean_unsigned_to_nat(2u);
v___x_489_ = l_Lean_Syntax_getArg(v___y_485_, v___x_488_);
v___x_490_ = l_Lean_Syntax_getArgs(v___x_489_);
lean_dec(v___x_489_);
v_sz_491_ = lean_array_size(v___x_490_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_417_, v___y_484_, v___x_490_, v_sz_491_, v___y_487_, v___y_486_);
lean_dec_ref(v___x_490_);
lean_dec(v___y_484_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v___y_472_ = v___y_485_;
v_messages_473_ = v_a_493_;
goto v___jp_471_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___y_485_);
lean_dec(v_errorMsg_452_);
lean_dec(v_pos_451_);
lean_del_object(v___x_425_);
lean_dec(v_startPos_418_);
v_a_494_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_492_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
v___jp_502_:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = l_Lean_Syntax_getArg(v___y_504_, v___x_510_);
v___x_512_ = l_Lean_Syntax_isNone(v___x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
lean_inc(v___x_511_);
v___x_513_ = l_Lean_Syntax_matchesNull(v___x_511_, v___x_510_);
if (v___x_513_ == 0)
{
lean_dec(v___x_511_);
lean_dec(v_moduleTk_x3f_509_);
lean_dec_ref(v_inputCtx_417_);
v___y_472_ = v___y_504_;
v_messages_473_ = v___y_507_;
goto v___jp_471_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = l_Lean_Syntax_getArg(v___x_511_, v___x_420_);
lean_dec(v___x_511_);
v___x_515_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_505_);
lean_inc_ref(v___y_506_);
lean_inc_ref(v___y_503_);
v___x_516_ = l_Lean_Name_mkStr4(v___y_503_, v___y_506_, v___y_505_, v___x_515_);
v___x_517_ = l_Lean_Syntax_isOfKind(v___x_514_, v___x_516_);
lean_dec(v___x_516_);
if (v___x_517_ == 0)
{
lean_dec(v_moduleTk_x3f_509_);
lean_dec_ref(v_inputCtx_417_);
v___y_472_ = v___y_504_;
v_messages_473_ = v___y_507_;
goto v___jp_471_;
}
else
{
v___y_484_ = v_moduleTk_x3f_509_;
v___y_485_ = v___y_504_;
v___y_486_ = v___y_507_;
v___y_487_ = v___y_508_;
goto v___jp_483_;
}
}
}
else
{
lean_dec(v___x_511_);
v___y_484_ = v_moduleTk_x3f_509_;
v___y_485_ = v___y_504_;
v___y_486_ = v___y_507_;
v___y_487_ = v___y_508_;
goto v___jp_483_;
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_520_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_521_ = l_Lean_Parser_ParserState_allErrors(v___x_449_);
v_sz_522_ = lean_array_size(v___x_521_);
v___x_523_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_417_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_417_, v___x_521_, v_sz_522_, v___x_523_, v___x_520_);
lean_dec_ref(v___x_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_529_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_519_);
v___x_530_ = l_Lean_Syntax_isOfKind(v___y_519_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec_ref(v_inputCtx_417_);
v___y_472_ = v___y_519_;
v_messages_473_ = v_a_525_;
goto v___jp_471_;
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = l_Lean_Syntax_getArg(v___y_519_, v___x_420_);
v___x_532_ = l_Lean_Syntax_isNone(v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_531_);
v___x_534_ = l_Lean_Syntax_matchesNull(v___x_531_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v___x_531_);
lean_dec_ref(v_inputCtx_417_);
v___y_472_ = v___y_519_;
v_messages_473_ = v_a_525_;
goto v___jp_471_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = l_Lean_Syntax_getArg(v___x_531_, v___x_420_);
lean_dec(v___x_531_);
v___x_536_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_535_);
v___x_537_ = l_Lean_Syntax_isOfKind(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec(v___x_535_);
lean_dec_ref(v_inputCtx_417_);
v___y_472_ = v___y_519_;
v_messages_473_ = v_a_525_;
goto v___jp_471_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = l_Lean_Syntax_getArg(v___x_535_, v___x_420_);
lean_dec(v___x_535_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___y_503_ = v___x_526_;
v___y_504_ = v___y_519_;
v___y_505_ = v___x_528_;
v___y_506_ = v___x_527_;
v___y_507_ = v_a_525_;
v___y_508_ = v___x_523_;
v_moduleTk_x3f_509_ = v___x_539_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec(v___x_531_);
v___x_540_ = lean_box(0);
v___y_503_ = v___x_526_;
v___y_504_ = v___y_519_;
v___y_505_ = v___x_528_;
v___y_506_ = v___x_527_;
v___y_507_ = v_a_525_;
v___y_508_ = v___x_523_;
v_moduleTk_x3f_509_ = v___x_540_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___y_519_);
lean_dec(v_errorMsg_452_);
lean_dec(v_pos_451_);
lean_del_object(v___x_425_);
lean_dec(v_startPos_418_);
lean_dec_ref(v_inputCtx_417_);
v_a_541_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_524_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_524_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_startPos_418_);
lean_dec_ref(v_inputCtx_417_);
v_a_556_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_422_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_422_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_564_, lean_object* v_startPos_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Parser_parseHeader(v_inputCtx_564_, v_startPos_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_575_, lean_object* v_pos_576_){
_start:
{
lean_object* v___y_578_; lean_object* v_inputString_588_; lean_object* v_endPos_589_; uint8_t v___x_590_; 
v_inputString_588_ = lean_ctor_get(v_inputCtx_575_, 0);
v_endPos_589_ = lean_ctor_get(v_inputCtx_575_, 3);
v___x_590_ = lean_nat_dec_le(v_pos_576_, v_endPos_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_inc(v_endPos_589_);
lean_inc(v_pos_576_);
lean_inc_ref(v_inputString_588_);
v___x_591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_591_, 0, v_inputString_588_);
lean_ctor_set(v___x_591_, 1, v_pos_576_);
lean_ctor_set(v___x_591_, 2, v_endPos_589_);
v___y_578_ = v___x_591_;
goto v___jp_577_;
}
else
{
lean_object* v___x_592_; 
lean_inc_n(v_pos_576_, 2);
lean_inc_ref(v_inputString_588_);
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v_inputString_588_);
lean_ctor_set(v___x_592_, 1, v_pos_576_);
lean_ctor_set(v___x_592_, 2, v_pos_576_);
v___y_578_ = v___x_592_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_atom_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_inc(v_pos_576_);
lean_inc_ref(v___y_578_);
v___x_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_579_, 0, v___y_578_);
lean_ctor_set(v___x_579_, 1, v_pos_576_);
lean_ctor_set(v___x_579_, 2, v___y_578_);
lean_ctor_set(v___x_579_, 3, v_pos_576_);
v___x_580_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_581_, 0, v___x_579_);
lean_ctor_set(v_atom_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v_atom_581_);
v___x_586_ = lean_box(2);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_582_);
lean_ctor_set(v___x_587_, 2, v___x_585_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_593_, lean_object* v_pos_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_593_, v_pos_594_);
lean_dec_ref(v_inputCtx_593_);
return v_res_595_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_607_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_607_);
v___x_609_ = l_Lean_Syntax_isOfKind(v_s_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_607_);
v___x_611_ = l_Lean_Syntax_isOfKind(v_s_607_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_613_ = l_Lean_Syntax_isOfKind(v_s_607_, v___x_612_);
return v___x_613_;
}
else
{
lean_dec(v_s_607_);
return v___x_611_;
}
}
else
{
lean_dec(v_s_607_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* v_s_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Lean_Parser_isTerminalCommand(v_s_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_621_, lean_object* v_pmctx_622_, lean_object* v_pos_623_){
_start:
{
lean_object* v_inputString_624_; lean_object* v_env_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_s_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_s_634_; lean_object* v_errorMsg_635_; 
v_inputString_624_ = lean_ctor_get(v_inputCtx_621_, 0);
v_env_625_ = lean_ctor_get(v_pmctx_622_, 0);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_628_ = l_Lean_Parser_SyntaxStack_empty;
v___x_629_ = l_Lean_Parser_initCacheForInput(v_inputString_624_);
v___x_630_ = lean_box(0);
lean_inc(v_pos_623_);
v_s_631_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_631_, 0, v___x_628_);
lean_ctor_set(v_s_631_, 1, v___x_626_);
lean_ctor_set(v_s_631_, 2, v_pos_623_);
lean_ctor_set(v_s_631_, 3, v___x_629_);
lean_ctor_set(v_s_631_, 4, v___x_630_);
lean_ctor_set(v_s_631_, 5, v___x_627_);
v___x_632_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_625_);
v___x_633_ = l_Lean_Parser_getTokenTable(v_env_625_);
v_s_634_ = l_Lean_Parser_ParserFn_run(v___x_632_, v_inputCtx_621_, v_pmctx_622_, v___x_633_, v_s_631_);
v_errorMsg_635_ = lean_ctor_get(v_s_634_, 4);
if (lean_obj_tag(v_errorMsg_635_) == 0)
{
lean_object* v_pos_636_; 
lean_dec(v_pos_623_);
v_pos_636_ = lean_ctor_get(v_s_634_, 2);
lean_inc(v_pos_636_);
lean_dec_ref(v_s_634_);
return v_pos_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_s_634_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_pos_623_, v___x_637_);
lean_dec(v_pos_623_);
return v___x_638_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_644_ = l_Lean_Parser_categoryParser(v___x_643_, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_646_ = l_Lean_Parser_withPosition(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; lean_object* v_fn_650_; lean_object* v___x_651_; 
v___x_649_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_650_ = lean_ctor_get(v___x_649_, 1);
lean_inc_ref(v_fn_650_);
v___x_651_ = lean_apply_2(v_fn_650_, v_a_647_, v_a_648_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_652_, lean_object* v_as_653_, size_t v_sz_654_, size_t v_i_655_, lean_object* v_b_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_lt(v_i_655_, v_sz_654_);
if (v___x_657_ == 0)
{
lean_dec_ref(v_inputCtx_652_);
return v_b_656_;
}
else
{
lean_object* v_a_658_; lean_object* v_snd_659_; lean_object* v_fst_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; 
v_a_658_ = lean_array_uget_borrowed(v_as_653_, v_i_655_);
v_snd_659_ = lean_ctor_get(v_a_658_, 1);
v_fst_660_ = lean_ctor_get(v_a_658_, 0);
v_fst_661_ = lean_ctor_get(v_snd_659_, 0);
v_snd_662_ = lean_ctor_get(v_snd_659_, 1);
lean_inc(v_snd_662_);
lean_inc(v_fst_661_);
lean_inc(v_fst_660_);
lean_inc_ref(v_inputCtx_652_);
v___x_663_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_652_, v_fst_660_, v_fst_661_, v_snd_662_);
v___x_664_ = l_Lean_MessageLog_add(v___x_663_, v_b_656_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_655_, v___x_665_);
v_i_655_ = v___x_666_;
v_b_656_ = v___x_664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_668_, lean_object* v_as_669_, lean_object* v_sz_670_, lean_object* v_i_671_, lean_object* v_b_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v_i_boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v_i_boxed_674_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_668_, v_as_669_, v_sz_boxed_673_, v_i_boxed_674_, v_b_672_);
lean_dec_ref(v_as_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_snd_676_, uint8_t v___x_677_, lean_object* v_inputCtx_678_, lean_object* v_pos_679_, lean_object* v_stxStack_680_, lean_object* v_val_681_, lean_object* v___x_682_, lean_object* v_fst_683_, uint8_t v___y_684_, lean_object* v_____r_685_, lean_object* v_pos_686_){
_start:
{
lean_object* v_messages_688_; uint8_t v___y_695_; uint8_t v___y_705_; uint8_t v___x_707_; 
v___x_707_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_680_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_680_);
v___x_709_ = l_Lean_Syntax_getPos_x3f(v___x_708_, v___y_684_);
lean_dec(v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
v___y_705_ = v___x_677_;
goto v___jp_704_;
}
else
{
lean_dec_ref_known(v___x_709_, 1);
v___y_705_ = v___y_684_;
goto v___jp_704_;
}
}
else
{
v___y_705_ = v___x_677_;
goto v___jp_704_;
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_messages_688_);
lean_ctor_set(v___x_689_, 1, v_snd_676_);
v___x_690_ = lean_box(v___x_677_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_pos_686_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc_ref(v_stxStack_680_);
v___x_696_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_678_, v_pos_679_, v_stxStack_680_, v_val_681_);
v___x_697_ = l_Lean_MessageLog_add(v___x_696_, v___x_682_);
if (v___y_695_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_snd_676_);
v___x_698_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_680_);
lean_dec_ref(v_stxStack_680_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_box(v___x_677_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_pos_686_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_dec_ref(v_stxStack_680_);
v_messages_688_ = v___x_697_;
goto v___jp_687_;
}
}
v___jp_704_:
{
uint8_t v___x_706_; 
v___x_706_ = lean_unbox(v_fst_683_);
if (v___x_706_ == 0)
{
v___y_695_ = v___y_705_;
goto v___jp_694_;
}
else
{
if (v___y_705_ == 0)
{
v___y_695_ = v___y_705_;
goto v___jp_694_;
}
else
{
lean_dec_ref(v_val_681_);
lean_dec_ref(v_stxStack_680_);
lean_dec(v_pos_679_);
lean_dec_ref(v_inputCtx_678_);
v_messages_688_ = v___x_682_;
goto v___jp_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_snd_710_, lean_object* v___x_711_, lean_object* v_inputCtx_712_, lean_object* v_pos_713_, lean_object* v_stxStack_714_, lean_object* v_val_715_, lean_object* v___x_716_, lean_object* v_fst_717_, lean_object* v___y_718_, lean_object* v_____r_719_, lean_object* v_pos_720_){
_start:
{
uint8_t v___x_1860__boxed_721_; uint8_t v___y_1863__boxed_722_; lean_object* v_res_723_; 
v___x_1860__boxed_721_ = lean_unbox(v___x_711_);
v___y_1863__boxed_722_ = lean_unbox(v___y_718_);
v_res_723_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_710_, v___x_1860__boxed_721_, v_inputCtx_712_, v_pos_713_, v_stxStack_714_, v_val_715_, v___x_716_, v_fst_717_, v___y_1863__boxed_722_, v_____r_719_, v_pos_720_);
lean_dec(v_fst_717_);
return v_res_723_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_725_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_726_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_726_, 0, v___x_725_);
lean_closure_set(v___x_726_, 1, v___x_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_727_, lean_object* v_pmctx_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___y_731_; lean_object* v_snd_735_; lean_object* v_snd_736_; lean_object* v_fst_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_811_; 
v_snd_735_ = lean_ctor_get(v_a_729_, 1);
lean_inc(v_snd_735_);
v_snd_736_ = lean_ctor_get(v_snd_735_, 1);
lean_inc(v_snd_736_);
v_fst_737_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v_a_729_, 1);
lean_dec(v_unused_812_);
v___x_739_ = v_a_729_;
v_isShared_740_ = v_isSharedCheck_811_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_fst_737_);
lean_dec(v_a_729_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_811_;
goto v_resetjp_738_;
}
v___jp_730_:
{
if (lean_obj_tag(v___y_731_) == 0)
{
lean_object* v_a_732_; 
lean_dec_ref(v_pmctx_728_);
lean_dec_ref(v_inputCtx_727_);
v_a_732_ = lean_ctor_get(v___y_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___y_731_, 1);
return v_a_732_;
}
else
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v___y_731_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___y_731_, 1);
v_a_729_ = v_a_733_;
goto _start;
}
}
v_resetjp_738_:
{
lean_object* v_fst_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_809_; 
v_fst_741_ = lean_ctor_get(v_snd_735_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_snd_735_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_snd_735_, 1);
lean_dec(v_unused_810_);
v___x_743_ = v_snd_735_;
v_isShared_744_ = v_isSharedCheck_809_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_fst_741_);
lean_dec(v_snd_735_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_809_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_808_; 
v_fst_745_ = lean_ctor_get(v_snd_736_, 0);
v_snd_746_ = lean_ctor_get(v_snd_736_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_snd_736_);
if (v_isSharedCheck_808_ == 0)
{
v___x_748_ = v_snd_736_;
v_isShared_749_ = v_isSharedCheck_808_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_inc(v_fst_745_);
lean_dec(v_snd_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_808_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___x_750_; 
v___x_750_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_727_, v_fst_737_);
if (v___x_750_ == 0)
{
lean_object* v_env_751_; lean_object* v_inputString_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_stxStack_762_; lean_object* v_pos_763_; lean_object* v_errorMsg_764_; lean_object* v_recoveredErrors_765_; uint8_t v___x_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; uint8_t v___y_771_; uint8_t v___x_790_; 
v_env_751_ = lean_ctor_get(v_pmctx_728_, 0);
v_inputString_752_ = lean_ctor_get(v_inputCtx_727_, 0);
v___x_753_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_751_);
v___x_754_ = l_Lean_Parser_getTokenTable(v_env_751_);
v___x_755_ = l_Lean_Parser_SyntaxStack_empty;
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Lean_Parser_initCacheForInput(v_inputString_752_);
v___x_758_ = lean_box(0);
v___x_759_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_737_);
v___x_760_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_760_, 0, v___x_755_);
lean_ctor_set(v___x_760_, 1, v___x_756_);
lean_ctor_set(v___x_760_, 2, v_fst_737_);
lean_ctor_set(v___x_760_, 3, v___x_757_);
lean_ctor_set(v___x_760_, 4, v___x_758_);
lean_ctor_set(v___x_760_, 5, v___x_759_);
lean_inc_ref(v_pmctx_728_);
lean_inc_ref_n(v_inputCtx_727_, 2);
v___x_761_ = l_Lean_Parser_ParserFn_run(v___x_753_, v_inputCtx_727_, v_pmctx_728_, v___x_754_, v___x_760_);
v_stxStack_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_stxStack_762_);
v_pos_763_ = lean_ctor_get(v___x_761_, 2);
lean_inc(v_pos_763_);
v_errorMsg_764_ = lean_ctor_get(v___x_761_, 4);
lean_inc(v_errorMsg_764_);
v_recoveredErrors_765_ = lean_ctor_get(v___x_761_, 5);
lean_inc_ref(v_recoveredErrors_765_);
lean_dec_ref(v___x_761_);
v___x_766_ = 1;
v_sz_767_ = lean_array_size(v_recoveredErrors_765_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_727_, v_recoveredErrors_765_, v_sz_767_, v___x_768_, v_fst_745_);
lean_dec_ref(v_recoveredErrors_765_);
v___x_790_ = lean_unbox(v_fst_741_);
if (v___x_790_ == 0)
{
v___y_771_ = v___x_750_;
goto v___jp_770_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_762_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_762_);
v___x_793_ = l_Lean_Syntax_isAntiquot(v___x_792_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
v___y_771_ = v___x_793_;
goto v___jp_770_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_errorMsg_764_);
lean_dec_ref(v_stxStack_762_);
lean_del_object(v___x_748_);
lean_del_object(v___x_743_);
lean_del_object(v___x_739_);
lean_dec(v_fst_737_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_769_);
lean_ctor_set(v___x_794_, 1, v_snd_746_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_fst_741_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_pos_763_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v_a_729_ = v___x_796_;
goto _start;
}
}
else
{
v___y_771_ = v___x_750_;
goto v___jp_770_;
}
}
v___jp_770_:
{
if (lean_obj_tag(v_errorMsg_764_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec(v_snd_746_);
lean_dec(v_fst_741_);
lean_dec(v_fst_737_);
lean_dec_ref(v_pmctx_728_);
lean_dec_ref(v_inputCtx_727_);
v___x_772_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_762_);
lean_dec_ref(v_stxStack_762_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_772_);
lean_ctor_set(v___x_748_, 0, v___x_769_);
v___x_774_ = v___x_748_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_782_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_box(v___y_771_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_774_);
lean_ctor_set(v___x_743_, 0, v___x_775_);
v___x_777_ = v___x_743_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_774_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_777_);
lean_ctor_set(v___x_739_, 0, v_pos_763_);
v___x_779_ = v___x_739_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_pos_763_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_val_783_; uint8_t v_decide_784_; 
lean_del_object(v___x_748_);
lean_del_object(v___x_743_);
lean_del_object(v___x_739_);
v_val_783_ = lean_ctor_get(v_errorMsg_764_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v_errorMsg_764_, 1);
v_decide_784_ = lean_nat_dec_eq(v_pos_763_, v_fst_737_);
lean_dec(v_fst_737_);
if (v_decide_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(0);
lean_inc(v_pos_763_);
lean_inc_ref(v_inputCtx_727_);
v___x_786_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_746_, v___x_766_, v_inputCtx_727_, v_pos_763_, v_stxStack_762_, v_val_783_, v___x_769_, v_fst_741_, v___y_771_, v___x_785_, v_pos_763_);
lean_dec(v_fst_741_);
v___y_731_ = v___x_786_;
goto v___jp_730_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_inc(v_pos_763_);
lean_inc_ref(v_pmctx_728_);
lean_inc_ref_n(v_inputCtx_727_, 2);
v___x_787_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_727_, v_pmctx_728_, v_pos_763_);
v___x_788_ = lean_box(0);
v___x_789_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_746_, v___x_766_, v_inputCtx_727_, v_pos_763_, v_stxStack_762_, v_val_783_, v___x_769_, v_fst_741_, v___y_771_, v___x_788_, v___x_787_);
lean_dec(v_fst_741_);
v___y_731_ = v___x_789_;
goto v___jp_730_;
}
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_snd_746_);
lean_dec_ref(v_pmctx_728_);
lean_inc(v_fst_737_);
v___x_798_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_727_, v_fst_737_);
lean_dec_ref(v_inputCtx_727_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_798_);
v___x_800_ = v___x_748_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_fst_745_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_807_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_800_);
v___x_802_ = v___x_743_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_741_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_802_);
v___x_804_ = v___x_739_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_fst_737_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_813_, lean_object* v_pmctx_814_, lean_object* v_mps_815_, lean_object* v_messages_816_){
_start:
{
lean_object* v_pos_817_; uint8_t v_recovering_818_; lean_object* v_leadingStartPos_x3f_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_860_; 
v_pos_817_ = lean_ctor_get(v_mps_815_, 0);
v_recovering_818_ = lean_ctor_get_uint8(v_mps_815_, sizeof(void*)*2);
v_leadingStartPos_x3f_819_ = lean_ctor_get(v_mps_815_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_mps_815_);
if (v_isSharedCheck_860_ == 0)
{
v___x_821_ = v_mps_815_;
v_isShared_822_ = v_isSharedCheck_860_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_leadingStartPos_x3f_819_);
lean_inc(v_pos_817_);
lean_dec(v_mps_815_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_860_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_stx_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_snd_829_; lean_object* v_snd_830_; lean_object* v_fst_831_; lean_object* v_fst_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_858_; 
v_stx_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_messages_816_);
lean_ctor_set(v___x_824_, 1, v_stx_823_);
v___x_825_ = lean_box(v_recovering_818_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_824_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_pos_817_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_813_, v_pmctx_814_, v___x_827_);
v_snd_829_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_snd_829_);
v_snd_830_ = lean_ctor_get(v_snd_829_, 1);
lean_inc(v_snd_830_);
v_fst_831_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_fst_831_);
lean_dec_ref(v___x_828_);
v_fst_832_ = lean_ctor_get(v_snd_829_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_snd_829_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_snd_829_, 1);
lean_dec(v_unused_859_);
v___x_834_ = v_snd_829_;
v_isShared_835_ = v_isSharedCheck_858_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_fst_832_);
lean_dec(v_snd_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_858_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_857_; 
v_fst_836_ = lean_ctor_get(v_snd_830_, 0);
v_snd_837_ = lean_ctor_get(v_snd_830_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_snd_830_);
if (v_isSharedCheck_857_ == 0)
{
v___x_839_ = v_snd_830_;
v_isShared_840_ = v_isSharedCheck_857_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v_snd_830_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_857_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_stx_842_; 
if (lean_obj_tag(v_leadingStartPos_x3f_819_) == 1)
{
lean_object* v_val_854_; lean_object* v___x_855_; lean_object* v_fst_856_; 
v_val_854_ = lean_ctor_get(v_leadingStartPos_x3f_819_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v_leadingStartPos_x3f_819_, 1);
v___x_855_ = l___private_Lean_Parser_Module_0__Lean_Parser_setLeadingStart(v_snd_837_, v_val_854_);
v_fst_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_fst_856_);
lean_dec_ref(v___x_855_);
v_stx_842_ = v_fst_856_;
goto v___jp_841_;
}
else
{
lean_dec(v_leadingStartPos_x3f_819_);
v_stx_842_ = v_snd_837_;
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_843_);
lean_ctor_set(v___x_821_, 0, v_fst_831_);
v___x_845_ = v___x_821_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_fst_831_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_853_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
uint8_t v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_unbox(v_fst_832_);
lean_dec(v_fst_832_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*2, v___x_846_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_fst_836_);
lean_ctor_set(v___x_839_, 0, v___x_845_);
v___x_848_ = v___x_839_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_fst_836_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_848_);
lean_ctor_set(v___x_834_, 0, v_stx_842_);
v___x_850_ = v___x_834_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_stx_842_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_861_, lean_object* v_pmctx_862_, lean_object* v_inst_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_861_, v_pmctx_862_, v_a_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_putStr_869_; lean_object* v___x_870_; 
v___x_868_ = lean_get_stdout();
v_putStr_869_ = lean_ctor_get(v___x_868_, 4);
lean_inc_ref(v_putStr_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = lean_apply_2(v_putStr_869_, v_s_866_, lean_box(0));
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_874_){
_start:
{
uint32_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = 10;
v___x_877_ = lean_string_push(v_s_874_, v___x_876_);
v___x_878_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___x_882_, lean_object* v_msg_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_Message_toString(v_msg_883_, v___x_882_);
v___x_886_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___x_887_, lean_object* v_msg_888_, lean_object* v___y_889_){
_start:
{
uint8_t v___x_1235__boxed_890_; lean_object* v_res_891_; 
v___x_1235__boxed_890_ = lean_unbox(v___x_887_);
v_res_891_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___x_1235__boxed_890_, v_msg_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_892_, lean_object* v_as_893_, size_t v_i_894_, size_t v_stop_895_, lean_object* v_b_896_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_eq(v_i_894_, v_stop_895_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_array_uget_borrowed(v_as_893_, v_i_894_);
lean_inc_ref(v_f_892_);
lean_inc(v___x_899_);
v___x_900_ = lean_apply_2(v_f_892_, v___x_899_, lean_box(0));
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; size_t v___x_902_; size_t v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_add(v_i_894_, v___x_902_);
v_i_894_ = v___x_903_;
v_b_896_ = v_a_901_;
goto _start;
}
else
{
lean_dec_ref(v_f_892_);
return v___x_900_;
}
}
else
{
lean_object* v___x_905_; 
lean_dec_ref(v_f_892_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v_b_896_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_906_, lean_object* v_as_907_, lean_object* v_i_908_, lean_object* v_stop_909_, lean_object* v_b_910_, lean_object* v___y_911_){
_start:
{
size_t v_i_boxed_912_; size_t v_stop_boxed_913_; lean_object* v_res_914_; 
v_i_boxed_912_ = lean_unbox_usize(v_i_908_);
lean_dec(v_i_908_);
v_stop_boxed_913_ = lean_unbox_usize(v_stop_909_);
lean_dec(v_stop_909_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_906_, v_as_907_, v_i_boxed_912_, v_stop_boxed_913_, v_b_910_);
lean_dec_ref(v_as_907_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_915_, lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_cs_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_932_; 
v_cs_918_ = lean_ctor_get(v_x_916_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_916_);
if (v_isSharedCheck_932_ == 0)
{
v___x_920_ = v_x_916_;
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_cs_918_);
lean_dec(v_x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_array_get_size(v_cs_918_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_nat_dec_lt(v___x_922_, v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_927_; 
lean_dec_ref(v_cs_918_);
lean_dec_ref(v_f_915_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_924_);
v___x_927_ = v___x_920_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_924_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
lean_del_object(v___x_920_);
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_923_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_915_, v_cs_918_, v___x_929_, v___x_930_, v___x_924_);
lean_dec_ref(v_cs_918_);
return v___x_931_;
}
}
}
else
{
lean_object* v_vs_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_vs_933_ = lean_ctor_get(v_x_916_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_916_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_x_916_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_vs_933_);
lean_dec(v_x_916_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get_size(v_vs_933_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_940_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_vs_933_);
lean_dec_ref(v_f_915_);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
lean_ctor_set(v___x_935_, 0, v___x_939_);
v___x_942_ = v___x_935_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_939_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_935_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_of_nat(v___x_938_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_915_, v_vs_933_, v___x_944_, v___x_945_, v___x_939_);
lean_dec_ref(v_vs_933_);
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_948_, lean_object* v_as_949_, size_t v_i_950_, size_t v_stop_951_, lean_object* v_b_952_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_eq(v_i_950_, v_stop_951_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_array_uget_borrowed(v_as_949_, v_i_950_);
lean_inc(v___x_955_);
lean_inc_ref(v_f_948_);
v___x_956_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_948_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; size_t v___x_958_; size_t v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_950_, v___x_958_);
v_i_950_ = v___x_959_;
v_b_952_ = v_a_957_;
goto _start;
}
else
{
lean_dec_ref(v_f_948_);
return v___x_956_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec_ref(v_f_948_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_b_952_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_962_, lean_object* v_as_963_, lean_object* v_i_964_, lean_object* v_stop_965_, lean_object* v_b_966_, lean_object* v___y_967_){
_start:
{
size_t v_i_boxed_968_; size_t v_stop_boxed_969_; lean_object* v_res_970_; 
v_i_boxed_968_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_stop_boxed_969_ = lean_unbox_usize(v_stop_965_);
lean_dec(v_stop_965_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_962_, v_as_963_, v_i_boxed_968_, v_stop_boxed_969_, v_b_966_);
lean_dec_ref(v_as_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_971_, lean_object* v_x_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_971_, v_x_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_975_, lean_object* v_t_976_){
_start:
{
lean_object* v_root_978_; lean_object* v_tail_979_; lean_object* v___x_980_; 
v_root_978_ = lean_ctor_get(v_t_976_, 0);
lean_inc_ref(v_root_978_);
v_tail_979_ = lean_ctor_get(v_t_976_, 1);
lean_inc_ref(v_tail_979_);
lean_dec_ref(v_t_976_);
lean_inc_ref(v_f_975_);
v___x_980_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_975_, v_root_978_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_994_; 
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_995_);
v___x_982_ = v___x_980_;
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
else
{
lean_dec(v___x_980_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_size(v_tail_979_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_nat_dec_lt(v___x_984_, v___x_985_);
if (v___x_987_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_tail_979_);
lean_dec_ref(v_f_975_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_986_);
v___x_989_ = v___x_982_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_986_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_982_);
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_985_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_975_, v_tail_979_, v___x_991_, v___x_992_, v___x_986_);
lean_dec_ref(v_tail_979_);
return v___x_993_;
}
}
}
else
{
lean_dec_ref(v_tail_979_);
lean_dec_ref(v_f_975_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_996_, lean_object* v_t_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_996_, v_t_997_);
return v_res_999_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_1001_, lean_object* v_x_1002_, size_t v_x_1003_, size_t v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_object* v_cs_1006_; lean_object* v___x_1007_; size_t v___x_1008_; lean_object* v_j_1009_; lean_object* v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v_cs_1006_ = lean_ctor_get(v_x_1002_, 0);
lean_inc_ref(v_cs_1006_);
lean_dec_ref_known(v_x_1002_, 1);
v___x_1007_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_1008_ = lean_usize_shift_right(v_x_1003_, v_x_1004_);
v_j_1009_ = lean_usize_to_nat(v___x_1008_);
v___x_1010_ = lean_array_get_borrowed(v___x_1007_, v_cs_1006_, v_j_1009_);
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_shift_left(v___x_1011_, v_x_1004_);
v___x_1013_ = lean_usize_sub(v___x_1012_, v___x_1011_);
v___x_1014_ = lean_usize_land(v_x_1003_, v___x_1013_);
v___x_1015_ = ((size_t)5ULL);
v___x_1016_ = lean_usize_sub(v_x_1004_, v___x_1015_);
lean_inc(v___x_1010_);
lean_inc_ref(v_f_1001_);
v___x_1017_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1001_, v___x_1010_, v___x_1014_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1032_; 
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1033_);
v___x_1019_ = v___x_1017_;
v_isShared_1020_ = v_isSharedCheck_1032_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v___x_1017_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1032_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_add(v_j_1009_, v___x_1021_);
lean_dec(v_j_1009_);
v___x_1023_ = lean_array_get_size(v_cs_1006_);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1027_; 
lean_dec(v___x_1022_);
lean_dec_ref(v_cs_1006_);
lean_dec_ref(v_f_1001_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1024_);
v___x_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
lean_del_object(v___x_1019_);
v___x_1029_ = lean_usize_of_nat(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1030_ = lean_usize_of_nat(v___x_1023_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1001_, v_cs_1006_, v___x_1029_, v___x_1030_, v___x_1024_);
lean_dec_ref(v_cs_1006_);
return v___x_1031_;
}
}
}
else
{
lean_dec(v_j_1009_);
lean_dec_ref(v_cs_1006_);
lean_dec_ref(v_f_1001_);
return v___x_1017_;
}
}
else
{
lean_object* v_vs_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1048_; 
v_vs_1034_ = lean_ctor_get(v_x_1002_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1002_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1036_ = v_x_1002_;
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_vs_1034_);
lean_dec(v_x_1002_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1038_ = lean_usize_to_nat(v_x_1003_);
v___x_1039_ = lean_array_get_size(v_vs_1034_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_nat_dec_lt(v___x_1038_, v___x_1039_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1043_; 
lean_dec(v___x_1038_);
lean_dec_ref(v_vs_1034_);
lean_dec_ref(v_f_1001_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1043_ = v___x_1036_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
else
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1036_);
v___x_1045_ = lean_usize_of_nat(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1046_ = lean_usize_of_nat(v___x_1039_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1001_, v_vs_1034_, v___x_1045_, v___x_1046_, v___x_1040_);
lean_dec_ref(v_vs_1034_);
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_x_1391__boxed_1054_; size_t v_x_1392__boxed_1055_; lean_object* v_res_1056_; 
v_x_1391__boxed_1054_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_x_1392__boxed_1055_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1049_, v_x_1050_, v_x_1391__boxed_1054_, v_x_1392__boxed_1055_);
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
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1069_, 0);
lean_dec(v_unused_1083_);
v___x_1071_ = v___x_1069_;
v_isShared_1072_ = v_isSharedCheck_1082_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v___x_1069_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1082_;
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
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
lean_del_object(v___x_1071_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = lean_usize_of_nat(v___x_1073_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1079_, v___x_1080_, v___x_1074_);
lean_dec_ref(v_tail_1064_);
return v___x_1081_;
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
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
lean_dec_ref(v_root_1063_);
v___x_1084_ = lean_nat_sub(v_start_1059_, v_tailOff_1066_);
lean_dec(v_tailOff_1066_);
v___x_1085_ = lean_array_get_size(v_tail_1064_);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_nat_dec_lt(v___x_1084_, v___x_1085_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v___x_1084_);
lean_dec_ref(v_tail_1064_);
lean_dec_ref(v_f_1057_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
return v___x_1088_;
}
else
{
size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_usize_of_nat(v___x_1084_);
lean_dec(v___x_1084_);
v___x_1090_ = lean_usize_of_nat(v___x_1085_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1057_, v_tail_1064_, v___x_1089_, v___x_1090_, v___x_1086_);
lean_dec_ref(v_tail_1064_);
return v___x_1091_;
}
}
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1057_, v_t_1058_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1093_, lean_object* v_t_1094_, lean_object* v_start_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1093_, v_t_1094_, v_start_1095_);
lean_dec(v_start_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1098_, lean_object* v_f_1099_){
_start:
{
lean_object* v_unreported_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_unreported_1101_ = lean_ctor_get(v_log_1098_, 1);
lean_inc_ref(v_unreported_1101_);
lean_dec_ref(v_log_1098_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1099_, v_unreported_1101_, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1104_, lean_object* v_f_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1104_, v_f_1105_);
return v_res_1107_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1));
v___x_1113_ = lean_mk_io_user_error(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1114_, lean_object* v_inputCtx_1115_, lean_object* v_state_1116_, lean_object* v_msgs_1117_, lean_object* v_stxs_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_snd_1125_; lean_object* v_fst_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; uint8_t v___x_1129_; 
v___x_1120_ = l_Lean_Options_empty;
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_box(0);
lean_inc_ref(v_env_1114_);
v___x_1123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1123_, 0, v_env_1114_);
lean_ctor_set(v___x_1123_, 1, v___x_1120_);
lean_ctor_set(v___x_1123_, 2, v___x_1121_);
lean_ctor_set(v___x_1123_, 3, v___x_1122_);
lean_inc_ref(v_inputCtx_1115_);
v___x_1124_ = l_Lean_Parser_parseCommand(v_inputCtx_1115_, v___x_1123_, v_state_1116_, v_msgs_1117_);
v_snd_1125_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_snd_1125_);
v_fst_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_n(v_fst_1126_, 2);
lean_dec_ref(v___x_1124_);
v_fst_1127_ = lean_ctor_get(v_snd_1125_, 0);
lean_inc(v_fst_1127_);
v_snd_1128_ = lean_ctor_get(v_snd_1125_, 1);
lean_inc(v_snd_1128_);
lean_dec(v_snd_1125_);
v___x_1129_ = l_Lean_Parser_isTerminalCommand(v_fst_1126_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_array_push(v_stxs_1118_, v_fst_1126_);
v_state_1116_ = v_fst_1127_;
v_msgs_1117_ = v_snd_1128_;
v_stxs_1118_ = v___x_1130_;
goto _start;
}
else
{
uint8_t v___x_1132_; 
lean_dec(v_fst_1127_);
lean_dec_ref(v_inputCtx_1115_);
lean_dec_ref(v_env_1114_);
v___x_1132_ = l_Lean_MessageLog_hasUnreported(v_snd_1128_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_snd_1128_);
v___x_1133_ = lean_array_push(v_stxs_1118_, v_fst_1126_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___f_1135_; lean_object* v___x_1136_; 
lean_dec(v_fst_1126_);
lean_dec_ref(v_stxs_1118_);
v___f_1135_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1136_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1128_, v___f_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1136_, 0);
lean_dec(v_unused_1145_);
v___x_1138_ = v___x_1136_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v___x_1136_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2);
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 1);
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1136_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1136_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1154_, lean_object* v_inputCtx_1155_, lean_object* v_state_1156_, lean_object* v_msgs_1157_, lean_object* v_stxs_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1154_, v_inputCtx_1155_, v_state_1156_, v_msgs_1157_, v_stxs_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1161_, lean_object* v_inputCtx_1162_, lean_object* v_s_1163_, lean_object* v_msgs_1164_, lean_object* v_stxs_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1161_, v_inputCtx_1162_, v_s_1163_, v_msgs_1164_, v_stxs_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1168_, lean_object* v_inputCtx_1169_, lean_object* v_s_1170_, lean_object* v_msgs_1171_, lean_object* v_stxs_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Parser_testParseModuleAux(v_env_1168_, v_inputCtx_1169_, v_s_1170_, v_msgs_1171_, v_stxs_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1183_, lean_object* v_fname_1184_, lean_object* v_contents_1185_){
_start:
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v_inputCtx_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1187_ = 1;
v___x_1188_ = lean_string_utf8_byte_size(v_contents_1185_);
v_inputCtx_1189_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1185_, v_fname_1184_, v___x_1187_, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inputCtx_1189_);
v___x_1191_ = l_Lean_Parser_parseHeader(v_inputCtx_1189_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_snd_1193_; lean_object* v_fst_1194_; lean_object* v_fst_1195_; lean_object* v_snd_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v_snd_1193_ = lean_ctor_get(v_a_1192_, 1);
lean_inc(v_snd_1193_);
v_fst_1194_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_fst_1194_);
lean_dec(v_a_1192_);
v_fst_1195_ = lean_ctor_get(v_snd_1193_, 0);
lean_inc(v_fst_1195_);
v_snd_1196_ = lean_ctor_get(v_snd_1193_, 1);
lean_inc(v_snd_1196_);
lean_dec(v_snd_1193_);
v___x_1197_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1198_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1183_, v_inputCtx_1189_, v_fst_1195_, v_snd_1196_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1214_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1203_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1204_ = l_Lean_mkListNode(v_a_1199_);
v___x_1205_ = lean_unsigned_to_nat(2u);
v___x_1206_ = lean_mk_empty_array_with_capacity(v___x_1205_);
v___x_1207_ = lean_array_push(v___x_1206_, v_fst_1194_);
v___x_1208_ = lean_array_push(v___x_1207_, v___x_1204_);
v___x_1209_ = lean_box(2);
v___x_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1203_);
lean_ctor_set(v___x_1210_, 2, v___x_1208_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1210_);
v___x_1212_ = v___x_1201_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_fst_1194_);
v_a_1215_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1198_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1198_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_inputCtx_1189_);
lean_dec_ref(v_env_1183_);
v_a_1223_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1191_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1191_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1231_, lean_object* v_fname_1232_, lean_object* v_contents_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Parser_testParseModule(v_env_1231_, v_fname_1232_, v_contents_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1236_, lean_object* v_fname_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_IO_FS_readFile(v_fname_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_Lean_Parser_testParseModule(v_env_1236_, v_fname_1237_, v_a_1240_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_fname_1237_);
lean_dec_ref(v_env_1236_);
v_a_1242_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1239_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1239_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1250_, lean_object* v_fname_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Parser_testParseFile(v_env_1250_, v_fname_1251_);
return v_res_1253_;
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
