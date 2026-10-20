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
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
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
v_stop_45_ = lean_ctor_get(v___x_43_, 2);
v___x_46_ = lean_nat_sub(v_stop_45_, v_start_44_);
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
v___x_74_ = l_Lean_Parser_Error_toString(v___y_68_);
v___x_75_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = l_Lean_MessageData_ofFormat(v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_77_, 0, v___y_67_);
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
v___y_67_ = v_fileName_82_;
v___y_68_ = v_e_81_;
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
v___y_67_ = v_fileName_82_;
v___y_68_ = v_e_81_;
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
v_decide_106_ = lean_nat_dec_eq(v_stopPos_105_, v___y_98_);
lean_dec(v_stopPos_105_);
if (v_decide_106_ == 0)
{
lean_dec(v_startPos_104_);
v_pos_79_ = v___y_98_;
v_endPos_x3f_80_ = v___y_99_;
v_e_81_ = v_e_101_;
goto v___jp_78_;
}
else
{
lean_dec(v___y_98_);
v_pos_79_ = v_startPos_104_;
v_endPos_x3f_80_ = v___y_99_;
v_e_81_ = v_e_101_;
goto v___jp_78_;
}
}
else
{
lean_dec(v___x_102_);
v_pos_79_ = v___y_98_;
v_endPos_x3f_80_ = v___y_99_;
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
v___y_98_ = v_pos_108_;
v___y_99_ = v_endPos_x3f_109_;
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
v___y_98_ = v_pos_108_;
v___y_99_ = v_endPos_x3f_109_;
v___y_100_ = v___x_115_;
goto v___jp_97_;
}
default: 
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4));
v___y_98_ = v_pos_108_;
v___y_99_ = v_endPos_x3f_109_;
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* v_x_163_, lean_object* v_x_164_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_171_, v_x_172_);
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
v___x_212_ = l_Lean_FileMap_toPosition(v___y_208_, v___y_211_);
lean_dec(v___y_211_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = 2;
v___x_215_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_216_, 0, v___y_209_);
lean_ctor_set(v___x_216_, 1, v___y_210_);
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
v___y_208_ = v_fileMap_220_;
v___y_209_ = v_fileName_219_;
v___y_210_ = v___x_221_;
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
v___y_208_ = v_fileMap_220_;
v___y_209_ = v_fileName_219_;
v___y_210_ = v___x_221_;
v___y_211_ = v_val_223_;
goto v___jp_207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_227_, lean_object* v_inputCtx_228_, lean_object* v_ref_229_, lean_object* v_msg_230_){
_start:
{
uint8_t v___x_3135__boxed_231_; lean_object* v_res_232_; 
v___x_3135__boxed_231_ = lean_unbox(v___x_227_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_3135__boxed_231_, v_inputCtx_228_, v_ref_229_, v_msg_230_);
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12));
v___x_256_ = l_Lean_MessageData_ofFormat(v___x_255_);
return v___x_256_;
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
lean_object* v___y_296_; lean_object* v_messages_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v_messages_305_; lean_object* v___x_310_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v_allTk_x3f_314_; lean_object* v___x_345_; lean_object* v___y_347_; lean_object* v_metaTk_x3f_348_; lean_object* v_pubTk_x3f_360_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_370_ = l_Lean_Syntax_getArg(v_a_293_, v___x_310_);
v___x_371_ = l_Lean_Syntax_isNone(v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; 
lean_inc(v___x_370_);
v___x_372_ = l_Lean_Syntax_matchesNull(v___x_370_, v___x_345_);
if (v___x_372_ == 0)
{
lean_dec(v___x_370_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = l_Lean_Syntax_getArg(v___x_370_, v___x_310_);
lean_dec(v___x_370_);
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22));
lean_inc(v___x_373_);
v___x_375_ = l_Lean_Syntax_isOfKind(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec(v___x_373_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Lean_Syntax_getArg(v___x_373_, v___x_310_);
lean_dec(v___x_373_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v_pubTk_x3f_360_ = v___x_377_;
goto v___jp_359_;
}
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v___x_370_);
v___x_378_ = lean_box(0);
v_pubTk_x3f_360_ = v___x_378_;
goto v___jp_359_;
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
v___jp_311_:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(5u);
v___x_316_ = l_Lean_Syntax_getArg(v_a_293_, v___x_315_);
v___x_317_ = l_Lean_Syntax_matchesNull(v___x_316_, v___x_310_);
if (v___x_317_ == 0)
{
lean_dec(v_allTk_x3f_314_);
lean_dec(v___y_313_);
lean_dec(v___y_312_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
if (lean_obj_tag(v_moduleTk_x3f_279_) == 0)
{
if (lean_obj_tag(v___y_312_) == 1)
{
lean_object* v_val_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_val_318_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___y_312_, 1);
v___x_319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13);
lean_inc_ref(v_inputCtx_278_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_318_, v___x_319_);
lean_dec(v_val_318_);
v___x_321_ = l_Lean_MessageLog_add(v___x_320_, v_b_283_);
v___y_303_ = v_allTk_x3f_314_;
v___y_304_ = v___y_313_;
v_messages_305_ = v___x_321_;
goto v___jp_302_;
}
else
{
lean_dec(v___y_312_);
v___y_303_ = v_allTk_x3f_314_;
v___y_304_ = v___y_313_;
v_messages_305_ = v_b_283_;
goto v___jp_302_;
}
}
else
{
lean_dec(v___y_313_);
if (lean_obj_tag(v_allTk_x3f_314_) == 1)
{
if (lean_obj_tag(v___y_312_) == 0)
{
lean_dec_ref_known(v_allTk_x3f_314_, 1);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v_val_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_343_; 
v_val_322_ = lean_ctor_get(v_allTk_x3f_314_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_allTk_x3f_314_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v___y_312_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___y_312_, 0);
lean_dec(v_unused_344_);
v___x_324_ = v___y_312_;
v_isShared_325_ = v_isSharedCheck_343_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___y_312_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_343_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_326_ = lean_unsigned_to_nat(4u);
v___x_327_ = l_Lean_Syntax_getArg(v_a_293_, v___x_326_);
v___x_328_ = l_Lean_TSyntax_getId(v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14));
v___x_330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_328_, v___x_317_);
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_string_append(v___x_333_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 3);
lean_ctor_set(v___x_324_, 0, v___x_336_);
v___x_338_ = v___x_324_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Lean_MessageData_ofFormat(v___x_338_);
lean_inc_ref(v_inputCtx_278_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_294_, v_inputCtx_278_, v_val_322_, v___x_339_);
lean_dec(v_val_322_);
v___x_341_ = l_Lean_MessageLog_add(v___x_340_, v_b_283_);
v_a_286_ = v___x_341_;
goto v___jp_285_;
}
}
}
}
else
{
lean_dec(v_allTk_x3f_314_);
lean_dec(v___y_312_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
}
}
}
v___jp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(3u);
v___x_350_ = l_Lean_Syntax_getArg(v_a_293_, v___x_349_);
v___x_351_ = l_Lean_Syntax_isNone(v___x_350_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
lean_inc(v___x_350_);
v___x_352_ = l_Lean_Syntax_matchesNull(v___x_350_, v___x_345_);
if (v___x_352_ == 0)
{
lean_dec(v___x_350_);
lean_dec(v_metaTk_x3f_348_);
lean_dec(v___y_347_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_353_ = l_Lean_Syntax_getArg(v___x_350_, v___x_310_);
lean_dec(v___x_350_);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18));
lean_inc(v___x_353_);
v___x_355_ = l_Lean_Syntax_isOfKind(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v___x_353_);
lean_dec(v_metaTk_x3f_348_);
lean_dec(v___y_347_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Lean_Syntax_getArg(v___x_353_, v___x_310_);
lean_dec(v___x_353_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___y_312_ = v___y_347_;
v___y_313_ = v_metaTk_x3f_348_;
v_allTk_x3f_314_ = v___x_357_;
goto v___jp_311_;
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v___x_350_);
v___x_358_ = lean_box(0);
v___y_312_ = v___y_347_;
v___y_313_ = v_metaTk_x3f_348_;
v_allTk_x3f_314_ = v___x_358_;
goto v___jp_311_;
}
}
v___jp_359_:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = l_Lean_Syntax_getArg(v_a_293_, v___x_345_);
v___x_362_ = l_Lean_Syntax_isNone(v___x_361_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
lean_inc(v___x_361_);
v___x_363_ = l_Lean_Syntax_matchesNull(v___x_361_, v___x_345_);
if (v___x_363_ == 0)
{
lean_dec(v___x_361_);
lean_dec(v_pubTk_x3f_360_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = l_Lean_Syntax_getArg(v___x_361_, v___x_310_);
lean_dec(v___x_361_);
v___x_365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20));
lean_inc(v___x_364_);
v___x_366_ = l_Lean_Syntax_isOfKind(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_dec(v___x_364_);
lean_dec(v_pubTk_x3f_360_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = l_Lean_Syntax_getArg(v___x_364_, v___x_310_);
lean_dec(v___x_364_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
v___y_347_ = v_pubTk_x3f_360_;
v_metaTk_x3f_348_ = v___x_368_;
goto v___jp_346_;
}
}
}
else
{
lean_object* v___x_369_; 
lean_dec(v___x_361_);
v___x_369_ = lean_box(0);
v___y_347_ = v_pubTk_x3f_360_;
v_metaTk_x3f_348_ = v___x_369_;
goto v___jp_346_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* v_inputCtx_379_, lean_object* v_moduleTk_x3f_380_, lean_object* v_as_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_){
_start:
{
size_t v_sz_boxed_386_; size_t v_i_boxed_387_; lean_object* v_res_388_; 
v_sz_boxed_386_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_387_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_379_, v_moduleTk_x3f_380_, v_as_381_, v_sz_boxed_386_, v_i_boxed_387_, v_b_384_);
lean_dec_ref(v_as_381_);
lean_dec(v_moduleTk_x3f_380_);
return v_res_388_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(32u);
v___x_392_ = lean_mk_empty_array_with_capacity(v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3(void){
_start:
{
size_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((size_t)5ULL);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_unsigned_to_nat(32u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__2, &l_Lean_Parser_parseHeader___closed__2_once, _init_l_Lean_Parser_parseHeader___closed__2);
v___x_399_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_395_);
lean_ctor_set(v___x_399_, 3, v___x_395_);
lean_ctor_set_usize(v___x_399_, 4, v___x_394_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_NameSet_empty;
v___x_401_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__3, &l_Lean_Parser_parseHeader___closed__3_once, _init_l_Lean_Parser_parseHeader___closed__3);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_ctor_set(v___x_402_, 2, v___x_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* v_inputCtx_415_){
_start:
{
lean_object* v___x_417_; uint32_t v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = 0;
v___x_419_ = l_Lean_mkEmptyEnvironment(v___x_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_539_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_539_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_539_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_539_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_fn_425_; lean_object* v_inputString_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_stxStack_437_; lean_object* v_pos_438_; lean_object* v_errorMsg_439_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; uint8_t v___y_444_; uint8_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_459_; lean_object* v_messages_460_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; size_t v___y_474_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; size_t v___y_495_; lean_object* v_moduleTk_x3f_496_; lean_object* v___y_506_; uint8_t v___x_536_; 
v___x_424_ = l_Lean_Parser_Module_header;
v_fn_425_ = lean_ctor_get(v___x_424_, 1);
v_inputString_426_ = lean_ctor_get(v_inputCtx_415_, 0);
lean_inc(v_a_420_);
v___x_427_ = l_Lean_Parser_getTokenTable(v_a_420_);
v___x_428_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_425_);
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_429_, 0, v___x_428_);
lean_closure_set(v___x_429_, 1, v_fn_425_);
v___x_430_ = l_Lean_Parser_Module_updateTokens(v___x_427_);
v___x_431_ = l_Lean_Options_empty;
v___x_432_ = lean_box(0);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_434_, 0, v_a_420_);
lean_ctor_set(v___x_434_, 1, v___x_431_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
v___x_435_ = l_Lean_Parser_mkParserState(v_inputString_426_);
lean_inc_ref(v_inputCtx_415_);
v___x_436_ = l_Lean_Parser_ParserFn_run(v___x_429_, v_inputCtx_415_, v___x_434_, v___x_430_, v___x_435_);
v_stxStack_437_ = lean_ctor_get(v___x_436_, 0);
v_pos_438_ = lean_ctor_get(v___x_436_, 2);
lean_inc(v_pos_438_);
v_errorMsg_439_ = lean_ctor_get(v___x_436_, 4);
lean_inc(v_errorMsg_439_);
v___x_536_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_437_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_437_);
v___y_506_ = v___x_537_;
goto v___jp_505_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
v___y_506_ = v___x_538_;
goto v___jp_505_;
}
v___jp_440_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_445_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_445_, 0, v_pos_438_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___y_441_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1 + 1, v___y_444_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___y_442_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___y_443_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_447_);
v___x_449_ = v___x_422_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
v___jp_451_:
{
if (v___y_452_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 1;
v___y_441_ = v___y_455_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_454_;
v___y_444_ = v___x_456_;
goto v___jp_440_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
v___y_441_ = v___y_455_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_454_;
v___y_444_ = v___x_457_;
goto v___jp_440_;
}
}
v___jp_458_:
{
lean_object* v___x_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_461_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_459_);
v_fst_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v___x_461_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v___x_461_);
v___x_464_ = lean_box(0);
v___x_465_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_439_, v___x_464_);
lean_dec(v_errorMsg_439_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 1;
v___x_467_ = lean_unbox(v_snd_463_);
lean_dec(v_snd_463_);
v___y_452_ = v___x_467_;
v___y_453_ = v_messages_460_;
v___y_454_ = v_fst_462_;
v___y_455_ = v___x_466_;
goto v___jp_451_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 0;
v___x_469_ = lean_unbox(v_snd_463_);
lean_dec(v_snd_463_);
v___y_452_ = v___x_469_;
v___y_453_ = v_messages_460_;
v___y_454_ = v_fst_462_;
v___y_455_ = v___x_468_;
goto v___jp_451_;
}
}
v___jp_470_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; size_t v_sz_478_; lean_object* v___x_479_; 
v___x_475_ = lean_unsigned_to_nat(2u);
v___x_476_ = l_Lean_Syntax_getArg(v___y_473_, v___x_475_);
v___x_477_ = l_Lean_Syntax_getArgs(v___x_476_);
lean_dec(v___x_476_);
v_sz_478_ = lean_array_size(v___x_477_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_415_, v___y_472_, v___x_477_, v_sz_478_, v___y_474_, v___y_471_);
lean_dec_ref(v___x_477_);
lean_dec(v___y_472_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v___y_459_ = v___y_473_;
v_messages_460_ = v_a_480_;
goto v___jp_458_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___y_473_);
lean_dec(v_errorMsg_439_);
lean_dec(v_pos_438_);
lean_del_object(v___x_422_);
v_a_481_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
v___jp_489_:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = l_Lean_Syntax_getArg(v___y_492_, v___x_497_);
v___x_499_ = l_Lean_Syntax_isNone(v___x_498_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; 
lean_inc(v___x_498_);
v___x_500_ = l_Lean_Syntax_matchesNull(v___x_498_, v___x_497_);
if (v___x_500_ == 0)
{
lean_dec(v___x_498_);
lean_dec(v_moduleTk_x3f_496_);
lean_dec_ref(v_inputCtx_415_);
v___y_459_ = v___y_492_;
v_messages_460_ = v___y_491_;
goto v___jp_458_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_501_ = l_Lean_Syntax_getArg(v___x_498_, v___x_417_);
lean_dec(v___x_498_);
v___x_502_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_490_);
lean_inc_ref(v___y_493_);
lean_inc_ref(v___y_494_);
v___x_503_ = l_Lean_Name_mkStr4(v___y_494_, v___y_493_, v___y_490_, v___x_502_);
v___x_504_ = l_Lean_Syntax_isOfKind(v___x_501_, v___x_503_);
lean_dec(v___x_503_);
if (v___x_504_ == 0)
{
lean_dec(v_moduleTk_x3f_496_);
lean_dec_ref(v_inputCtx_415_);
v___y_459_ = v___y_492_;
v_messages_460_ = v___y_491_;
goto v___jp_458_;
}
else
{
v___y_471_ = v___y_491_;
v___y_472_ = v_moduleTk_x3f_496_;
v___y_473_ = v___y_492_;
v___y_474_ = v___y_495_;
goto v___jp_470_;
}
}
}
else
{
lean_dec(v___x_498_);
v___y_471_ = v___y_491_;
v___y_472_ = v_moduleTk_x3f_496_;
v___y_473_ = v___y_492_;
v___y_474_ = v___y_495_;
goto v___jp_470_;
}
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_507_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_508_ = l_Lean_Parser_ParserState_allErrors(v___x_436_);
v_sz_509_ = lean_array_size(v___x_508_);
v___x_510_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_415_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_415_, v___x_508_, v_sz_509_, v___x_510_, v___x_507_);
lean_dec_ref(v___x_508_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_516_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_506_);
v___x_517_ = l_Lean_Syntax_isOfKind(v___y_506_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_inputCtx_415_);
v___y_459_ = v___y_506_;
v_messages_460_ = v_a_512_;
goto v___jp_458_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = l_Lean_Syntax_getArg(v___y_506_, v___x_417_);
v___x_519_ = l_Lean_Syntax_isNone(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_518_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_518_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v___x_518_);
lean_dec_ref(v_inputCtx_415_);
v___y_459_ = v___y_506_;
v_messages_460_ = v_a_512_;
goto v___jp_458_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = l_Lean_Syntax_getArg(v___x_518_, v___x_417_);
lean_dec(v___x_518_);
v___x_523_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_522_);
v___x_524_ = l_Lean_Syntax_isOfKind(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_dec(v___x_522_);
lean_dec_ref(v_inputCtx_415_);
v___y_459_ = v___y_506_;
v_messages_460_ = v_a_512_;
goto v___jp_458_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = l_Lean_Syntax_getArg(v___x_522_, v___x_417_);
lean_dec(v___x_522_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___y_490_ = v___x_515_;
v___y_491_ = v_a_512_;
v___y_492_ = v___y_506_;
v___y_493_ = v___x_514_;
v___y_494_ = v___x_513_;
v___y_495_ = v___x_510_;
v_moduleTk_x3f_496_ = v___x_526_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v___x_518_);
v___x_527_ = lean_box(0);
v___y_490_ = v___x_515_;
v___y_491_ = v_a_512_;
v___y_492_ = v___y_506_;
v___y_493_ = v___x_514_;
v___y_494_ = v___x_513_;
v___y_495_ = v___x_510_;
v_moduleTk_x3f_496_ = v___x_527_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v___y_506_);
lean_dec(v_errorMsg_439_);
lean_dec(v_pos_438_);
lean_del_object(v___x_422_);
lean_dec_ref(v_inputCtx_415_);
v_a_528_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_511_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_511_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_inputCtx_415_);
v_a_540_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_419_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_419_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Parser_parseHeader(v_inputCtx_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_558_, lean_object* v_pos_559_){
_start:
{
lean_object* v___y_561_; lean_object* v_inputString_571_; lean_object* v_endPos_572_; uint8_t v___x_573_; 
v_inputString_571_ = lean_ctor_get(v_inputCtx_558_, 0);
v_endPos_572_ = lean_ctor_get(v_inputCtx_558_, 3);
v___x_573_ = lean_nat_dec_le(v_pos_559_, v_endPos_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_inc(v_endPos_572_);
lean_inc(v_pos_559_);
lean_inc_ref(v_inputString_571_);
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v_inputString_571_);
lean_ctor_set(v___x_574_, 1, v_pos_559_);
lean_ctor_set(v___x_574_, 2, v_endPos_572_);
v___y_561_ = v___x_574_;
goto v___jp_560_;
}
else
{
lean_object* v___x_575_; 
lean_inc_n(v_pos_559_, 2);
lean_inc_ref(v_inputString_571_);
v___x_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_575_, 0, v_inputString_571_);
lean_ctor_set(v___x_575_, 1, v_pos_559_);
lean_ctor_set(v___x_575_, 2, v_pos_559_);
v___y_561_ = v___x_575_;
goto v___jp_560_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_atom_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_inc(v_pos_559_);
lean_inc_ref(v___y_561_);
v___x_562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_562_, 0, v___y_561_);
lean_ctor_set(v___x_562_, 1, v_pos_559_);
lean_ctor_set(v___x_562_, 2, v___y_561_);
lean_ctor_set(v___x_562_, 3, v_pos_559_);
v___x_563_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_564_, 0, v___x_562_);
lean_ctor_set(v_atom_564_, 1, v___x_563_);
v___x_565_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_array_push(v___x_567_, v_atom_564_);
v___x_569_ = lean_box(2);
v___x_570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_565_);
lean_ctor_set(v___x_570_, 2, v___x_568_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_576_, lean_object* v_pos_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_576_, v_pos_577_);
lean_dec_ref(v_inputCtx_576_);
return v_res_578_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_590_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_590_);
v___x_592_ = l_Lean_Syntax_isOfKind(v_s_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_590_);
v___x_594_ = l_Lean_Syntax_isOfKind(v_s_590_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_596_ = l_Lean_Syntax_isOfKind(v_s_590_, v___x_595_);
return v___x_596_;
}
else
{
lean_dec(v_s_590_);
return v___x_594_;
}
}
else
{
lean_dec(v_s_590_);
return v___x_592_;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_604_, lean_object* v_pmctx_605_, lean_object* v_pos_606_){
_start:
{
lean_object* v_inputString_607_; lean_object* v_env_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_s_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_s_617_; lean_object* v_errorMsg_618_; 
v_inputString_607_ = lean_ctor_get(v_inputCtx_604_, 0);
v_env_608_ = lean_ctor_get(v_pmctx_605_, 0);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_611_ = l_Lean_Parser_SyntaxStack_empty;
v___x_612_ = l_Lean_Parser_initCacheForInput(v_inputString_607_);
v___x_613_ = lean_box(0);
lean_inc(v_pos_606_);
v_s_614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_614_, 0, v___x_611_);
lean_ctor_set(v_s_614_, 1, v___x_609_);
lean_ctor_set(v_s_614_, 2, v_pos_606_);
lean_ctor_set(v_s_614_, 3, v___x_612_);
lean_ctor_set(v_s_614_, 4, v___x_613_);
lean_ctor_set(v_s_614_, 5, v___x_610_);
v___x_615_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_608_);
v___x_616_ = l_Lean_Parser_getTokenTable(v_env_608_);
v_s_617_ = l_Lean_Parser_ParserFn_run(v___x_615_, v_inputCtx_604_, v_pmctx_605_, v___x_616_, v_s_614_);
v_errorMsg_618_ = lean_ctor_get(v_s_617_, 4);
if (lean_obj_tag(v_errorMsg_618_) == 0)
{
lean_object* v_pos_619_; 
lean_dec(v_pos_606_);
v_pos_619_ = lean_ctor_get(v_s_617_, 2);
lean_inc(v_pos_619_);
lean_dec_ref(v_s_617_);
return v_pos_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_s_617_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_pos_606_, v___x_620_);
lean_dec(v_pos_606_);
return v___x_621_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_627_ = l_Lean_Parser_categoryParser(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_629_ = l_Lean_Parser_withPosition(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_632_; lean_object* v_fn_633_; lean_object* v___x_634_; 
v___x_632_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc_ref(v_fn_633_);
v___x_634_ = lean_apply_2(v_fn_633_, v_a_630_, v_a_631_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_635_, lean_object* v_as_636_, size_t v_sz_637_, size_t v_i_638_, lean_object* v_b_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_638_, v_sz_637_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_inputCtx_635_);
return v_b_639_;
}
else
{
lean_object* v_a_641_; lean_object* v_snd_642_; lean_object* v_fst_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; 
v_a_641_ = lean_array_uget_borrowed(v_as_636_, v_i_638_);
v_snd_642_ = lean_ctor_get(v_a_641_, 1);
v_fst_643_ = lean_ctor_get(v_a_641_, 0);
v_fst_644_ = lean_ctor_get(v_snd_642_, 0);
v_snd_645_ = lean_ctor_get(v_snd_642_, 1);
lean_inc(v_snd_645_);
lean_inc(v_fst_644_);
lean_inc(v_fst_643_);
lean_inc_ref(v_inputCtx_635_);
v___x_646_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_635_, v_fst_643_, v_fst_644_, v_snd_645_);
v___x_647_ = l_Lean_MessageLog_add(v___x_646_, v_b_639_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_638_, v___x_648_);
v_i_638_ = v___x_649_;
v_b_639_ = v___x_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_651_, lean_object* v_as_652_, lean_object* v_sz_653_, lean_object* v_i_654_, lean_object* v_b_655_){
_start:
{
size_t v_sz_boxed_656_; size_t v_i_boxed_657_; lean_object* v_res_658_; 
v_sz_boxed_656_ = lean_unbox_usize(v_sz_653_);
lean_dec(v_sz_653_);
v_i_boxed_657_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_651_, v_as_652_, v_sz_boxed_656_, v_i_boxed_657_, v_b_655_);
lean_dec_ref(v_as_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_snd_659_, uint8_t v___x_660_, lean_object* v_inputCtx_661_, lean_object* v_pos_662_, lean_object* v_stxStack_663_, lean_object* v_val_664_, lean_object* v___x_665_, lean_object* v_fst_666_, uint8_t v___y_667_, lean_object* v_____r_668_, lean_object* v_pos_669_){
_start:
{
lean_object* v_messages_671_; uint8_t v___y_678_; uint8_t v___y_688_; uint8_t v___x_690_; 
v___x_690_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_663_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_663_);
v___x_692_ = l_Lean_Syntax_getPos_x3f(v___x_691_, v___y_667_);
lean_dec(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
v___y_688_ = v___x_660_;
goto v___jp_687_;
}
else
{
lean_dec_ref_known(v___x_692_, 1);
v___y_688_ = v___y_667_;
goto v___jp_687_;
}
}
else
{
v___y_688_ = v___x_660_;
goto v___jp_687_;
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_messages_671_);
lean_ctor_set(v___x_672_, 1, v_snd_659_);
v___x_673_ = lean_box(v___x_660_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_pos_669_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_inc_ref(v_stxStack_663_);
v___x_679_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_661_, v_pos_662_, v_stxStack_663_, v_val_664_);
v___x_680_ = l_Lean_MessageLog_add(v___x_679_, v___x_665_);
if (v___y_678_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_snd_659_);
v___x_681_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_663_);
lean_dec_ref(v_stxStack_663_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_box(v___x_660_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_pos_669_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
else
{
lean_dec_ref(v_stxStack_663_);
v_messages_671_ = v___x_680_;
goto v___jp_670_;
}
}
v___jp_687_:
{
uint8_t v___x_689_; 
v___x_689_ = lean_unbox(v_fst_666_);
if (v___x_689_ == 0)
{
v___y_678_ = v___y_688_;
goto v___jp_677_;
}
else
{
if (v___y_688_ == 0)
{
v___y_678_ = v___y_688_;
goto v___jp_677_;
}
else
{
lean_dec_ref(v_val_664_);
lean_dec_ref(v_stxStack_663_);
lean_dec(v_pos_662_);
lean_dec_ref(v_inputCtx_661_);
v_messages_671_ = v___x_665_;
goto v___jp_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_snd_693_, lean_object* v___x_694_, lean_object* v_inputCtx_695_, lean_object* v_pos_696_, lean_object* v_stxStack_697_, lean_object* v_val_698_, lean_object* v___x_699_, lean_object* v_fst_700_, lean_object* v___y_701_, lean_object* v_____r_702_, lean_object* v_pos_703_){
_start:
{
uint8_t v___x_1844__boxed_704_; uint8_t v___y_1847__boxed_705_; lean_object* v_res_706_; 
v___x_1844__boxed_704_ = lean_unbox(v___x_694_);
v___y_1847__boxed_705_ = lean_unbox(v___y_701_);
v_res_706_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_693_, v___x_1844__boxed_704_, v_inputCtx_695_, v_pos_696_, v_stxStack_697_, v_val_698_, v___x_699_, v_fst_700_, v___y_1847__boxed_705_, v_____r_702_, v_pos_703_);
lean_dec(v_fst_700_);
return v_res_706_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_708_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_709_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_709_, 0, v___x_708_);
lean_closure_set(v___x_709_, 1, v___x_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_710_, lean_object* v_pmctx_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___y_714_; lean_object* v_snd_718_; lean_object* v_snd_719_; lean_object* v_fst_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_794_; 
v_snd_718_ = lean_ctor_get(v_a_712_, 1);
lean_inc(v_snd_718_);
v_snd_719_ = lean_ctor_get(v_snd_718_, 1);
lean_inc(v_snd_719_);
v_fst_720_ = lean_ctor_get(v_a_712_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_a_712_, 1);
lean_dec(v_unused_795_);
v___x_722_ = v_a_712_;
v_isShared_723_ = v_isSharedCheck_794_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_fst_720_);
lean_dec(v_a_712_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_794_;
goto v_resetjp_721_;
}
v___jp_713_:
{
if (lean_obj_tag(v___y_714_) == 0)
{
lean_object* v_a_715_; 
lean_dec_ref(v_pmctx_711_);
lean_dec_ref(v_inputCtx_710_);
v_a_715_ = lean_ctor_get(v___y_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___y_714_, 1);
return v_a_715_;
}
else
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v___y_714_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___y_714_, 1);
v_a_712_ = v_a_716_;
goto _start;
}
}
v_resetjp_721_:
{
lean_object* v_fst_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_792_; 
v_fst_724_ = lean_ctor_get(v_snd_718_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_snd_718_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_snd_718_, 1);
lean_dec(v_unused_793_);
v___x_726_ = v_snd_718_;
v_isShared_727_ = v_isSharedCheck_792_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_fst_724_);
lean_dec(v_snd_718_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_792_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_791_; 
v_fst_728_ = lean_ctor_get(v_snd_719_, 0);
v_snd_729_ = lean_ctor_get(v_snd_719_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_snd_719_);
if (v_isSharedCheck_791_ == 0)
{
v___x_731_ = v_snd_719_;
v_isShared_732_ = v_isSharedCheck_791_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v_snd_719_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_791_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_710_, v_fst_720_);
if (v___x_733_ == 0)
{
lean_object* v_env_734_; lean_object* v_inputString_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_stxStack_745_; lean_object* v_pos_746_; lean_object* v_errorMsg_747_; lean_object* v_recoveredErrors_748_; uint8_t v___x_749_; size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; uint8_t v___y_754_; uint8_t v___x_773_; 
v_env_734_ = lean_ctor_get(v_pmctx_711_, 0);
v_inputString_735_ = lean_ctor_get(v_inputCtx_710_, 0);
v___x_736_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_734_);
v___x_737_ = l_Lean_Parser_getTokenTable(v_env_734_);
v___x_738_ = l_Lean_Parser_SyntaxStack_empty;
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Lean_Parser_initCacheForInput(v_inputString_735_);
v___x_741_ = lean_box(0);
v___x_742_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_720_);
v___x_743_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_743_, 0, v___x_738_);
lean_ctor_set(v___x_743_, 1, v___x_739_);
lean_ctor_set(v___x_743_, 2, v_fst_720_);
lean_ctor_set(v___x_743_, 3, v___x_740_);
lean_ctor_set(v___x_743_, 4, v___x_741_);
lean_ctor_set(v___x_743_, 5, v___x_742_);
lean_inc_ref(v_pmctx_711_);
lean_inc_ref_n(v_inputCtx_710_, 2);
v___x_744_ = l_Lean_Parser_ParserFn_run(v___x_736_, v_inputCtx_710_, v_pmctx_711_, v___x_737_, v___x_743_);
v_stxStack_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_stxStack_745_);
v_pos_746_ = lean_ctor_get(v___x_744_, 2);
lean_inc(v_pos_746_);
v_errorMsg_747_ = lean_ctor_get(v___x_744_, 4);
lean_inc(v_errorMsg_747_);
v_recoveredErrors_748_ = lean_ctor_get(v___x_744_, 5);
lean_inc_ref(v_recoveredErrors_748_);
lean_dec_ref(v___x_744_);
v___x_749_ = 1;
v_sz_750_ = lean_array_size(v_recoveredErrors_748_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_710_, v_recoveredErrors_748_, v_sz_750_, v___x_751_, v_fst_728_);
lean_dec_ref(v_recoveredErrors_748_);
v___x_773_ = lean_unbox(v_fst_724_);
if (v___x_773_ == 0)
{
v___y_754_ = v___x_733_;
goto v___jp_753_;
}
else
{
uint8_t v___x_774_; 
v___x_774_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_745_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_745_);
v___x_776_ = l_Lean_Syntax_isAntiquot(v___x_775_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
v___y_754_ = v___x_776_;
goto v___jp_753_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_errorMsg_747_);
lean_dec_ref(v_stxStack_745_);
lean_del_object(v___x_731_);
lean_del_object(v___x_726_);
lean_del_object(v___x_722_);
lean_dec(v_fst_720_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_752_);
lean_ctor_set(v___x_777_, 1, v_snd_729_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_fst_724_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_pos_746_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v_a_712_ = v___x_779_;
goto _start;
}
}
else
{
v___y_754_ = v___x_733_;
goto v___jp_753_;
}
}
v___jp_753_:
{
if (lean_obj_tag(v_errorMsg_747_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v_snd_729_);
lean_dec(v_fst_724_);
lean_dec(v_fst_720_);
lean_dec_ref(v_pmctx_711_);
lean_dec_ref(v_inputCtx_710_);
v___x_755_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_745_);
lean_dec_ref(v_stxStack_745_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_755_);
lean_ctor_set(v___x_731_, 0, v___x_752_);
v___x_757_ = v___x_731_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_765_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_box(v___y_754_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_757_);
lean_ctor_set(v___x_726_, 0, v___x_758_);
v___x_760_ = v___x_726_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_757_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_760_);
lean_ctor_set(v___x_722_, 0, v_pos_746_);
v___x_762_ = v___x_722_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_pos_746_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_val_766_; uint8_t v_decide_767_; 
lean_del_object(v___x_731_);
lean_del_object(v___x_726_);
lean_del_object(v___x_722_);
v_val_766_ = lean_ctor_get(v_errorMsg_747_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_errorMsg_747_, 1);
v_decide_767_ = lean_nat_dec_eq(v_pos_746_, v_fst_720_);
lean_dec(v_fst_720_);
if (v_decide_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_box(0);
lean_inc(v_pos_746_);
lean_inc_ref(v_inputCtx_710_);
v___x_769_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_729_, v___x_749_, v_inputCtx_710_, v_pos_746_, v_stxStack_745_, v_val_766_, v___x_752_, v_fst_724_, v___y_754_, v___x_768_, v_pos_746_);
lean_dec(v_fst_724_);
v___y_714_ = v___x_769_;
goto v___jp_713_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_inc(v_pos_746_);
lean_inc_ref(v_pmctx_711_);
lean_inc_ref_n(v_inputCtx_710_, 2);
v___x_770_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_710_, v_pmctx_711_, v_pos_746_);
v___x_771_ = lean_box(0);
v___x_772_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_729_, v___x_749_, v_inputCtx_710_, v_pos_746_, v_stxStack_745_, v_val_766_, v___x_752_, v_fst_724_, v___y_754_, v___x_771_, v___x_770_);
lean_dec(v_fst_724_);
v___y_714_ = v___x_772_;
goto v___jp_713_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_snd_729_);
lean_dec_ref(v_pmctx_711_);
lean_inc(v_fst_720_);
v___x_781_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_710_, v_fst_720_);
lean_dec_ref(v_inputCtx_710_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_781_);
v___x_783_ = v___x_731_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_728_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_790_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_783_);
v___x_785_ = v___x_726_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_724_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_785_);
v___x_787_ = v___x_722_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_796_, lean_object* v_pmctx_797_, lean_object* v_mps_798_, lean_object* v_messages_799_){
_start:
{
lean_object* v_pos_800_; uint8_t v_recovering_801_; uint8_t v_hasLeading_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_842_; 
v_pos_800_ = lean_ctor_get(v_mps_798_, 0);
v_recovering_801_ = lean_ctor_get_uint8(v_mps_798_, sizeof(void*)*1);
v_hasLeading_802_ = lean_ctor_get_uint8(v_mps_798_, sizeof(void*)*1 + 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_mps_798_);
if (v_isSharedCheck_842_ == 0)
{
v___x_804_ = v_mps_798_;
v_isShared_805_ = v_isSharedCheck_842_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_pos_800_);
lean_dec(v_mps_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_842_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_stx_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_snd_812_; lean_object* v_snd_813_; lean_object* v_fst_814_; lean_object* v_fst_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_840_; 
v_stx_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_messages_799_);
lean_ctor_set(v___x_807_, 1, v_stx_806_);
v___x_808_ = lean_box(v_recovering_801_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_pos_800_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_796_, v_pmctx_797_, v___x_810_);
v_snd_812_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_snd_812_);
v_snd_813_ = lean_ctor_get(v_snd_812_, 1);
lean_inc(v_snd_813_);
v_fst_814_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_fst_814_);
lean_dec_ref(v___x_811_);
v_fst_815_ = lean_ctor_get(v_snd_812_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v_snd_812_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_snd_812_, 1);
lean_dec(v_unused_841_);
v___x_817_ = v_snd_812_;
v_isShared_818_ = v_isSharedCheck_840_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_fst_815_);
lean_dec(v_snd_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_840_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_839_; 
v_fst_819_ = lean_ctor_get(v_snd_813_, 0);
v_snd_820_ = lean_ctor_get(v_snd_813_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_snd_813_);
if (v_isSharedCheck_839_ == 0)
{
v___x_822_ = v_snd_813_;
v_isShared_823_ = v_isSharedCheck_839_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_inc(v_fst_819_);
lean_dec(v_snd_813_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_839_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_stx_825_; 
if (v_hasLeading_802_ == 0)
{
v_stx_825_ = v_snd_820_;
goto v___jp_824_;
}
else
{
lean_object* v___x_837_; lean_object* v_fst_838_; 
v___x_837_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_820_);
v_fst_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_fst_838_);
lean_dec_ref(v___x_837_);
v_stx_825_ = v_fst_838_;
goto v___jp_824_;
}
v___jp_824_:
{
uint8_t v___x_826_; lean_object* v___x_828_; 
v___x_826_ = 0;
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_fst_814_);
v___x_828_ = v___x_804_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_fst_814_);
v___x_828_ = v_reuseFailAlloc_836_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
uint8_t v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_unbox(v_fst_815_);
lean_dec(v_fst_815_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*1, v___x_829_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*1 + 1, v___x_826_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_fst_819_);
lean_ctor_set(v___x_822_, 0, v___x_828_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_fst_819_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_831_);
lean_ctor_set(v___x_817_, 0, v_stx_825_);
v___x_833_ = v___x_817_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_stx_825_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_843_, lean_object* v_pmctx_844_, lean_object* v_inst_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_843_, v_pmctx_844_, v_a_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_848_){
_start:
{
lean_object* v___x_850_; lean_object* v_putStr_851_; lean_object* v___x_852_; 
v___x_850_ = lean_get_stdout();
v_putStr_851_ = lean_ctor_get(v___x_850_, 4);
lean_inc_ref(v_putStr_851_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_apply_2(v_putStr_851_, v_s_848_, lean_box(0));
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_856_){
_start:
{
uint32_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = 10;
v___x_859_ = lean_string_push(v_s_856_, v___x_858_);
v___x_860_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___x_864_, lean_object* v_msg_865_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = l_Lean_Message_toString(v_msg_865_, v___x_864_);
v___x_868_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___x_869_, lean_object* v_msg_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_1235__boxed_872_; lean_object* v_res_873_; 
v___x_1235__boxed_872_ = lean_unbox(v___x_869_);
v_res_873_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___x_1235__boxed_872_, v_msg_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_874_, lean_object* v_as_875_, size_t v_i_876_, size_t v_stop_877_, lean_object* v_b_878_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_usize_dec_eq(v_i_876_, v_stop_877_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_array_uget_borrowed(v_as_875_, v_i_876_);
lean_inc_ref(v_f_874_);
lean_inc(v___x_881_);
v___x_882_ = lean_apply_2(v_f_874_, v___x_881_, lean_box(0));
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; size_t v___x_884_; size_t v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_876_, v___x_884_);
v_i_876_ = v___x_885_;
v_b_878_ = v_a_883_;
goto _start;
}
else
{
lean_dec_ref(v_f_874_);
return v___x_882_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref(v_f_874_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_878_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_888_, lean_object* v_as_889_, lean_object* v_i_890_, lean_object* v_stop_891_, lean_object* v_b_892_, lean_object* v___y_893_){
_start:
{
size_t v_i_boxed_894_; size_t v_stop_boxed_895_; lean_object* v_res_896_; 
v_i_boxed_894_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_stop_boxed_895_ = lean_unbox_usize(v_stop_891_);
lean_dec(v_stop_891_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_888_, v_as_889_, v_i_boxed_894_, v_stop_boxed_895_, v_b_892_);
lean_dec_ref(v_as_889_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_object* v_cs_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_914_; 
v_cs_900_ = lean_ctor_get(v_x_898_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_914_ == 0)
{
v___x_902_ = v_x_898_;
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_cs_900_);
lean_dec(v_x_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_array_get_size(v_cs_900_);
v___x_906_ = lean_box(0);
v___x_907_ = lean_nat_dec_lt(v___x_904_, v___x_905_);
if (v___x_907_ == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_cs_900_);
lean_dec_ref(v_f_897_);
if (v_isShared_903_ == 0)
{
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
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
lean_del_object(v___x_902_);
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_905_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_897_, v_cs_900_, v___x_911_, v___x_912_, v___x_906_);
lean_dec_ref(v_cs_900_);
return v___x_913_;
}
}
}
else
{
lean_object* v_vs_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_929_; 
v_vs_915_ = lean_ctor_get(v_x_898_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_929_ == 0)
{
v___x_917_ = v_x_898_;
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_vs_915_);
lean_dec(v_x_898_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_array_get_size(v_vs_915_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_nat_dec_lt(v___x_919_, v___x_920_);
if (v___x_922_ == 0)
{
lean_object* v___x_924_; 
lean_dec_ref(v_vs_915_);
lean_dec_ref(v_f_897_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 0, v___x_921_);
v___x_924_ = v___x_917_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_921_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
else
{
size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_917_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = lean_usize_of_nat(v___x_920_);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_897_, v_vs_915_, v___x_926_, v___x_927_, v___x_921_);
lean_dec_ref(v_vs_915_);
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_930_, lean_object* v_as_931_, size_t v_i_932_, size_t v_stop_933_, lean_object* v_b_934_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_eq(v_i_932_, v_stop_933_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_array_uget_borrowed(v_as_931_, v_i_932_);
lean_inc(v___x_937_);
lean_inc_ref(v_f_930_);
v___x_938_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_930_, v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; size_t v___x_940_; size_t v___x_941_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = ((size_t)1ULL);
v___x_941_ = lean_usize_add(v_i_932_, v___x_940_);
v_i_932_ = v___x_941_;
v_b_934_ = v_a_939_;
goto _start;
}
else
{
lean_dec_ref(v_f_930_);
return v___x_938_;
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v_f_930_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_934_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_944_, lean_object* v_as_945_, lean_object* v_i_946_, lean_object* v_stop_947_, lean_object* v_b_948_, lean_object* v___y_949_){
_start:
{
size_t v_i_boxed_950_; size_t v_stop_boxed_951_; lean_object* v_res_952_; 
v_i_boxed_950_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_stop_boxed_951_ = lean_unbox_usize(v_stop_947_);
lean_dec(v_stop_947_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_944_, v_as_945_, v_i_boxed_950_, v_stop_boxed_951_, v_b_948_);
lean_dec_ref(v_as_945_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_953_, lean_object* v_x_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_953_, v_x_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_957_, lean_object* v_t_958_){
_start:
{
lean_object* v_root_960_; lean_object* v_tail_961_; lean_object* v___x_962_; 
v_root_960_ = lean_ctor_get(v_t_958_, 0);
lean_inc_ref(v_root_960_);
v_tail_961_ = lean_ctor_get(v_t_958_, 1);
lean_inc_ref(v_tail_961_);
lean_dec_ref(v_t_958_);
lean_inc_ref(v_f_957_);
v___x_962_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_957_, v_root_960_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_977_);
v___x_964_ = v___x_962_;
v_isShared_965_ = v_isSharedCheck_976_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_962_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_976_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_array_get_size(v_tail_961_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_nat_dec_lt(v___x_966_, v___x_967_);
if (v___x_969_ == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v_tail_961_);
lean_dec_ref(v_f_957_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_968_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_968_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
lean_del_object(v___x_964_);
v___x_973_ = ((size_t)0ULL);
v___x_974_ = lean_usize_of_nat(v___x_967_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_957_, v_tail_961_, v___x_973_, v___x_974_, v___x_968_);
lean_dec_ref(v_tail_961_);
return v___x_975_;
}
}
}
else
{
lean_dec_ref(v_tail_961_);
lean_dec_ref(v_f_957_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_978_, lean_object* v_t_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_978_, v_t_979_);
return v_res_981_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_983_, lean_object* v_x_984_, size_t v_x_985_, size_t v_x_986_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
lean_object* v_cs_988_; lean_object* v___x_989_; size_t v___x_990_; lean_object* v_j_991_; lean_object* v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v_cs_988_ = lean_ctor_get(v_x_984_, 0);
lean_inc_ref(v_cs_988_);
lean_dec_ref_known(v_x_984_, 1);
v___x_989_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_990_ = lean_usize_shift_right(v_x_985_, v_x_986_);
v_j_991_ = lean_usize_to_nat(v___x_990_);
v___x_992_ = lean_array_get_borrowed(v___x_989_, v_cs_988_, v_j_991_);
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_shift_left(v___x_993_, v_x_986_);
v___x_995_ = lean_usize_sub(v___x_994_, v___x_993_);
v___x_996_ = lean_usize_land(v_x_985_, v___x_995_);
v___x_997_ = ((size_t)5ULL);
v___x_998_ = lean_usize_sub(v_x_986_, v___x_997_);
lean_inc(v___x_992_);
lean_inc_ref(v_f_983_);
v___x_999_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_983_, v___x_992_, v___x_996_, v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_999_, 0);
lean_dec(v_unused_1015_);
v___x_1001_ = v___x_999_;
v_isShared_1002_ = v_isSharedCheck_1014_;
goto v_resetjp_1000_;
}
else
{
lean_dec(v___x_999_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1014_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_j_991_, v___x_1003_);
lean_dec(v_j_991_);
v___x_1005_ = lean_array_get_size(v_cs_988_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v___x_1004_);
lean_dec_ref(v_cs_988_);
lean_dec_ref(v_f_983_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1006_);
v___x_1009_ = v___x_1001_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
size_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_1001_);
v___x_1011_ = lean_usize_of_nat(v___x_1004_);
lean_dec(v___x_1004_);
v___x_1012_ = lean_usize_of_nat(v___x_1005_);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_983_, v_cs_988_, v___x_1011_, v___x_1012_, v___x_1006_);
lean_dec_ref(v_cs_988_);
return v___x_1013_;
}
}
}
else
{
lean_dec(v_j_991_);
lean_dec_ref(v_cs_988_);
lean_dec_ref(v_f_983_);
return v___x_999_;
}
}
else
{
lean_object* v_vs_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1030_; 
v_vs_1016_ = lean_ctor_get(v_x_984_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1018_ = v_x_984_;
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_vs_1016_);
lean_dec(v_x_984_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1020_ = lean_usize_to_nat(v_x_985_);
v___x_1021_ = lean_array_get_size(v_vs_1016_);
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v___x_1020_);
lean_dec_ref(v_vs_1016_);
lean_dec_ref(v_f_983_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1022_);
v___x_1025_ = v___x_1018_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
lean_del_object(v___x_1018_);
v___x_1027_ = lean_usize_of_nat(v___x_1020_);
lean_dec(v___x_1020_);
v___x_1028_ = lean_usize_of_nat(v___x_1021_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_983_, v_vs_1016_, v___x_1027_, v___x_1028_, v___x_1022_);
lean_dec_ref(v_vs_1016_);
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_x_1391__boxed_1036_; size_t v_x_1392__boxed_1037_; lean_object* v_res_1038_; 
v_x_1391__boxed_1036_ = lean_unbox_usize(v_x_1033_);
lean_dec(v_x_1033_);
v_x_1392__boxed_1037_ = lean_unbox_usize(v_x_1034_);
lean_dec(v_x_1034_);
v_res_1038_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1031_, v_x_1032_, v_x_1391__boxed_1036_, v_x_1392__boxed_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1039_, lean_object* v_t_1040_, lean_object* v_start_1041_){
_start:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_nat_dec_eq(v_start_1041_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v_root_1045_; lean_object* v_tail_1046_; size_t v_shift_1047_; lean_object* v_tailOff_1048_; uint8_t v___x_1049_; 
v_root_1045_ = lean_ctor_get(v_t_1040_, 0);
lean_inc_ref(v_root_1045_);
v_tail_1046_ = lean_ctor_get(v_t_1040_, 1);
lean_inc_ref(v_tail_1046_);
v_shift_1047_ = lean_ctor_get_usize(v_t_1040_, 4);
v_tailOff_1048_ = lean_ctor_get(v_t_1040_, 3);
lean_inc(v_tailOff_1048_);
lean_dec_ref(v_t_1040_);
v___x_1049_ = lean_nat_dec_le(v_tailOff_1048_, v_start_1041_);
if (v___x_1049_ == 0)
{
size_t v___x_1050_; lean_object* v___x_1051_; 
lean_dec(v_tailOff_1048_);
v___x_1050_ = lean_usize_of_nat(v_start_1041_);
lean_inc_ref(v_f_1039_);
v___x_1051_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1039_, v_root_1045_, v___x_1050_, v_shift_1047_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1065_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1055_ = lean_array_get_size(v_tail_1046_);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_nat_dec_lt(v___x_1043_, v___x_1055_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref(v_tail_1046_);
lean_dec_ref(v_f_1039_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
lean_del_object(v___x_1053_);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = lean_usize_of_nat(v___x_1055_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1039_, v_tail_1046_, v___x_1061_, v___x_1062_, v___x_1056_);
lean_dec_ref(v_tail_1046_);
return v___x_1063_;
}
}
}
else
{
lean_dec_ref(v_tail_1046_);
lean_dec_ref(v_f_1039_);
return v___x_1051_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
lean_dec_ref(v_root_1045_);
v___x_1066_ = lean_nat_sub(v_start_1041_, v_tailOff_1048_);
lean_dec(v_tailOff_1048_);
v___x_1067_ = lean_array_get_size(v_tail_1046_);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
lean_dec(v___x_1066_);
lean_dec_ref(v_tail_1046_);
lean_dec_ref(v_f_1039_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
return v___x_1070_;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_usize_of_nat(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1072_ = lean_usize_of_nat(v___x_1067_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1039_, v_tail_1046_, v___x_1071_, v___x_1072_, v___x_1068_);
lean_dec_ref(v_tail_1046_);
return v___x_1073_;
}
}
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1039_, v_t_1040_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1075_, lean_object* v_t_1076_, lean_object* v_start_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1075_, v_t_1076_, v_start_1077_);
lean_dec(v_start_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1080_, lean_object* v_f_1081_){
_start:
{
lean_object* v_unreported_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_unreported_1083_ = lean_ctor_get(v_log_1080_, 1);
lean_inc_ref(v_unreported_1083_);
lean_dec_ref(v_log_1080_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1081_, v_unreported_1083_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1086_, lean_object* v_f_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1086_, v_f_1087_);
return v_res_1089_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1));
v___x_1095_ = lean_mk_io_user_error(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1096_, lean_object* v_inputCtx_1097_, lean_object* v_state_1098_, lean_object* v_msgs_1099_, lean_object* v_stxs_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_snd_1107_; lean_object* v_fst_1108_; lean_object* v_fst_1109_; lean_object* v_snd_1110_; uint8_t v___x_1111_; 
v___x_1102_ = l_Lean_Options_empty;
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_box(0);
lean_inc_ref(v_env_1096_);
v___x_1105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1105_, 0, v_env_1096_);
lean_ctor_set(v___x_1105_, 1, v___x_1102_);
lean_ctor_set(v___x_1105_, 2, v___x_1103_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
lean_inc_ref(v_inputCtx_1097_);
v___x_1106_ = l_Lean_Parser_parseCommand(v_inputCtx_1097_, v___x_1105_, v_state_1098_, v_msgs_1099_);
v_snd_1107_ = lean_ctor_get(v___x_1106_, 1);
lean_inc(v_snd_1107_);
v_fst_1108_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_n(v_fst_1108_, 2);
lean_dec_ref(v___x_1106_);
v_fst_1109_ = lean_ctor_get(v_snd_1107_, 0);
lean_inc(v_fst_1109_);
v_snd_1110_ = lean_ctor_get(v_snd_1107_, 1);
lean_inc(v_snd_1110_);
lean_dec(v_snd_1107_);
v___x_1111_ = l_Lean_Parser_isTerminalCommand(v_fst_1108_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_array_push(v_stxs_1100_, v_fst_1108_);
v_state_1098_ = v_fst_1109_;
v_msgs_1099_ = v_snd_1110_;
v_stxs_1100_ = v___x_1112_;
goto _start;
}
else
{
uint8_t v___x_1114_; 
lean_dec(v_fst_1109_);
lean_dec_ref(v_inputCtx_1097_);
lean_dec_ref(v_env_1096_);
v___x_1114_ = l_Lean_MessageLog_hasUnreported(v_snd_1110_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_snd_1110_);
v___x_1115_ = lean_array_push(v_stxs_1100_, v_fst_1108_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v___f_1117_; lean_object* v___x_1118_; 
lean_dec(v_fst_1108_);
lean_dec_ref(v_stxs_1100_);
v___f_1117_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1118_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1110_, v___f_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1127_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__2);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1136_, lean_object* v_inputCtx_1137_, lean_object* v_state_1138_, lean_object* v_msgs_1139_, lean_object* v_stxs_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1136_, v_inputCtx_1137_, v_state_1138_, v_msgs_1139_, v_stxs_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1143_, lean_object* v_inputCtx_1144_, lean_object* v_s_1145_, lean_object* v_msgs_1146_, lean_object* v_stxs_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1143_, v_inputCtx_1144_, v_s_1145_, v_msgs_1146_, v_stxs_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1150_, lean_object* v_inputCtx_1151_, lean_object* v_s_1152_, lean_object* v_msgs_1153_, lean_object* v_stxs_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Parser_testParseModuleAux(v_env_1150_, v_inputCtx_1151_, v_s_1152_, v_msgs_1153_, v_stxs_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1165_, lean_object* v_fname_1166_, lean_object* v_contents_1167_){
_start:
{
uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v_inputCtx_1171_; lean_object* v___x_1172_; 
v___x_1169_ = 1;
v___x_1170_ = lean_string_utf8_byte_size(v_contents_1167_);
v_inputCtx_1171_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1167_, v_fname_1166_, v___x_1169_, v___x_1170_);
lean_inc_ref(v_inputCtx_1171_);
v___x_1172_ = l_Lean_Parser_parseHeader(v_inputCtx_1171_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_snd_1174_; lean_object* v_fst_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v_snd_1174_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1174_);
v_fst_1175_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1175_);
lean_dec(v_a_1173_);
v_fst_1176_ = lean_ctor_get(v_snd_1174_, 0);
lean_inc(v_fst_1176_);
v_snd_1177_ = lean_ctor_get(v_snd_1174_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_snd_1174_);
v___x_1178_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1179_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1165_, v_inputCtx_1171_, v_fst_1176_, v_snd_1177_, v___x_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1195_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1184_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1185_ = l_Lean_mkListNode(v_a_1180_);
v___x_1186_ = lean_unsigned_to_nat(2u);
v___x_1187_ = lean_mk_empty_array_with_capacity(v___x_1186_);
v___x_1188_ = lean_array_push(v___x_1187_, v_fst_1175_);
v___x_1189_ = lean_array_push(v___x_1188_, v___x_1185_);
v___x_1190_ = lean_box(2);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___x_1184_);
lean_ctor_set(v___x_1191_, 2, v___x_1189_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1191_);
v___x_1193_ = v___x_1182_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_fst_1175_);
v_a_1196_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1179_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1179_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_inputCtx_1171_);
lean_dec_ref(v_env_1165_);
v_a_1204_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1172_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1172_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1212_, lean_object* v_fname_1213_, lean_object* v_contents_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Parser_testParseModule(v_env_1212_, v_fname_1213_, v_contents_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1217_, lean_object* v_fname_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_IO_FS_readFile(v_fname_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l_Lean_Parser_testParseModule(v_env_1217_, v_fname_1218_, v_a_1221_);
return v___x_1222_;
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_fname_1218_);
lean_dec_ref(v_env_1217_);
v_a_1223_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1220_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1220_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1231_, lean_object* v_fname_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Parser_testParseFile(v_env_1231_, v_fname_1232_);
return v_res_1234_;
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
