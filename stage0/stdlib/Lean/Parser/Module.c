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
uint8_t l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(lean_object* v_x_163_, lean_object* v_x_164_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_163_ = stack[0].m_obj;
lean_object* v_x_164_ = stack[1].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_163_, v_x_164_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_172_, v_x_173_);
lean_dec(v_x_173_);
lean_dec(v_x_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(lean_object* v_inputCtx_176_, lean_object* v_as_177_, size_t v_sz_178_, size_t v_i_179_, lean_object* v_b_180_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
lean_dec_ref(v_inputCtx_176_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_b_180_);
return v___x_183_;
}
else
{
lean_object* v_a_184_; lean_object* v_snd_185_; lean_object* v_fst_186_; lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_189_; lean_object* v___x_190_; size_t v___x_191_; size_t v___x_192_; 
v_a_184_ = lean_array_uget_borrowed(v_as_177_, v_i_179_);
v_snd_185_ = lean_ctor_get(v_a_184_, 1);
v_fst_186_ = lean_ctor_get(v_a_184_, 0);
v_fst_187_ = lean_ctor_get(v_snd_185_, 0);
v_snd_188_ = lean_ctor_get(v_snd_185_, 1);
lean_inc(v_snd_188_);
lean_inc(v_fst_187_);
lean_inc(v_fst_186_);
lean_inc_ref(v_inputCtx_176_);
v___x_189_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_176_, v_fst_186_, v_fst_187_, v_snd_188_);
v___x_190_ = l_Lean_MessageLog_add(v___x_189_, v_b_180_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_179_, v___x_191_);
v_i_179_ = v___x_192_;
v_b_180_ = v___x_190_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_176_ = stack[0].m_obj;
lean_object* v_as_177_ = stack[1].m_obj;
size_t v_sz_178_ = stack[2].m_num;
size_t v_i_179_ = stack[3].m_num;
lean_object* v_b_180_ = stack[4].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_176_, v_as_177_, v_sz_178_, v_i_179_, v_b_180_);
stack->m_obj
 = v_res_194_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(uint8_t v___x_204_, lean_object* v_inputCtx_205_, lean_object* v_ref_206_, lean_object* v_msg_207_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_204_ = stack[0].m_num;
lean_object* v_inputCtx_205_ = stack[1].m_obj;
lean_object* v_ref_206_ = stack[2].m_obj;
lean_object* v_msg_207_ = stack[3].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_204_, v_inputCtx_205_, v_ref_206_, v_msg_207_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(lean_object* v___x_230_, lean_object* v_inputCtx_231_, lean_object* v_ref_232_, lean_object* v_msg_233_){
_start:
{
uint8_t v___x_3087__boxed_234_; lean_object* v_res_235_; 
v___x_3087__boxed_234_ = lean_unbox(v___x_230_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_3087__boxed_234_, v_inputCtx_231_, v_ref_232_, v_msg_233_);
lean_dec(v_ref_232_);
return v_res_235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6));
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9));
v___x_254_ = l_Lean_MessageData_ofFormat(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15));
v___x_262_ = l_Lean_MessageData_ofFormat(v___x_261_);
return v___x_262_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(lean_object* v_inputCtx_281_, lean_object* v_moduleTk_x3f_282_, lean_object* v_as_283_, size_t v_sz_284_, size_t v_i_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_a_289_; uint8_t v___x_293_; 
v___x_293_ = lean_usize_dec_lt(v_i_285_, v_sz_284_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v_inputCtx_281_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v_b_286_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v_a_296_; uint8_t v___x_297_; 
v___x_295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4));
v_a_296_ = lean_array_uget_borrowed(v_as_283_, v_i_285_);
lean_inc(v_a_296_);
v___x_297_ = l_Lean_Syntax_isOfKind(v_a_296_, v___x_295_);
if (v___x_297_ == 0)
{
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___y_299_; lean_object* v_messages_300_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v_messages_308_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___x_338_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v_allTk_x3f_342_; lean_object* v___x_353_; lean_object* v___y_355_; lean_object* v_metaTk_x3f_356_; lean_object* v_pubTk_x3f_368_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_378_ = l_Lean_Syntax_getArg(v_a_296_, v___x_338_);
v___x_379_ = l_Lean_Syntax_isNone(v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
lean_inc(v___x_378_);
v___x_380_ = l_Lean_Syntax_matchesNull(v___x_378_, v___x_353_);
if (v___x_380_ == 0)
{
lean_dec(v___x_378_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = l_Lean_Syntax_getArg(v___x_378_, v___x_338_);
lean_dec(v___x_378_);
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22));
lean_inc(v___x_381_);
v___x_383_ = l_Lean_Syntax_isOfKind(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v___x_381_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_Syntax_getArg(v___x_381_, v___x_338_);
lean_dec(v___x_381_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v_pubTk_x3f_368_ = v___x_385_;
goto v___jp_367_;
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v___x_378_);
v___x_386_ = lean_box(0);
v_pubTk_x3f_368_ = v___x_386_;
goto v___jp_367_;
}
v___jp_298_:
{
if (lean_obj_tag(v___y_299_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_val_301_ = lean_ctor_get(v___y_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___y_299_, 1);
v___x_302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7);
lean_inc_ref(v_inputCtx_281_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_297_, v_inputCtx_281_, v_val_301_, v___x_302_);
lean_dec(v_val_301_);
v___x_304_ = l_Lean_MessageLog_add(v___x_303_, v_messages_300_);
v_a_289_ = v___x_304_;
goto v___jp_288_;
}
else
{
lean_dec(v___y_299_);
v_a_289_ = v_messages_300_;
goto v___jp_288_;
}
}
v___jp_305_:
{
if (lean_obj_tag(v___y_307_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_val_309_ = lean_ctor_get(v___y_307_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___y_307_, 1);
v___x_310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
lean_inc_ref(v_inputCtx_281_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_297_, v_inputCtx_281_, v_val_309_, v___x_310_);
lean_dec(v_val_309_);
v___x_312_ = l_Lean_MessageLog_add(v___x_311_, v_messages_308_);
v___y_299_ = v___y_306_;
v_messages_300_ = v___x_312_;
goto v___jp_298_;
}
else
{
lean_dec(v___y_307_);
v___y_299_ = v___y_306_;
v_messages_300_ = v_messages_308_;
goto v___jp_298_;
}
}
v___jp_313_:
{
if (lean_obj_tag(v___y_315_) == 1)
{
if (lean_obj_tag(v___y_316_) == 0)
{
lean_dec_ref_known(v___y_315_, 1);
lean_dec(v___y_314_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_336_; 
v_isSharedCheck_336_ = !lean_is_exclusive(v___y_316_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___y_316_, 0);
lean_dec(v_unused_337_);
v___x_319_ = v___y_316_;
v_isShared_320_ = v_isSharedCheck_336_;
goto v_resetjp_318_;
}
else
{
lean_dec(v___y_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_336_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
if (v___y_317_ == 0)
{
lean_del_object(v___x_319_);
lean_dec_ref_known(v___y_315_, 1);
lean_dec(v___y_314_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v_val_321_ = lean_ctor_get(v___y_315_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___y_315_, 1);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_314_, v___y_317_);
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
v___x_325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = lean_string_append(v___x_326_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13));
v___x_329_ = lean_string_append(v___x_327_, v___x_328_);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 3);
lean_ctor_set(v___x_319_, 0, v___x_329_);
v___x_331_ = v___x_319_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lean_MessageData_ofFormat(v___x_331_);
lean_inc_ref(v_inputCtx_281_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_297_, v_inputCtx_281_, v_val_321_, v___x_332_);
lean_dec(v_val_321_);
v___x_334_ = l_Lean_MessageLog_add(v___x_333_, v_b_286_);
v_a_289_ = v___x_334_;
goto v___jp_288_;
}
}
}
}
}
else
{
lean_dec(v___y_316_);
lean_dec(v___y_315_);
lean_dec(v___y_314_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
}
v___jp_339_:
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(5u);
v___x_344_ = l_Lean_Syntax_getArg(v_a_296_, v___x_343_);
v___x_345_ = l_Lean_Syntax_matchesNull(v___x_344_, v___x_338_);
if (v___x_345_ == 0)
{
lean_dec(v_allTk_x3f_342_);
lean_dec(v___y_341_);
lean_dec(v___y_340_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = l_Lean_Syntax_getArg(v_a_296_, v___x_346_);
v___x_348_ = l_Lean_TSyntax_getId(v___x_347_);
lean_dec(v___x_347_);
if (lean_obj_tag(v_moduleTk_x3f_282_) == 0)
{
if (v___x_345_ == 0)
{
lean_dec(v___y_341_);
v___y_314_ = v___x_348_;
v___y_315_ = v_allTk_x3f_342_;
v___y_316_ = v___y_340_;
v___y_317_ = v___x_345_;
goto v___jp_313_;
}
else
{
lean_dec(v___x_348_);
if (lean_obj_tag(v___y_340_) == 1)
{
lean_object* v_val_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_val_349_ = lean_ctor_get(v___y_340_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v___y_340_, 1);
v___x_350_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
lean_inc_ref(v_inputCtx_281_);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_297_, v_inputCtx_281_, v_val_349_, v___x_350_);
lean_dec(v_val_349_);
v___x_352_ = l_Lean_MessageLog_add(v___x_351_, v_b_286_);
v___y_306_ = v_allTk_x3f_342_;
v___y_307_ = v___y_341_;
v_messages_308_ = v___x_352_;
goto v___jp_305_;
}
else
{
lean_dec(v___y_340_);
v___y_306_ = v_allTk_x3f_342_;
v___y_307_ = v___y_341_;
v_messages_308_ = v_b_286_;
goto v___jp_305_;
}
}
}
else
{
lean_dec(v___y_341_);
v___y_314_ = v___x_348_;
v___y_315_ = v_allTk_x3f_342_;
v___y_316_ = v___y_340_;
v___y_317_ = v___x_345_;
goto v___jp_313_;
}
}
}
v___jp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = l_Lean_Syntax_getArg(v_a_296_, v___x_357_);
v___x_359_ = l_Lean_Syntax_isNone(v___x_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
lean_inc(v___x_358_);
v___x_360_ = l_Lean_Syntax_matchesNull(v___x_358_, v___x_353_);
if (v___x_360_ == 0)
{
lean_dec(v___x_358_);
lean_dec(v_metaTk_x3f_356_);
lean_dec(v___y_355_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_Syntax_getArg(v___x_358_, v___x_338_);
lean_dec(v___x_358_);
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18));
lean_inc(v___x_361_);
v___x_363_ = l_Lean_Syntax_isOfKind(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v___x_361_);
lean_dec(v_metaTk_x3f_356_);
lean_dec(v___y_355_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_Lean_Syntax_getArg(v___x_361_, v___x_338_);
lean_dec(v___x_361_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
v___y_340_ = v___y_355_;
v___y_341_ = v_metaTk_x3f_356_;
v_allTk_x3f_342_ = v___x_365_;
goto v___jp_339_;
}
}
}
else
{
lean_object* v___x_366_; 
lean_dec(v___x_358_);
v___x_366_ = lean_box(0);
v___y_340_ = v___y_355_;
v___y_341_ = v_metaTk_x3f_356_;
v_allTk_x3f_342_ = v___x_366_;
goto v___jp_339_;
}
}
v___jp_367_:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = l_Lean_Syntax_getArg(v_a_296_, v___x_353_);
v___x_370_ = l_Lean_Syntax_isNone(v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_inc(v___x_369_);
v___x_371_ = l_Lean_Syntax_matchesNull(v___x_369_, v___x_353_);
if (v___x_371_ == 0)
{
lean_dec(v___x_369_);
lean_dec(v_pubTk_x3f_368_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = l_Lean_Syntax_getArg(v___x_369_, v___x_338_);
lean_dec(v___x_369_);
v___x_373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20));
lean_inc(v___x_372_);
v___x_374_ = l_Lean_Syntax_isOfKind(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v___x_372_);
lean_dec(v_pubTk_x3f_368_);
v_a_289_ = v_b_286_;
goto v___jp_288_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Lean_Syntax_getArg(v___x_372_, v___x_338_);
lean_dec(v___x_372_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___y_355_ = v_pubTk_x3f_368_;
v_metaTk_x3f_356_ = v___x_376_;
goto v___jp_354_;
}
}
}
else
{
lean_object* v___x_377_; 
lean_dec(v___x_369_);
v___x_377_ = lean_box(0);
v___y_355_ = v_pubTk_x3f_368_;
v_metaTk_x3f_356_ = v___x_377_;
goto v___jp_354_;
}
}
}
}
v___jp_288_:
{
size_t v___x_290_; size_t v___x_291_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_i_285_, v___x_290_);
v_i_285_ = v___x_291_;
v_b_286_ = v_a_289_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_281_ = stack[0].m_obj;
lean_object* v_moduleTk_x3f_282_ = stack[1].m_obj;
lean_object* v_as_283_ = stack[2].m_obj;
size_t v_sz_284_ = stack[3].m_num;
size_t v_i_285_ = stack[4].m_num;
lean_object* v_b_286_ = stack[5].m_obj;
lean_object* v_res_387_;
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_281_, v_moduleTk_x3f_282_, v_as_283_, v_sz_284_, v_i_285_, v_b_286_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(lean_object* v_inputCtx_388_, lean_object* v_moduleTk_x3f_389_, lean_object* v_as_390_, lean_object* v_sz_391_, lean_object* v_i_392_, lean_object* v_b_393_, lean_object* v___y_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_391_);
lean_dec(v_sz_391_);
v_i_boxed_396_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_388_, v_moduleTk_x3f_389_, v_as_390_, v_sz_boxed_395_, v_i_boxed_396_, v_b_393_);
lean_dec_ref(v_as_390_);
lean_dec(v_moduleTk_x3f_389_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__2(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__3(void){
_start:
{
size_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((size_t)5ULL);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_unsigned_to_nat(32u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__2, &l_Lean_Parser_parseHeader___closed__2_once, _init_l_Lean_Parser_parseHeader___closed__2);
v___x_408_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_404_);
lean_ctor_set(v___x_408_, 3, v___x_404_);
lean_ctor_set_usize(v___x_408_, 4, v___x_403_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Parser_parseHeader___closed__4(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = l_Lean_NameSet_empty;
v___x_410_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__3, &l_Lean_Parser_parseHeader___closed__3_once, _init_l_Lean_Parser_parseHeader___closed__3);
v___x_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
return v___x_411_;
}
}
lean_object* l_Lean_Parser_parseHeader(lean_object* v_inputCtx_424_){
_start:
{
lean_object* v___x_426_; uint32_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = 0;
v___x_428_ = l_Lean_mkEmptyEnvironment(v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_548_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_548_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_548_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_548_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_fn_434_; lean_object* v_inputString_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_stxStack_446_; lean_object* v_pos_447_; lean_object* v_errorMsg_448_; lean_object* v___y_450_; uint8_t v___y_451_; lean_object* v___y_452_; uint8_t v___y_453_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_468_; lean_object* v_messages_469_; size_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_499_; size_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v_moduleTk_x3f_505_; lean_object* v___y_515_; uint8_t v___x_545_; 
v___x_433_ = l_Lean_Parser_Module_header;
v_fn_434_ = lean_ctor_get(v___x_433_, 1);
v_inputString_435_ = lean_ctor_get(v_inputCtx_424_, 0);
lean_inc(v_a_429_);
v___x_436_ = l_Lean_Parser_getTokenTable(v_a_429_);
v___x_437_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_434_);
v___x_438_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_438_, 0, v___x_437_);
lean_closure_set(v___x_438_, 1, v_fn_434_);
v___x_439_ = l_Lean_Parser_Module_updateTokens(v___x_436_);
v___x_440_ = l_Lean_Options_empty;
v___x_441_ = lean_box(0);
v___x_442_ = lean_box(0);
v___x_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_443_, 0, v_a_429_);
lean_ctor_set(v___x_443_, 1, v___x_440_);
lean_ctor_set(v___x_443_, 2, v___x_441_);
lean_ctor_set(v___x_443_, 3, v___x_442_);
v___x_444_ = l_Lean_Parser_mkParserState(v_inputString_435_);
lean_inc_ref(v_inputCtx_424_);
v___x_445_ = l_Lean_Parser_ParserFn_run(v___x_438_, v_inputCtx_424_, v___x_443_, v___x_439_, v___x_444_);
v_stxStack_446_ = lean_ctor_get(v___x_445_, 0);
v_pos_447_ = lean_ctor_get(v___x_445_, 2);
lean_inc(v_pos_447_);
v_errorMsg_448_ = lean_ctor_get(v___x_445_, 4);
lean_inc(v_errorMsg_448_);
v___x_545_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_446_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_446_);
v___y_515_ = v___x_546_;
goto v___jp_514_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
v___y_515_ = v___x_547_;
goto v___jp_514_;
}
v___jp_449_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_454_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_454_, 0, v_pos_447_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___y_451_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1 + 1, v___y_453_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___y_450_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_452_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_456_);
v___x_458_ = v___x_431_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
v___jp_460_:
{
if (v___y_461_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 1;
v___y_450_ = v___y_462_;
v___y_451_ = v___y_464_;
v___y_452_ = v___y_463_;
v___y_453_ = v___x_465_;
goto v___jp_449_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 0;
v___y_450_ = v___y_462_;
v___y_451_ = v___y_464_;
v___y_452_ = v___y_463_;
v___y_453_ = v___x_466_;
goto v___jp_449_;
}
}
v___jp_467_:
{
lean_object* v___x_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_470_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_468_);
v_fst_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v___x_470_, 1);
lean_inc(v_snd_472_);
lean_dec_ref(v___x_470_);
v___x_473_ = lean_box(0);
v___x_474_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_448_, v___x_473_);
lean_dec(v_errorMsg_448_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 1;
v___x_476_ = lean_unbox(v_snd_472_);
lean_dec(v_snd_472_);
v___y_461_ = v___x_476_;
v___y_462_ = v_messages_469_;
v___y_463_ = v_fst_471_;
v___y_464_ = v___x_475_;
goto v___jp_460_;
}
else
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 0;
v___x_478_ = lean_unbox(v_snd_472_);
lean_dec(v_snd_472_);
v___y_461_ = v___x_478_;
v___y_462_ = v_messages_469_;
v___y_463_ = v_fst_471_;
v___y_464_ = v___x_477_;
goto v___jp_460_;
}
}
v___jp_479_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; size_t v_sz_487_; lean_object* v___x_488_; 
v___x_484_ = lean_unsigned_to_nat(2u);
v___x_485_ = l_Lean_Syntax_getArg(v___y_481_, v___x_484_);
v___x_486_ = l_Lean_Syntax_getArgs(v___x_485_);
lean_dec(v___x_485_);
v_sz_487_ = lean_array_size(v___x_486_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_424_, v___y_483_, v___x_486_, v_sz_487_, v___y_480_, v___y_482_);
lean_dec_ref(v___x_486_);
lean_dec(v___y_483_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___y_468_ = v___y_481_;
v_messages_469_ = v_a_489_;
goto v___jp_467_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___y_481_);
lean_dec(v_errorMsg_448_);
lean_dec(v_pos_447_);
lean_del_object(v___x_431_);
v_a_490_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_488_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
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
lean_dec_ref(v_inputCtx_424_);
v___y_468_ = v___y_499_;
v_messages_469_ = v___y_503_;
goto v___jp_467_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = l_Lean_Syntax_getArg(v___x_507_, v___x_426_);
lean_dec(v___x_507_);
v___x_511_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_501_);
lean_inc_ref(v___y_504_);
lean_inc_ref(v___y_502_);
v___x_512_ = l_Lean_Name_mkStr4(v___y_502_, v___y_504_, v___y_501_, v___x_511_);
v___x_513_ = l_Lean_Syntax_isOfKind(v___x_510_, v___x_512_);
lean_dec(v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_moduleTk_x3f_505_);
lean_dec_ref(v_inputCtx_424_);
v___y_468_ = v___y_499_;
v_messages_469_ = v___y_503_;
goto v___jp_467_;
}
else
{
v___y_480_ = v___y_500_;
v___y_481_ = v___y_499_;
v___y_482_ = v___y_503_;
v___y_483_ = v_moduleTk_x3f_505_;
goto v___jp_479_;
}
}
}
else
{
lean_dec(v___x_507_);
v___y_480_ = v___y_500_;
v___y_481_ = v___y_499_;
v___y_482_ = v___y_503_;
v___y_483_ = v_moduleTk_x3f_505_;
goto v___jp_479_;
}
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_516_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_517_ = l_Lean_Parser_ParserState_allErrors(v___x_445_);
v_sz_518_ = lean_array_size(v___x_517_);
v___x_519_ = ((size_t)0ULL);
lean_inc_ref(v_inputCtx_424_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_424_, v___x_517_, v_sz_518_, v___x_519_, v___x_516_);
lean_dec_ref(v___x_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1));
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2));
v___x_525_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__6));
lean_inc(v___y_515_);
v___x_526_ = l_Lean_Syntax_isOfKind(v___y_515_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_inputCtx_424_);
v___y_468_ = v___y_515_;
v_messages_469_ = v_a_521_;
goto v___jp_467_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = l_Lean_Syntax_getArg(v___y_515_, v___x_426_);
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
lean_dec_ref(v_inputCtx_424_);
v___y_468_ = v___y_515_;
v_messages_469_ = v_a_521_;
goto v___jp_467_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = l_Lean_Syntax_getArg(v___x_527_, v___x_426_);
lean_dec(v___x_527_);
v___x_532_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_531_);
v___x_533_ = l_Lean_Syntax_isOfKind(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
lean_dec_ref(v_inputCtx_424_);
v___y_468_ = v___y_515_;
v_messages_469_ = v_a_521_;
goto v___jp_467_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Lean_Syntax_getArg(v___x_531_, v___x_426_);
lean_dec(v___x_531_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___y_499_ = v___y_515_;
v___y_500_ = v___x_519_;
v___y_501_ = v___x_524_;
v___y_502_ = v___x_522_;
v___y_503_ = v_a_521_;
v___y_504_ = v___x_523_;
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
v___y_500_ = v___x_519_;
v___y_501_ = v___x_524_;
v___y_502_ = v___x_522_;
v___y_503_ = v_a_521_;
v___y_504_ = v___x_523_;
v_moduleTk_x3f_505_ = v___x_536_;
goto v___jp_498_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v___y_515_);
lean_dec(v_errorMsg_448_);
lean_dec(v_pos_447_);
lean_del_object(v___x_431_);
lean_dec_ref(v_inputCtx_424_);
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
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_inputCtx_424_);
v_a_549_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_428_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_428_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_parseHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_424_ = stack[0].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Lean_Parser_parseHeader(v_inputCtx_424_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader___boxed(lean_object* v_inputCtx_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Parser_parseHeader(v_inputCtx_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* v_inputCtx_568_, lean_object* v_pos_569_){
_start:
{
lean_object* v___y_571_; lean_object* v_inputString_581_; lean_object* v_endPos_582_; uint8_t v___x_583_; 
v_inputString_581_ = lean_ctor_get(v_inputCtx_568_, 0);
v_endPos_582_ = lean_ctor_get(v_inputCtx_568_, 3);
v___x_583_ = lean_nat_dec_le(v_pos_569_, v_endPos_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_inc(v_endPos_582_);
lean_inc(v_pos_569_);
lean_inc_ref(v_inputString_581_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v_inputString_581_);
lean_ctor_set(v___x_584_, 1, v_pos_569_);
lean_ctor_set(v___x_584_, 2, v_endPos_582_);
v___y_571_ = v___x_584_;
goto v___jp_570_;
}
else
{
lean_object* v___x_585_; 
lean_inc_n(v_pos_569_, 2);
lean_inc_ref(v_inputString_581_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_inputString_581_);
lean_ctor_set(v___x_585_, 1, v_pos_569_);
lean_ctor_set(v___x_585_, 2, v_pos_569_);
v___y_571_ = v___x_585_;
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_atom_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_inc(v_pos_569_);
lean_inc_ref(v___y_571_);
v___x_572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_572_, 0, v___y_571_);
lean_ctor_set(v___x_572_, 1, v_pos_569_);
lean_ctor_set(v___x_572_, 2, v___y_571_);
lean_ctor_set(v___x_572_, 3, v_pos_569_);
v___x_573_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v_atom_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_574_, 0, v___x_572_);
lean_ctor_set(v_atom_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_array_push(v___x_577_, v_atom_574_);
v___x_579_ = lean_box(2);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_575_);
lean_ctor_set(v___x_580_, 2, v___x_578_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(lean_object* v_inputCtx_586_, lean_object* v_pos_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_586_, v_pos_587_);
lean_dec_ref(v_inputCtx_586_);
return v_res_588_;
}
}
uint8_t l_Lean_Parser_isTerminalCommand(lean_object* v_s_600_){
_start:
{
uint8_t v___y_602_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__1));
lean_inc(v_s_600_);
v___x_606_ = l_Lean_Syntax_isOfKind(v_s_600_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Parser_isTerminalCommand___closed__2));
lean_inc(v_s_600_);
v___x_608_ = l_Lean_Syntax_isOfKind(v_s_600_, v___x_607_);
v___y_602_ = v___x_608_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___x_606_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2));
v___x_604_ = l_Lean_Syntax_isOfKind(v_s_600_, v___x_603_);
return v___x_604_;
}
else
{
lean_dec(v_s_600_);
return v___y_602_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_isTerminalCommand_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_600_ = stack[0].m_obj;
uint8_t v_res_609_;
v_res_609_ = l_Lean_Parser_isTerminalCommand(v_s_600_);
stack->m_num = v_res_609_;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_617_, lean_object* v_pmctx_618_, lean_object* v_pos_619_){
_start:
{
lean_object* v_inputString_620_; lean_object* v_env_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_s_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_s_630_; lean_object* v_errorMsg_631_; 
v_inputString_620_ = lean_ctor_get(v_inputCtx_617_, 0);
v_env_621_ = lean_ctor_get(v_pmctx_618_, 0);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_624_ = l_Lean_Parser_SyntaxStack_empty;
v___x_625_ = l_Lean_Parser_initCacheForInput(v_inputString_620_);
v___x_626_ = lean_box(0);
lean_inc(v_pos_619_);
v_s_627_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_627_, 0, v___x_624_);
lean_ctor_set(v_s_627_, 1, v___x_622_);
lean_ctor_set(v_s_627_, 2, v_pos_619_);
lean_ctor_set(v_s_627_, 3, v___x_625_);
lean_ctor_set(v_s_627_, 4, v___x_626_);
lean_ctor_set(v_s_627_, 5, v___x_623_);
v___x_628_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_621_);
v___x_629_ = l_Lean_Parser_getTokenTable(v_env_621_);
v_s_630_ = l_Lean_Parser_ParserFn_run(v___x_628_, v_inputCtx_617_, v_pmctx_618_, v___x_629_, v_s_627_);
v_errorMsg_631_ = lean_ctor_get(v_s_630_, 4);
if (lean_obj_tag(v_errorMsg_631_) == 0)
{
lean_object* v_pos_632_; 
lean_dec(v_pos_619_);
v_pos_632_ = lean_ctor_get(v_s_630_, 2);
lean_inc(v_pos_632_);
lean_dec_ref(v_s_630_);
return v_pos_632_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_s_630_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_pos_619_, v___x_633_);
lean_dec(v_pos_619_);
return v___x_634_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_640_ = l_Lean_Parser_categoryParser(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_642_ = l_Lean_Parser_withPosition(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_645_; lean_object* v_fn_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_646_ = lean_ctor_get(v___x_645_, 1);
lean_inc_ref(v_fn_646_);
v___x_647_ = lean_apply_2(v_fn_646_, v_a_643_, v_a_644_);
return v___x_647_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_648_, lean_object* v_as_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_b_652_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_648_ = stack[0].m_obj;
lean_object* v_as_649_ = stack[1].m_obj;
size_t v_sz_650_ = stack[2].m_num;
size_t v_i_651_ = stack[3].m_num;
lean_object* v_b_652_ = stack[4].m_obj;
lean_object* v_res_664_;
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_648_, v_as_649_, v_sz_650_, v_i_651_, v_b_652_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_665_, lean_object* v_as_666_, lean_object* v_sz_667_, lean_object* v_i_668_, lean_object* v_b_669_){
_start:
{
size_t v_sz_boxed_670_; size_t v_i_boxed_671_; lean_object* v_res_672_; 
v_sz_boxed_670_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_671_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_665_, v_as_666_, v_sz_boxed_670_, v_i_boxed_671_, v_b_669_);
lean_dec_ref(v_as_666_);
return v_res_672_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_stxStack_673_, uint8_t v___x_674_, lean_object* v_snd_675_, lean_object* v_inputCtx_676_, lean_object* v_pos_677_, lean_object* v_val_678_, lean_object* v___x_679_, lean_object* v_fst_680_, uint8_t v___x_681_, uint8_t v___y_682_, lean_object* v_____r_683_, lean_object* v_pos_684_){
_start:
{
uint8_t v___y_686_; lean_object* v_messages_687_; uint8_t v___y_700_; uint8_t v___y_701_; uint8_t v___y_705_; uint8_t v___x_707_; 
v___x_707_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_673_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_673_);
v___x_709_ = l_Lean_Syntax_getPos_x3f(v___x_708_, v___y_682_);
lean_dec(v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
v___y_705_ = v___x_674_;
goto v___jp_704_;
}
else
{
lean_dec_ref_known(v___x_709_, 1);
v___y_705_ = v___y_682_;
goto v___jp_704_;
}
}
else
{
v___y_705_ = v___x_674_;
goto v___jp_704_;
}
v___jp_685_:
{
if (v___y_686_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_snd_675_);
v___x_688_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_673_);
lean_dec_ref(v_stxStack_673_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_messages_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_box(v___x_674_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_pos_684_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec_ref(v_stxStack_673_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_messages_687_);
lean_ctor_set(v___x_694_, 1, v_snd_675_);
v___x_695_ = lean_box(v___x_674_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_pos_684_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
v___jp_699_:
{
if (v___y_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc_ref(v_stxStack_673_);
v___x_702_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_676_, v_pos_677_, v_stxStack_673_, v_val_678_);
v___x_703_ = l_Lean_MessageLog_add(v___x_702_, v___x_679_);
v___y_686_ = v___y_700_;
v_messages_687_ = v___x_703_;
goto v___jp_685_;
}
else
{
lean_dec_ref(v_val_678_);
lean_dec(v_pos_677_);
lean_dec_ref(v_inputCtx_676_);
v___y_686_ = v___y_700_;
v_messages_687_ = v___x_679_;
goto v___jp_685_;
}
}
v___jp_704_:
{
uint8_t v___x_706_; 
v___x_706_ = lean_unbox(v_fst_680_);
if (v___x_706_ == 0)
{
v___y_700_ = v___y_705_;
v___y_701_ = v___x_681_;
goto v___jp_699_;
}
else
{
v___y_700_ = v___y_705_;
v___y_701_ = v___y_705_;
goto v___jp_699_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stxStack_673_ = stack[0].m_obj;
uint8_t v___x_674_ = stack[1].m_num;
lean_object* v_snd_675_ = stack[2].m_obj;
lean_object* v_inputCtx_676_ = stack[3].m_obj;
lean_object* v_pos_677_ = stack[4].m_obj;
lean_object* v_val_678_ = stack[5].m_obj;
lean_object* v___x_679_ = stack[6].m_obj;
lean_object* v_fst_680_ = stack[7].m_obj;
uint8_t v___x_681_ = stack[8].m_num;
uint8_t v___y_682_ = stack[9].m_num;
lean_object* v_____r_683_ = stack[10].m_obj;
lean_object* v_pos_684_ = stack[11].m_obj;
lean_object* v_res_710_;
v_res_710_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_673_, v___x_674_, v_snd_675_, v_inputCtx_676_, v_pos_677_, v_val_678_, v___x_679_, v_fst_680_, v___x_681_, v___y_682_, v_____r_683_, v_pos_684_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_stxStack_711_, lean_object* v___x_712_, lean_object* v_snd_713_, lean_object* v_inputCtx_714_, lean_object* v_pos_715_, lean_object* v_val_716_, lean_object* v___x_717_, lean_object* v_fst_718_, lean_object* v___x_719_, lean_object* v___y_720_, lean_object* v_____r_721_, lean_object* v_pos_722_){
_start:
{
uint8_t v___x_1772__boxed_723_; uint8_t v___x_1775__boxed_724_; uint8_t v___y_1776__boxed_725_; lean_object* v_res_726_; 
v___x_1772__boxed_723_ = lean_unbox(v___x_712_);
v___x_1775__boxed_724_ = lean_unbox(v___x_719_);
v___y_1776__boxed_725_ = lean_unbox(v___y_720_);
v_res_726_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_711_, v___x_1772__boxed_723_, v_snd_713_, v_inputCtx_714_, v_pos_715_, v_val_716_, v___x_717_, v_fst_718_, v___x_1775__boxed_724_, v___y_1776__boxed_725_, v_____r_721_, v_pos_722_);
lean_dec(v_fst_718_);
return v_res_726_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_728_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_729_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_729_, 0, v___x_728_);
lean_closure_set(v___x_729_, 1, v___x_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_730_, lean_object* v_pmctx_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___y_734_; lean_object* v_snd_738_; lean_object* v_snd_739_; lean_object* v_fst_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_823_; 
v_snd_738_ = lean_ctor_get(v_a_732_, 1);
lean_inc(v_snd_738_);
v_snd_739_ = lean_ctor_get(v_snd_738_, 1);
lean_inc(v_snd_739_);
v_fst_740_ = lean_ctor_get(v_a_732_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_a_732_, 1);
lean_dec(v_unused_824_);
v___x_742_ = v_a_732_;
v_isShared_743_ = v_isSharedCheck_823_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_fst_740_);
lean_dec(v_a_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_823_;
goto v_resetjp_741_;
}
v___jp_733_:
{
if (lean_obj_tag(v___y_734_) == 0)
{
lean_object* v_a_735_; 
lean_dec_ref(v_pmctx_731_);
lean_dec_ref(v_inputCtx_730_);
v_a_735_ = lean_ctor_get(v___y_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___y_734_, 1);
return v_a_735_;
}
else
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v___y_734_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___y_734_, 1);
v_a_732_ = v_a_736_;
goto _start;
}
}
v_resetjp_741_:
{
lean_object* v_fst_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_821_; 
v_fst_744_ = lean_ctor_get(v_snd_738_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_snd_738_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_snd_738_, 1);
lean_dec(v_unused_822_);
v___x_746_ = v_snd_738_;
v_isShared_747_ = v_isSharedCheck_821_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_fst_744_);
lean_dec(v_snd_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_821_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_820_; 
v_fst_748_ = lean_ctor_get(v_snd_739_, 0);
v_snd_749_ = lean_ctor_get(v_snd_739_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_snd_739_);
if (v_isSharedCheck_820_ == 0)
{
v___x_751_ = v_snd_739_;
v_isShared_752_ = v_isSharedCheck_820_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snd_749_);
lean_inc(v_fst_748_);
lean_dec(v_snd_739_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_820_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
uint8_t v___x_753_; 
v___x_753_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_730_, v_fst_740_);
if (v___x_753_ == 0)
{
lean_object* v_env_754_; lean_object* v_inputString_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_stxStack_765_; lean_object* v_pos_766_; lean_object* v_errorMsg_767_; lean_object* v_recoveredErrors_768_; uint8_t v___x_769_; size_t v_sz_770_; size_t v___x_771_; lean_object* v___x_772_; uint8_t v___y_774_; uint8_t v___y_807_; uint8_t v___x_808_; 
v_env_754_ = lean_ctor_get(v_pmctx_731_, 0);
v_inputString_755_ = lean_ctor_get(v_inputCtx_730_, 0);
v___x_756_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_754_);
v___x_757_ = l_Lean_Parser_getTokenTable(v_env_754_);
v___x_758_ = l_Lean_Parser_SyntaxStack_empty;
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_Parser_initCacheForInput(v_inputString_755_);
v___x_761_ = lean_box(0);
v___x_762_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_740_);
v___x_763_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_763_, 0, v___x_758_);
lean_ctor_set(v___x_763_, 1, v___x_759_);
lean_ctor_set(v___x_763_, 2, v_fst_740_);
lean_ctor_set(v___x_763_, 3, v___x_760_);
lean_ctor_set(v___x_763_, 4, v___x_761_);
lean_ctor_set(v___x_763_, 5, v___x_762_);
lean_inc_ref(v_pmctx_731_);
lean_inc_ref_n(v_inputCtx_730_, 2);
v___x_764_ = l_Lean_Parser_ParserFn_run(v___x_756_, v_inputCtx_730_, v_pmctx_731_, v___x_757_, v___x_763_);
v_stxStack_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_stxStack_765_);
v_pos_766_ = lean_ctor_get(v___x_764_, 2);
lean_inc(v_pos_766_);
v_errorMsg_767_ = lean_ctor_get(v___x_764_, 4);
lean_inc(v_errorMsg_767_);
v_recoveredErrors_768_ = lean_ctor_get(v___x_764_, 5);
lean_inc_ref(v_recoveredErrors_768_);
lean_dec_ref(v___x_764_);
v___x_769_ = 1;
v_sz_770_ = lean_array_size(v_recoveredErrors_768_);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_730_, v_recoveredErrors_768_, v_sz_770_, v___x_771_, v_fst_748_);
lean_dec_ref(v_recoveredErrors_768_);
v___x_808_ = lean_unbox(v_fst_744_);
if (v___x_808_ == 0)
{
v___y_807_ = v___x_753_;
goto v___jp_806_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_765_);
if (v___x_809_ == 0)
{
goto v___jp_803_;
}
else
{
v___y_807_ = v___x_753_;
goto v___jp_806_;
}
}
v___jp_773_:
{
if (v___y_774_ == 0)
{
if (lean_obj_tag(v_errorMsg_767_) == 0)
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_snd_749_);
lean_dec(v_fst_744_);
lean_dec(v_fst_740_);
lean_dec_ref(v_pmctx_731_);
lean_dec_ref(v_inputCtx_730_);
v___x_775_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_765_);
lean_dec_ref(v_stxStack_765_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_775_);
lean_ctor_set(v___x_751_, 0, v___x_772_);
v___x_777_ = v___x_751_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_785_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_box(v___y_774_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_777_);
lean_ctor_set(v___x_746_, 0, v___x_778_);
v___x_780_ = v___x_746_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_777_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_780_);
lean_ctor_set(v___x_742_, 0, v_pos_766_);
v___x_782_ = v___x_742_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_pos_766_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_val_786_; uint8_t v_decide_787_; 
lean_del_object(v___x_751_);
lean_del_object(v___x_746_);
lean_del_object(v___x_742_);
v_val_786_ = lean_ctor_get(v_errorMsg_767_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v_errorMsg_767_, 1);
v_decide_787_ = lean_nat_dec_eq(v_pos_766_, v_fst_740_);
lean_dec(v_fst_740_);
if (v_decide_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_box(0);
lean_inc(v_pos_766_);
lean_inc_ref(v_inputCtx_730_);
v___x_789_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_765_, v___x_769_, v_snd_749_, v_inputCtx_730_, v_pos_766_, v_val_786_, v___x_772_, v_fst_744_, v___x_753_, v___y_774_, v___x_788_, v_pos_766_);
lean_dec(v_fst_744_);
v___y_734_ = v___x_789_;
goto v___jp_733_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc(v_pos_766_);
lean_inc_ref(v_pmctx_731_);
lean_inc_ref_n(v_inputCtx_730_, 2);
v___x_790_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_730_, v_pmctx_731_, v_pos_766_);
v___x_791_ = lean_box(0);
v___x_792_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_765_, v___x_769_, v_snd_749_, v_inputCtx_730_, v_pos_766_, v_val_786_, v___x_772_, v_fst_744_, v___x_753_, v___y_774_, v___x_791_, v___x_790_);
lean_dec(v_fst_744_);
v___y_734_ = v___x_792_;
goto v___jp_733_;
}
}
}
else
{
lean_object* v___x_794_; 
lean_dec(v_errorMsg_767_);
lean_dec_ref(v_stxStack_765_);
lean_dec(v_fst_740_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_772_);
v___x_794_ = v___x_751_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_749_);
v___x_794_ = v_reuseFailAlloc_802_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_794_);
v___x_796_ = v___x_746_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_fst_744_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_801_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_796_);
lean_ctor_set(v___x_742_, 0, v_pos_766_);
v___x_798_ = v___x_742_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_pos_766_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_a_732_ = v___x_798_;
goto _start;
}
}
}
}
}
v___jp_803_:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_765_);
v___x_805_ = l_Lean_Syntax_isAntiquot(v___x_804_);
lean_dec(v___x_804_);
v___y_774_ = v___x_805_;
goto v___jp_773_;
}
v___jp_806_:
{
if (v___y_807_ == 0)
{
v___y_774_ = v___x_753_;
goto v___jp_773_;
}
else
{
goto v___jp_803_;
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_snd_749_);
lean_dec_ref(v_pmctx_731_);
lean_inc(v_fst_740_);
v___x_810_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_730_, v_fst_740_);
lean_dec_ref(v_inputCtx_730_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_810_);
v___x_812_ = v___x_751_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_748_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_819_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_812_);
v___x_814_ = v___x_746_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_744_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_814_);
v___x_816_ = v___x_742_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fst_740_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_825_, lean_object* v_pmctx_826_, lean_object* v_mps_827_, lean_object* v_messages_828_){
_start:
{
lean_object* v_pos_829_; uint8_t v_recovering_830_; uint8_t v_hasLeading_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_871_; 
v_pos_829_ = lean_ctor_get(v_mps_827_, 0);
v_recovering_830_ = lean_ctor_get_uint8(v_mps_827_, sizeof(void*)*1);
v_hasLeading_831_ = lean_ctor_get_uint8(v_mps_827_, sizeof(void*)*1 + 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_mps_827_);
if (v_isSharedCheck_871_ == 0)
{
v___x_833_ = v_mps_827_;
v_isShared_834_ = v_isSharedCheck_871_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_pos_829_);
lean_dec(v_mps_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_871_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_stx_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_snd_841_; lean_object* v_snd_842_; lean_object* v_fst_843_; lean_object* v_fst_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_869_; 
v_stx_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_messages_828_);
lean_ctor_set(v___x_836_, 1, v_stx_835_);
v___x_837_ = lean_box(v_recovering_830_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_836_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_pos_829_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_825_, v_pmctx_826_, v___x_839_);
v_snd_841_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_841_);
v_snd_842_ = lean_ctor_get(v_snd_841_, 1);
lean_inc(v_snd_842_);
v_fst_843_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_843_);
lean_dec_ref(v___x_840_);
v_fst_844_ = lean_ctor_get(v_snd_841_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_snd_841_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_snd_841_, 1);
lean_dec(v_unused_870_);
v___x_846_ = v_snd_841_;
v_isShared_847_ = v_isSharedCheck_869_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_fst_844_);
lean_dec(v_snd_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_869_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_868_; 
v_fst_848_ = lean_ctor_get(v_snd_842_, 0);
v_snd_849_ = lean_ctor_get(v_snd_842_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_snd_842_);
if (v_isSharedCheck_868_ == 0)
{
v___x_851_ = v_snd_842_;
v_isShared_852_ = v_isSharedCheck_868_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_snd_842_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_868_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_stx_854_; 
if (v_hasLeading_831_ == 0)
{
v_stx_854_ = v_snd_849_;
goto v___jp_853_;
}
else
{
lean_object* v___x_866_; lean_object* v_fst_867_; 
v___x_866_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_849_);
v_fst_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_fst_867_);
lean_dec_ref(v___x_866_);
v_stx_854_ = v_fst_867_;
goto v___jp_853_;
}
v___jp_853_:
{
uint8_t v___x_855_; lean_object* v___x_857_; 
v___x_855_ = 0;
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_fst_843_);
v___x_857_ = v___x_833_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fst_843_);
v___x_857_ = v_reuseFailAlloc_865_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
uint8_t v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_unbox(v_fst_844_);
lean_dec(v_fst_844_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*1, v___x_858_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*1 + 1, v___x_855_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_fst_848_);
lean_ctor_set(v___x_851_, 0, v___x_857_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_fst_848_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_860_);
lean_ctor_set(v___x_846_, 0, v_stx_854_);
v___x_862_ = v___x_846_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_stx_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_872_, lean_object* v_pmctx_873_, lean_object* v_inst_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_872_, v_pmctx_873_, v_a_875_);
return v___x_876_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_putStr_880_; lean_object* v___x_881_; 
v___x_879_ = lean_get_stdout();
v_putStr_880_ = lean_ctor_get(v___x_879_, 4);
lean_inc_ref(v_putStr_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_apply_2(v_putStr_880_, v_s_877_, lean_box(0));
return v___x_881_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_877_ = stack[0].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_877_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_883_);
return v_res_885_;
}
}
lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_886_){
_start:
{
uint32_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = 10;
v___x_889_ = lean_string_push(v_s_886_, v___x_888_);
v___x_890_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_886_ = stack[0].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_886_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_892_);
return v_res_894_;
}
}
lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_895_, lean_object* v_msg_896_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l_Lean_Message_toString(v_msg_896_, v___y_895_);
v___x_899_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_895_ = stack[0].m_num;
lean_object* v_msg_896_ = stack[1].m_obj;
lean_object* v_res_900_;
v_res_900_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_895_, v_msg_896_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_901_, lean_object* v_msg_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___y_1222__boxed_904_; lean_object* v_res_905_; 
v___y_1222__boxed_904_ = lean_unbox(v___y_901_);
v_res_905_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_1222__boxed_904_, v_msg_902_);
return v_res_905_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_906_, lean_object* v_as_907_, size_t v_i_908_, size_t v_stop_909_, lean_object* v_b_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_eq(v_i_908_, v_stop_909_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_array_uget_borrowed(v_as_907_, v_i_908_);
lean_inc_ref(v_f_906_);
lean_inc(v___x_913_);
v___x_914_ = lean_apply_2(v_f_906_, v___x_913_, lean_box(0));
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; size_t v___x_916_; size_t v___x_917_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_908_, v___x_916_);
v_i_908_ = v___x_917_;
v_b_910_ = v_a_915_;
goto _start;
}
else
{
lean_dec_ref(v_f_906_);
return v___x_914_;
}
}
else
{
lean_object* v___x_919_; 
lean_dec_ref(v_f_906_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_b_910_);
return v___x_919_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_906_ = stack[0].m_obj;
lean_object* v_as_907_ = stack[1].m_obj;
size_t v_i_908_ = stack[2].m_num;
size_t v_stop_909_ = stack[3].m_num;
lean_object* v_b_910_ = stack[4].m_obj;
lean_object* v_res_920_;
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_906_, v_as_907_, v_i_908_, v_stop_909_, v_b_910_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_921_, lean_object* v_as_922_, lean_object* v_i_923_, lean_object* v_stop_924_, lean_object* v_b_925_, lean_object* v___y_926_){
_start:
{
size_t v_i_boxed_927_; size_t v_stop_boxed_928_; lean_object* v_res_929_; 
v_i_boxed_927_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_stop_boxed_928_ = lean_unbox_usize(v_stop_924_);
lean_dec(v_stop_924_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_921_, v_as_922_, v_i_boxed_927_, v_stop_boxed_928_, v_b_925_);
lean_dec_ref(v_as_922_);
return v_res_929_;
}
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_object* v_cs_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_cs_933_ = lean_ctor_get(v_x_931_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_x_931_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_cs_933_);
lean_dec(v_x_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get_size(v_cs_933_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_940_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_cs_933_);
lean_dec_ref(v_f_930_);
if (v_isShared_936_ == 0)
{
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
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_930_, v_cs_933_, v___x_944_, v___x_945_, v___x_939_);
lean_dec_ref(v_cs_933_);
return v___x_946_;
}
}
}
else
{
lean_object* v_vs_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_962_; 
v_vs_948_ = lean_ctor_get(v_x_931_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_962_ == 0)
{
v___x_950_ = v_x_931_;
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_vs_948_);
lean_dec(v_x_931_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_array_get_size(v_vs_948_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
if (v___x_955_ == 0)
{
lean_object* v___x_957_; 
lean_dec_ref(v_vs_948_);
lean_dec_ref(v_f_930_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
lean_ctor_set(v___x_950_, 0, v___x_954_);
v___x_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_954_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
lean_del_object(v___x_950_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = lean_usize_of_nat(v___x_953_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_930_, v_vs_948_, v___x_959_, v___x_960_, v___x_954_);
lean_dec_ref(v_vs_948_);
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_930_ = stack[0].m_obj;
lean_object* v_x_931_ = stack[1].m_obj;
lean_object* v_res_963_;
v_res_963_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_930_, v_x_931_);
stack->m_obj
 = v_res_963_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_964_, lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_, lean_object* v_b_968_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
lean_inc(v___x_971_);
lean_inc_ref(v_f_964_);
v___x_972_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_964_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; size_t v___x_974_; size_t v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_966_, v___x_974_);
v_i_966_ = v___x_975_;
v_b_968_ = v_a_973_;
goto _start;
}
else
{
lean_dec_ref(v_f_964_);
return v___x_972_;
}
}
else
{
lean_object* v___x_977_; 
lean_dec_ref(v_f_964_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_b_968_);
return v___x_977_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_964_ = stack[0].m_obj;
lean_object* v_as_965_ = stack[1].m_obj;
size_t v_i_966_ = stack[2].m_num;
size_t v_stop_967_ = stack[3].m_num;
lean_object* v_b_968_ = stack[4].m_obj;
lean_object* v_res_978_;
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_964_, v_as_965_, v_i_966_, v_stop_967_, v_b_968_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_979_, lean_object* v_as_980_, lean_object* v_i_981_, lean_object* v_stop_982_, lean_object* v_b_983_, lean_object* v___y_984_){
_start:
{
size_t v_i_boxed_985_; size_t v_stop_boxed_986_; lean_object* v_res_987_; 
v_i_boxed_985_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_stop_boxed_986_ = lean_unbox_usize(v_stop_982_);
lean_dec(v_stop_982_);
v_res_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_979_, v_as_980_, v_i_boxed_985_, v_stop_boxed_986_, v_b_983_);
lean_dec_ref(v_as_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_988_, lean_object* v_x_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_988_, v_x_989_);
return v_res_991_;
}
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_992_, lean_object* v_t_993_){
_start:
{
lean_object* v_root_995_; lean_object* v_tail_996_; lean_object* v___x_997_; 
v_root_995_ = lean_ctor_get(v_t_993_, 0);
lean_inc_ref(v_root_995_);
v_tail_996_ = lean_ctor_get(v_t_993_, 1);
lean_inc_ref(v_tail_996_);
lean_dec_ref(v_t_993_);
lean_inc_ref(v_f_992_);
v___x_997_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_992_, v_root_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_997_, 0);
lean_dec(v_unused_1012_);
v___x_999_ = v___x_997_;
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
else
{
lean_dec(v___x_997_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = lean_array_get_size(v_tail_996_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_nat_dec_lt(v___x_1001_, v___x_1002_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1006_; 
lean_dec_ref(v_tail_996_);
lean_dec_ref(v_f_992_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1003_);
v___x_1006_ = v___x_999_;
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
size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_999_);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = lean_usize_of_nat(v___x_1002_);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_992_, v_tail_996_, v___x_1008_, v___x_1009_, v___x_1003_);
lean_dec_ref(v_tail_996_);
return v___x_1010_;
}
}
}
else
{
lean_dec_ref(v_tail_996_);
lean_dec_ref(v_f_992_);
return v___x_997_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_992_ = stack[0].m_obj;
lean_object* v_t_993_ = stack[1].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_992_, v_t_993_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_1014_, lean_object* v_t_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1014_, v_t_1015_);
return v_res_1017_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1018_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_1019_, lean_object* v_x_1020_, size_t v_x_1021_, size_t v_x_1022_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_cs_1024_; lean_object* v___x_1025_; size_t v___x_1026_; lean_object* v_j_1027_; lean_object* v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v_cs_1024_ = lean_ctor_get(v_x_1020_, 0);
lean_inc_ref(v_cs_1024_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1025_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_1026_ = lean_usize_shift_right(v_x_1021_, v_x_1022_);
v_j_1027_ = lean_usize_to_nat(v___x_1026_);
v___x_1028_ = lean_array_get_borrowed(v___x_1025_, v_cs_1024_, v_j_1027_);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_shift_left(v___x_1029_, v_x_1022_);
v___x_1031_ = lean_usize_sub(v___x_1030_, v___x_1029_);
v___x_1032_ = lean_usize_land(v_x_1021_, v___x_1031_);
v___x_1033_ = ((size_t)5ULL);
v___x_1034_ = lean_usize_sub(v_x_1022_, v___x_1033_);
lean_inc(v___x_1028_);
lean_inc_ref(v_f_1019_);
v___x_1035_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1019_, v___x_1028_, v___x_1032_, v___x_1034_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1051_);
v___x_1037_ = v___x_1035_;
v_isShared_1038_ = v_isSharedCheck_1050_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1035_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1050_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_j_1027_, v___x_1039_);
lean_dec(v_j_1027_);
v___x_1041_ = lean_array_get_size(v_cs_1024_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_nat_dec_lt(v___x_1040_, v___x_1041_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1045_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_cs_1024_);
lean_dec_ref(v_f_1019_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1042_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_1037_);
v___x_1047_ = lean_usize_of_nat(v___x_1040_);
lean_dec(v___x_1040_);
v___x_1048_ = lean_usize_of_nat(v___x_1041_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1019_, v_cs_1024_, v___x_1047_, v___x_1048_, v___x_1042_);
lean_dec_ref(v_cs_1024_);
return v___x_1049_;
}
}
}
else
{
lean_dec(v_j_1027_);
lean_dec_ref(v_cs_1024_);
lean_dec_ref(v_f_1019_);
return v___x_1035_;
}
}
else
{
lean_object* v_vs_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1066_; 
v_vs_1052_ = lean_ctor_get(v_x_1020_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1054_ = v_x_1020_;
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_vs_1052_);
lean_dec(v_x_1020_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1066_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = lean_usize_to_nat(v_x_1021_);
v___x_1057_ = lean_array_get_size(v_vs_1052_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v___x_1056_);
lean_dec_ref(v_vs_1052_);
lean_dec_ref(v_f_1019_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1058_);
v___x_1061_ = v___x_1054_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1058_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1054_);
v___x_1063_ = lean_usize_of_nat(v___x_1056_);
lean_dec(v___x_1056_);
v___x_1064_ = lean_usize_of_nat(v___x_1057_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1019_, v_vs_1052_, v___x_1063_, v___x_1064_, v___x_1058_);
lean_dec_ref(v_vs_1052_);
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1019_ = stack[0].m_obj;
lean_object* v_x_1020_ = stack[1].m_obj;
size_t v_x_1021_ = stack[2].m_num;
size_t v_x_1022_ = stack[3].m_num;
lean_object* v_res_1067_;
v_res_1067_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1019_, v_x_1020_, v_x_1021_, v_x_1022_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_){
_start:
{
size_t v_x_1456__boxed_1073_; size_t v_x_1457__boxed_1074_; lean_object* v_res_1075_; 
v_x_1456__boxed_1073_ = lean_unbox_usize(v_x_1070_);
lean_dec(v_x_1070_);
v_x_1457__boxed_1074_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1075_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1068_, v_x_1069_, v_x_1456__boxed_1073_, v_x_1457__boxed_1074_);
return v_res_1075_;
}
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1076_, lean_object* v_t_1077_, lean_object* v_start_1078_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_nat_dec_eq(v_start_1078_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v_root_1082_; lean_object* v_tail_1083_; size_t v_shift_1084_; lean_object* v_tailOff_1085_; uint8_t v___x_1086_; 
v_root_1082_ = lean_ctor_get(v_t_1077_, 0);
lean_inc_ref(v_root_1082_);
v_tail_1083_ = lean_ctor_get(v_t_1077_, 1);
lean_inc_ref(v_tail_1083_);
v_shift_1084_ = lean_ctor_get_usize(v_t_1077_, 4);
v_tailOff_1085_ = lean_ctor_get(v_t_1077_, 3);
lean_inc(v_tailOff_1085_);
lean_dec_ref(v_t_1077_);
v___x_1086_ = lean_nat_dec_le(v_tailOff_1085_, v_start_1078_);
if (v___x_1086_ == 0)
{
size_t v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_tailOff_1085_);
v___x_1087_ = lean_usize_of_nat(v_start_1078_);
lean_inc_ref(v_f_1076_);
v___x_1088_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1076_, v_root_1082_, v___x_1087_, v_shift_1084_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v___x_1088_, 0);
lean_dec(v_unused_1102_);
v___x_1090_ = v___x_1088_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v___x_1088_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_array_get_size(v_tail_1083_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_lt(v___x_1080_, v___x_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref(v_tail_1083_);
lean_dec_ref(v_f_1076_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1093_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
lean_del_object(v___x_1090_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_of_nat(v___x_1092_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1076_, v_tail_1083_, v___x_1098_, v___x_1099_, v___x_1093_);
lean_dec_ref(v_tail_1083_);
return v___x_1100_;
}
}
}
else
{
lean_dec_ref(v_tail_1083_);
lean_dec_ref(v_f_1076_);
return v___x_1088_;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
lean_dec_ref(v_root_1082_);
v___x_1103_ = lean_nat_sub(v_start_1078_, v_tailOff_1085_);
lean_dec(v_tailOff_1085_);
v___x_1104_ = lean_array_get_size(v_tail_1083_);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_nat_dec_lt(v___x_1103_, v___x_1104_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_dec(v___x_1103_);
lean_dec_ref(v_tail_1083_);
lean_dec_ref(v_f_1076_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
return v___x_1107_;
}
else
{
size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_usize_of_nat(v___x_1103_);
lean_dec(v___x_1103_);
v___x_1109_ = lean_usize_of_nat(v___x_1104_);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1076_, v_tail_1083_, v___x_1108_, v___x_1109_, v___x_1105_);
lean_dec_ref(v_tail_1083_);
return v___x_1110_;
}
}
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1076_, v_t_1077_);
return v___x_1111_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1076_ = stack[0].m_obj;
lean_object* v_t_1077_ = stack[1].m_obj;
lean_object* v_start_1078_ = stack[2].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1076_, v_t_1077_, v_start_1078_);
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1113_, lean_object* v_t_1114_, lean_object* v_start_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1113_, v_t_1114_, v_start_1115_);
lean_dec(v_start_1115_);
return v_res_1117_;
}
}
lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1118_, lean_object* v_f_1119_){
_start:
{
lean_object* v_unreported_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_unreported_1121_ = lean_ctor_get(v_log_1118_, 1);
lean_inc_ref(v_unreported_1121_);
lean_dec_ref(v_log_1118_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1119_, v_unreported_1121_, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_1118_ = stack[0].m_obj;
lean_object* v_f_1119_ = stack[1].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1118_, v_f_1119_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1125_, lean_object* v_f_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1125_, v_f_1126_);
return v_res_1128_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1131_ = lean_mk_io_user_error(v___x_1130_);
return v___x_1131_;
}
}
lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1132_, lean_object* v_inputCtx_1133_, lean_object* v_state_1134_, lean_object* v_msgs_1135_, lean_object* v_stxs_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_snd_1143_; lean_object* v_fst_1144_; lean_object* v_fst_1145_; lean_object* v_snd_1146_; uint8_t v___y_1148_; uint8_t v___x_1169_; 
v___x_1138_ = l_Lean_Options_empty;
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_box(0);
lean_inc_ref(v_env_1132_);
v___x_1141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1141_, 0, v_env_1132_);
lean_ctor_set(v___x_1141_, 1, v___x_1138_);
lean_ctor_set(v___x_1141_, 2, v___x_1139_);
lean_ctor_set(v___x_1141_, 3, v___x_1140_);
lean_inc_ref(v_inputCtx_1133_);
v___x_1142_ = l_Lean_Parser_parseCommand(v_inputCtx_1133_, v___x_1141_, v_state_1134_, v_msgs_1135_);
v_snd_1143_ = lean_ctor_get(v___x_1142_, 1);
lean_inc(v_snd_1143_);
v_fst_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_n(v_fst_1144_, 2);
lean_dec_ref(v___x_1142_);
v_fst_1145_ = lean_ctor_get(v_snd_1143_, 0);
lean_inc(v_fst_1145_);
v_snd_1146_ = lean_ctor_get(v_snd_1143_, 1);
lean_inc(v_snd_1146_);
lean_dec(v_snd_1143_);
v___x_1169_ = l_Lean_Parser_isTerminalCommand(v_fst_1144_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_array_push(v_stxs_1136_, v_fst_1144_);
v_state_1134_ = v_fst_1145_;
v_msgs_1135_ = v_snd_1146_;
v_stxs_1136_ = v___x_1170_;
goto _start;
}
else
{
uint8_t v___x_1172_; 
lean_dec(v_fst_1145_);
lean_dec_ref(v_inputCtx_1133_);
lean_dec_ref(v_env_1132_);
v___x_1172_ = l_Lean_MessageLog_hasUnreported(v_snd_1146_);
if (v___x_1172_ == 0)
{
if (v___x_1169_ == 0)
{
lean_dec(v_fst_1144_);
lean_dec_ref(v_stxs_1136_);
v___y_1148_ = v___x_1169_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_snd_1146_);
v___x_1173_ = lean_array_push(v_stxs_1136_, v_fst_1144_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
else
{
uint8_t v___x_1175_; 
lean_dec(v_fst_1144_);
lean_dec_ref(v_stxs_1136_);
v___x_1175_ = 0;
v___y_1148_ = v___x_1175_;
goto v___jp_1147_;
}
}
v___jp_1147_:
{
lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(v___y_1148_);
v___f_1150_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1150_, 0, v___x_1149_);
v___x_1151_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1146_, v___f_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1151_, 0);
lean_dec(v_unused_1160_);
v___x_1153_ = v___x_1151_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v___x_1151_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 1);
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1151_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1151_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1132_ = stack[0].m_obj;
lean_object* v_inputCtx_1133_ = stack[1].m_obj;
lean_object* v_state_1134_ = stack[2].m_obj;
lean_object* v_msgs_1135_ = stack[3].m_obj;
lean_object* v_stxs_1136_ = stack[4].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1132_, v_inputCtx_1133_, v_state_1134_, v_msgs_1135_, v_stxs_1136_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1177_, lean_object* v_inputCtx_1178_, lean_object* v_state_1179_, lean_object* v_msgs_1180_, lean_object* v_stxs_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1177_, v_inputCtx_1178_, v_state_1179_, v_msgs_1180_, v_stxs_1181_);
return v_res_1183_;
}
}
lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1184_, lean_object* v_inputCtx_1185_, lean_object* v_s_1186_, lean_object* v_msgs_1187_, lean_object* v_stxs_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1184_, v_inputCtx_1185_, v_s_1186_, v_msgs_1187_, v_stxs_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_Lean_Parser_testParseModuleAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1184_ = stack[0].m_obj;
lean_object* v_inputCtx_1185_ = stack[1].m_obj;
lean_object* v_s_1186_ = stack[2].m_obj;
lean_object* v_msgs_1187_ = stack[3].m_obj;
lean_object* v_stxs_1188_ = stack[4].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lean_Parser_testParseModuleAux(v_env_1184_, v_inputCtx_1185_, v_s_1186_, v_msgs_1187_, v_stxs_1188_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1192_, lean_object* v_inputCtx_1193_, lean_object* v_s_1194_, lean_object* v_msgs_1195_, lean_object* v_stxs_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Parser_testParseModuleAux(v_env_1192_, v_inputCtx_1193_, v_s_1194_, v_msgs_1195_, v_stxs_1196_);
return v_res_1198_;
}
}
lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1207_, lean_object* v_fname_1208_, lean_object* v_contents_1209_){
_start:
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v_inputCtx_1213_; lean_object* v___x_1214_; 
v___x_1211_ = 1;
v___x_1212_ = lean_string_utf8_byte_size(v_contents_1209_);
v_inputCtx_1213_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1209_, v_fname_1208_, v___x_1211_, v___x_1212_);
lean_inc_ref(v_inputCtx_1213_);
v___x_1214_ = l_Lean_Parser_parseHeader(v_inputCtx_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v_snd_1216_; lean_object* v_fst_1217_; lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v_snd_1216_ = lean_ctor_get(v_a_1215_, 1);
lean_inc(v_snd_1216_);
v_fst_1217_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_fst_1217_);
lean_dec(v_a_1215_);
v_fst_1218_ = lean_ctor_get(v_snd_1216_, 0);
lean_inc(v_fst_1218_);
v_snd_1219_ = lean_ctor_get(v_snd_1216_, 1);
lean_inc(v_snd_1219_);
lean_dec(v_snd_1216_);
v___x_1220_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1221_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1207_, v_inputCtx_1213_, v_fst_1218_, v_snd_1219_, v___x_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1237_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1226_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1227_ = l_Lean_mkListNode(v_a_1222_);
v___x_1228_ = lean_unsigned_to_nat(2u);
v___x_1229_ = lean_mk_empty_array_with_capacity(v___x_1228_);
v___x_1230_ = lean_array_push(v___x_1229_, v_fst_1217_);
v___x_1231_ = lean_array_push(v___x_1230_, v___x_1227_);
v___x_1232_ = lean_box(2);
v___x_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1226_);
lean_ctor_set(v___x_1233_, 2, v___x_1231_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1233_);
v___x_1235_ = v___x_1224_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_fst_1217_);
v_a_1238_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1221_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1221_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_inputCtx_1213_);
lean_dec_ref(v_env_1207_);
v_a_1246_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1214_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1214_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_testParseModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1207_ = stack[0].m_obj;
lean_object* v_fname_1208_ = stack[1].m_obj;
lean_object* v_contents_1209_ = stack[2].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_Lean_Parser_testParseModule(v_env_1207_, v_fname_1208_, v_contents_1209_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1255_, lean_object* v_fname_1256_, lean_object* v_contents_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Parser_testParseModule(v_env_1255_, v_fname_1256_, v_contents_1257_);
return v_res_1259_;
}
}
lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1260_, lean_object* v_fname_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_IO_FS_readFile(v_fname_1261_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_Parser_testParseModule(v_env_1260_, v_fname_1261_, v_a_1264_);
return v___x_1265_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_fname_1261_);
lean_dec_ref(v_env_1260_);
v_a_1266_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1263_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1263_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_testParseFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1260_ = stack[0].m_obj;
lean_object* v_fname_1261_ = stack[1].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l_Lean_Parser_testParseFile(v_env_1260_, v_fname_1261_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1275_, lean_object* v_fname_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Parser_testParseFile(v_env_1275_, v_fname_1276_);
return v_res_1278_;
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
