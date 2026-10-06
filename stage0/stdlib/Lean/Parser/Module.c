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
v___x_212_ = l_Lean_FileMap_toPosition(v___y_209_, v___y_211_);
lean_dec(v___y_211_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = 2;
v___x_215_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0));
v___x_216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_216_, 0, v___y_208_);
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
v___y_208_ = v_fileName_219_;
v___y_209_ = v_fileMap_220_;
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
v___y_208_ = v_fileName_219_;
v___y_209_ = v_fileMap_220_;
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
lean_object* v___y_296_; lean_object* v_messages_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v_messages_305_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v_allTk_x3f_339_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v_metaTk_x3f_353_; lean_object* v_pubTk_x3f_365_; lean_object* v___x_375_; uint8_t v___x_376_; 
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
if (lean_obj_tag(v___y_312_) == 1)
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_dec_ref_known(v___y_312_, 1);
lean_dec(v___y_313_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_333_; 
v_isSharedCheck_333_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___y_311_, 0);
lean_dec(v_unused_334_);
v___x_316_ = v___y_311_;
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___y_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_333_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
if (v___y_314_ == 0)
{
lean_del_object(v___x_316_);
lean_dec_ref_known(v___y_312_, 1);
lean_dec(v___y_313_);
v_a_286_ = v_b_283_;
goto v___jp_285_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_val_318_ = lean_ctor_get(v___y_312_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___y_312_, 1);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11));
v___x_320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_313_, v___y_314_);
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
lean_dec(v___y_313_);
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
lean_dec(v___y_338_);
v___y_311_ = v___y_337_;
v___y_312_ = v_allTk_x3f_339_;
v___y_313_ = v___x_345_;
v___y_314_ = v___x_342_;
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
v___y_303_ = v_allTk_x3f_339_;
v___y_304_ = v___y_338_;
v_messages_305_ = v___x_349_;
goto v___jp_302_;
}
else
{
lean_dec(v___y_337_);
v___y_303_ = v_allTk_x3f_339_;
v___y_304_ = v___y_338_;
v_messages_305_ = v_b_283_;
goto v___jp_302_;
}
}
}
else
{
lean_dec(v___y_338_);
v___y_311_ = v___y_337_;
v___y_312_ = v_allTk_x3f_339_;
v___y_313_ = v___x_345_;
v___y_314_ = v___x_342_;
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
lean_object* v___x_422_; uint32_t v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = 0;
v___x_424_ = l_Lean_mkEmptyEnvironment(v___x_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_544_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_544_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_544_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_544_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_fn_430_; lean_object* v_inputString_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_stxStack_442_; lean_object* v_pos_443_; lean_object* v_errorMsg_444_; lean_object* v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; uint8_t v___y_449_; lean_object* v___y_457_; uint8_t v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_464_; lean_object* v_messages_465_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; size_t v___y_479_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; size_t v___y_500_; lean_object* v_moduleTk_x3f_501_; lean_object* v___y_511_; uint8_t v___x_541_; 
v___x_429_ = l_Lean_Parser_Module_header;
v_fn_430_ = lean_ctor_get(v___x_429_, 1);
v_inputString_431_ = lean_ctor_get(v_inputCtx_420_, 0);
lean_inc(v_a_425_);
v___x_432_ = l_Lean_Parser_getTokenTable(v_a_425_);
v___x_433_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
lean_inc_ref(v_fn_430_);
v___x_434_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_434_, 0, v___x_433_);
lean_closure_set(v___x_434_, 1, v_fn_430_);
v___x_435_ = l_Lean_Parser_Module_updateTokens(v___x_432_);
v___x_436_ = l_Lean_Options_empty;
v___x_437_ = lean_box(0);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_439_, 0, v_a_425_);
lean_ctor_set(v___x_439_, 1, v___x_436_);
lean_ctor_set(v___x_439_, 2, v___x_437_);
lean_ctor_set(v___x_439_, 3, v___x_438_);
v___x_440_ = l_Lean_Parser_mkParserState(v_inputString_431_);
lean_inc_ref(v_inputCtx_420_);
v___x_441_ = l_Lean_Parser_ParserFn_run(v___x_434_, v_inputCtx_420_, v___x_439_, v___x_435_, v___x_440_);
v_stxStack_442_ = lean_ctor_get(v___x_441_, 0);
v_pos_443_ = lean_ctor_get(v___x_441_, 2);
lean_inc(v_pos_443_);
v_errorMsg_444_ = lean_ctor_get(v___x_441_, 4);
lean_inc(v_errorMsg_444_);
v___x_541_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_442_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_442_);
v___y_511_ = v___x_542_;
goto v___jp_510_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
v___y_511_ = v___x_543_;
goto v___jp_510_;
}
v___jp_445_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_450_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_450_, 0, v_pos_443_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___y_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1 + 1, v___y_449_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___y_447_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___y_446_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_452_);
v___x_454_ = v___x_427_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
v___jp_456_:
{
if (v___y_458_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 1;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___y_460_;
v___y_449_ = v___x_461_;
goto v___jp_445_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
v___y_446_ = v___y_457_;
v___y_447_ = v___y_459_;
v___y_448_ = v___y_460_;
v___y_449_ = v___x_462_;
goto v___jp_445_;
}
}
v___jp_463_:
{
lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_466_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v___y_464_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_466_);
v___x_469_ = lean_box(0);
v___x_470_ = l_instBEqOption_beq___at___00Lean_Parser_parseHeader_spec__0(v_errorMsg_444_, v___x_469_);
lean_dec(v_errorMsg_444_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 1;
v___x_472_ = lean_unbox(v_snd_468_);
lean_dec(v_snd_468_);
v___y_457_ = v_fst_467_;
v___y_458_ = v___x_472_;
v___y_459_ = v_messages_465_;
v___y_460_ = v___x_471_;
goto v___jp_456_;
}
else
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 0;
v___x_474_ = lean_unbox(v_snd_468_);
lean_dec(v_snd_468_);
v___y_457_ = v_fst_467_;
v___y_458_ = v___x_474_;
v___y_459_ = v_messages_465_;
v___y_460_ = v___x_473_;
goto v___jp_456_;
}
}
v___jp_475_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; size_t v_sz_483_; lean_object* v___x_484_; 
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = l_Lean_Syntax_getArg(v___y_477_, v___x_480_);
v___x_482_ = l_Lean_Syntax_getArgs(v___x_481_);
lean_dec(v___x_481_);
v_sz_483_ = lean_array_size(v___x_482_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_420_, v___y_478_, v___x_482_, v_sz_483_, v___y_479_, v___y_476_);
lean_dec_ref(v___x_482_);
lean_dec(v___y_478_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___y_464_ = v___y_477_;
v_messages_465_ = v_a_485_;
goto v___jp_463_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v___y_477_);
lean_dec(v_errorMsg_444_);
lean_dec(v_pos_443_);
lean_del_object(v___x_427_);
v_a_486_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
v___jp_494_:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = l_Lean_Syntax_getArg(v___y_497_, v___x_502_);
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
v___y_464_ = v___y_497_;
v_messages_465_ = v___y_495_;
goto v___jp_463_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_506_ = l_Lean_Syntax_getArg(v___x_503_, v___x_422_);
lean_dec(v___x_503_);
v___x_507_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__1));
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc_ref(v___y_496_);
v___x_508_ = l_Lean_Name_mkStr4(v___y_496_, v___y_498_, v___y_499_, v___x_507_);
v___x_509_ = l_Lean_Syntax_isOfKind(v___x_506_, v___x_508_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v_moduleTk_x3f_501_);
lean_dec_ref(v_inputCtx_420_);
v___y_464_ = v___y_497_;
v_messages_465_ = v___y_495_;
goto v___jp_463_;
}
else
{
v___y_476_ = v___y_495_;
v___y_477_ = v___y_497_;
v___y_478_ = v_moduleTk_x3f_501_;
v___y_479_ = v___y_500_;
goto v___jp_475_;
}
}
}
else
{
lean_dec(v___x_503_);
v___y_476_ = v___y_495_;
v___y_477_ = v___y_497_;
v___y_478_ = v_moduleTk_x3f_501_;
v___y_479_ = v___y_500_;
goto v___jp_475_;
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_512_ = lean_obj_once(&l_Lean_Parser_parseHeader___closed__4, &l_Lean_Parser_parseHeader___closed__4_once, _init_l_Lean_Parser_parseHeader___closed__4);
v___x_513_ = l_Lean_Parser_ParserState_allErrors(v___x_441_);
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
v___y_464_ = v___y_511_;
v_messages_465_ = v_a_517_;
goto v___jp_463_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = l_Lean_Syntax_getArg(v___y_511_, v___x_422_);
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
v___y_464_ = v___y_511_;
v_messages_465_ = v_a_517_;
goto v___jp_463_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = l_Lean_Syntax_getArg(v___x_523_, v___x_422_);
lean_dec(v___x_523_);
v___x_528_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__8));
lean_inc(v___x_527_);
v___x_529_ = l_Lean_Syntax_isOfKind(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v___x_527_);
lean_dec_ref(v_inputCtx_420_);
v___y_464_ = v___y_511_;
v_messages_465_ = v_a_517_;
goto v___jp_463_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = l_Lean_Syntax_getArg(v___x_527_, v___x_422_);
lean_dec(v___x_527_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___y_495_ = v_a_517_;
v___y_496_ = v___x_518_;
v___y_497_ = v___y_511_;
v___y_498_ = v___x_519_;
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
v___y_495_ = v_a_517_;
v___y_496_ = v___x_518_;
v___y_497_ = v___y_511_;
v___y_498_ = v___x_519_;
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
lean_dec(v_errorMsg_444_);
lean_dec(v_pos_443_);
lean_del_object(v___x_427_);
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
v_a_545_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_424_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_424_);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* v_inputCtx_611_, lean_object* v_pmctx_612_, lean_object* v_pos_613_){
_start:
{
lean_object* v_inputString_614_; lean_object* v_env_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_s_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_s_624_; lean_object* v_errorMsg_625_; 
v_inputString_614_ = lean_ctor_get(v_inputCtx_611_, 0);
v_env_615_ = lean_ctor_get(v_pmctx_612_, 0);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
v___x_618_ = l_Lean_Parser_SyntaxStack_empty;
v___x_619_ = l_Lean_Parser_initCacheForInput(v_inputString_614_);
v___x_620_ = lean_box(0);
lean_inc(v_pos_613_);
v_s_621_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_s_621_, 0, v___x_618_);
lean_ctor_set(v_s_621_, 1, v___x_616_);
lean_ctor_set(v_s_621_, 2, v_pos_613_);
lean_ctor_set(v_s_621_, 3, v___x_619_);
lean_ctor_set(v_s_621_, 4, v___x_620_);
lean_ctor_set(v_s_621_, 5, v___x_617_);
v___x_622_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1));
lean_inc_ref(v_env_615_);
v___x_623_ = l_Lean_Parser_getTokenTable(v_env_615_);
v_s_624_ = l_Lean_Parser_ParserFn_run(v___x_622_, v_inputCtx_611_, v_pmctx_612_, v___x_623_, v_s_621_);
v_errorMsg_625_ = lean_ctor_get(v_s_624_, 4);
if (lean_obj_tag(v_errorMsg_625_) == 0)
{
lean_object* v_pos_626_; 
lean_dec(v_pos_613_);
v_pos_626_ = lean_ctor_get(v_s_624_, 2);
lean_inc(v_pos_626_);
lean_dec_ref(v_s_624_);
return v_pos_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec_ref(v_s_624_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_pos_613_, v___x_627_);
lean_dec(v_pos_613_);
return v___x_628_;
}
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__2(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = ((lean_object*)(l_Lean_Parser_topLevelCommandParserFn___closed__1));
v___x_634_ = l_Lean_Parser_categoryParser(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Parser_topLevelCommandParserFn___closed__3(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__2, &l_Lean_Parser_topLevelCommandParserFn___closed__2_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__2);
v___x_636_ = l_Lean_Parser_withPosition(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_639_; lean_object* v_fn_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&l_Lean_Parser_topLevelCommandParserFn___closed__3, &l_Lean_Parser_topLevelCommandParserFn___closed__3_once, _init_l_Lean_Parser_topLevelCommandParserFn___closed__3);
v_fn_640_ = lean_ctor_get(v___x_639_, 1);
lean_inc_ref(v_fn_640_);
v___x_641_ = lean_apply_2(v_fn_640_, v_a_637_, v_a_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(lean_object* v_inputCtx_642_, lean_object* v_as_643_, size_t v_sz_644_, size_t v_i_645_, lean_object* v_b_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_lt(v_i_645_, v_sz_644_);
if (v___x_647_ == 0)
{
lean_dec_ref(v_inputCtx_642_);
return v_b_646_;
}
else
{
lean_object* v_a_648_; lean_object* v_snd_649_; lean_object* v_fst_650_; lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_654_; size_t v___x_655_; size_t v___x_656_; 
v_a_648_ = lean_array_uget_borrowed(v_as_643_, v_i_645_);
v_snd_649_ = lean_ctor_get(v_a_648_, 1);
v_fst_650_ = lean_ctor_get(v_a_648_, 0);
v_fst_651_ = lean_ctor_get(v_snd_649_, 0);
v_snd_652_ = lean_ctor_get(v_snd_649_, 1);
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_inc(v_fst_650_);
lean_inc_ref(v_inputCtx_642_);
v___x_653_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_642_, v_fst_650_, v_fst_651_, v_snd_652_);
v___x_654_ = l_Lean_MessageLog_add(v___x_653_, v_b_646_);
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_add(v_i_645_, v___x_655_);
v_i_645_ = v___x_656_;
v_b_646_ = v___x_654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(lean_object* v_inputCtx_658_, lean_object* v_as_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_b_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_664_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_658_, v_as_659_, v_sz_boxed_663_, v_i_boxed_664_, v_b_662_);
lean_dec_ref(v_as_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(lean_object* v_stxStack_666_, uint8_t v___x_667_, lean_object* v_snd_668_, lean_object* v_inputCtx_669_, lean_object* v_pos_670_, lean_object* v_val_671_, lean_object* v___x_672_, lean_object* v_fst_673_, uint8_t v___x_674_, uint8_t v___y_675_, lean_object* v_____r_676_, lean_object* v_pos_677_){
_start:
{
uint8_t v___y_679_; lean_object* v_messages_680_; uint8_t v___y_693_; uint8_t v___y_694_; uint8_t v___y_698_; uint8_t v___x_700_; 
v___x_700_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_666_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_666_);
v___x_702_ = l_Lean_Syntax_getPos_x3f(v___x_701_, v___y_675_);
lean_dec(v___x_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
v___y_698_ = v___x_667_;
goto v___jp_697_;
}
else
{
lean_dec_ref_known(v___x_702_, 1);
v___y_698_ = v___y_675_;
goto v___jp_697_;
}
}
else
{
v___y_698_ = v___x_667_;
goto v___jp_697_;
}
v___jp_678_:
{
if (v___y_679_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_snd_668_);
v___x_681_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_666_);
lean_dec_ref(v_stxStack_666_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_messages_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_box(v___x_667_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_pos_677_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_stxStack_666_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_messages_680_);
lean_ctor_set(v___x_687_, 1, v_snd_668_);
v___x_688_ = lean_box(v___x_667_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_pos_677_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
v___jp_692_:
{
if (v___y_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_inc_ref(v_stxStack_666_);
v___x_695_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(v_inputCtx_669_, v_pos_670_, v_stxStack_666_, v_val_671_);
v___x_696_ = l_Lean_MessageLog_add(v___x_695_, v___x_672_);
v___y_679_ = v___y_693_;
v_messages_680_ = v___x_696_;
goto v___jp_678_;
}
else
{
lean_dec_ref(v_val_671_);
lean_dec(v_pos_670_);
lean_dec_ref(v_inputCtx_669_);
v___y_679_ = v___y_693_;
v_messages_680_ = v___x_672_;
goto v___jp_678_;
}
}
v___jp_697_:
{
uint8_t v___x_699_; 
v___x_699_ = lean_unbox(v_fst_673_);
if (v___x_699_ == 0)
{
v___y_693_ = v___y_698_;
v___y_694_ = v___x_674_;
goto v___jp_692_;
}
else
{
v___y_693_ = v___y_698_;
v___y_694_ = v___y_698_;
goto v___jp_692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(lean_object* v_stxStack_703_, lean_object* v___x_704_, lean_object* v_snd_705_, lean_object* v_inputCtx_706_, lean_object* v_pos_707_, lean_object* v_val_708_, lean_object* v___x_709_, lean_object* v_fst_710_, lean_object* v___x_711_, lean_object* v___y_712_, lean_object* v_____r_713_, lean_object* v_pos_714_){
_start:
{
uint8_t v___x_1762__boxed_715_; uint8_t v___x_1765__boxed_716_; uint8_t v___y_1766__boxed_717_; lean_object* v_res_718_; 
v___x_1762__boxed_715_ = lean_unbox(v___x_704_);
v___x_1765__boxed_716_ = lean_unbox(v___x_711_);
v___y_1766__boxed_717_ = lean_unbox(v___y_712_);
v_res_718_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_703_, v___x_1762__boxed_715_, v_snd_705_, v_inputCtx_706_, v_pos_707_, v_val_708_, v___x_709_, v_fst_710_, v___x_1765__boxed_716_, v___y_1766__boxed_717_, v_____r_713_, v_pos_714_);
lean_dec(v_fst_710_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
v___x_720_ = ((lean_object*)(l_Lean_Parser_parseHeader___closed__0));
v___x_721_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_721_, 0, v___x_720_);
lean_closure_set(v___x_721_, 1, v___x_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(lean_object* v_inputCtx_722_, lean_object* v_pmctx_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___y_726_; lean_object* v_snd_730_; lean_object* v_snd_731_; lean_object* v_fst_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_815_; 
v_snd_730_ = lean_ctor_get(v_a_724_, 1);
lean_inc(v_snd_730_);
v_snd_731_ = lean_ctor_get(v_snd_730_, 1);
lean_inc(v_snd_731_);
v_fst_732_ = lean_ctor_get(v_a_724_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_a_724_, 1);
lean_dec(v_unused_816_);
v___x_734_ = v_a_724_;
v_isShared_735_ = v_isSharedCheck_815_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_fst_732_);
lean_dec(v_a_724_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_815_;
goto v_resetjp_733_;
}
v___jp_725_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_object* v_a_727_; 
lean_dec_ref(v_pmctx_723_);
lean_dec_ref(v_inputCtx_722_);
v_a_727_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___y_726_, 1);
return v_a_727_;
}
else
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___y_726_, 1);
v_a_724_ = v_a_728_;
goto _start;
}
}
v_resetjp_733_:
{
lean_object* v_fst_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_813_; 
v_fst_736_ = lean_ctor_get(v_snd_730_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_snd_730_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_snd_730_, 1);
lean_dec(v_unused_814_);
v___x_738_ = v_snd_730_;
v_isShared_739_ = v_isSharedCheck_813_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_fst_736_);
lean_dec(v_snd_730_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_813_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_812_; 
v_fst_740_ = lean_ctor_get(v_snd_731_, 0);
v_snd_741_ = lean_ctor_get(v_snd_731_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_snd_731_);
if (v_isSharedCheck_812_ == 0)
{
v___x_743_ = v_snd_731_;
v_isShared_744_ = v_isSharedCheck_812_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_snd_741_);
lean_inc(v_fst_740_);
lean_dec(v_snd_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_812_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_722_, v_fst_732_);
if (v___x_745_ == 0)
{
lean_object* v_env_746_; lean_object* v_inputString_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_stxStack_757_; lean_object* v_pos_758_; lean_object* v_errorMsg_759_; lean_object* v_recoveredErrors_760_; uint8_t v___x_761_; size_t v_sz_762_; size_t v___x_763_; lean_object* v___x_764_; uint8_t v___y_766_; uint8_t v___y_799_; uint8_t v___x_800_; 
v_env_746_ = lean_ctor_get(v_pmctx_723_, 0);
v_inputString_747_ = lean_ctor_get(v_inputCtx_722_, 0);
v___x_748_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
lean_inc_ref(v_env_746_);
v___x_749_ = l_Lean_Parser_getTokenTable(v_env_746_);
v___x_750_ = l_Lean_Parser_SyntaxStack_empty;
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = l_Lean_Parser_initCacheForInput(v_inputString_747_);
v___x_753_ = lean_box(0);
v___x_754_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0));
lean_inc(v_fst_732_);
v___x_755_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_755_, 0, v___x_750_);
lean_ctor_set(v___x_755_, 1, v___x_751_);
lean_ctor_set(v___x_755_, 2, v_fst_732_);
lean_ctor_set(v___x_755_, 3, v___x_752_);
lean_ctor_set(v___x_755_, 4, v___x_753_);
lean_ctor_set(v___x_755_, 5, v___x_754_);
lean_inc_ref(v_pmctx_723_);
lean_inc_ref_n(v_inputCtx_722_, 2);
v___x_756_ = l_Lean_Parser_ParserFn_run(v___x_748_, v_inputCtx_722_, v_pmctx_723_, v___x_749_, v___x_755_);
v_stxStack_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_ref(v_stxStack_757_);
v_pos_758_ = lean_ctor_get(v___x_756_, 2);
lean_inc(v_pos_758_);
v_errorMsg_759_ = lean_ctor_get(v___x_756_, 4);
lean_inc(v_errorMsg_759_);
v_recoveredErrors_760_ = lean_ctor_get(v___x_756_, 5);
lean_inc_ref(v_recoveredErrors_760_);
lean_dec_ref(v___x_756_);
v___x_761_ = 1;
v_sz_762_ = lean_array_size(v_recoveredErrors_760_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_722_, v_recoveredErrors_760_, v_sz_762_, v___x_763_, v_fst_740_);
lean_dec_ref(v_recoveredErrors_760_);
v___x_800_ = lean_unbox(v_fst_736_);
if (v___x_800_ == 0)
{
v___y_799_ = v___x_745_;
goto v___jp_798_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_757_);
if (v___x_801_ == 0)
{
goto v___jp_795_;
}
else
{
v___y_799_ = v___x_745_;
goto v___jp_798_;
}
}
v___jp_765_:
{
if (v___y_766_ == 0)
{
if (lean_obj_tag(v_errorMsg_759_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec(v_snd_741_);
lean_dec(v_fst_736_);
lean_dec(v_fst_732_);
lean_dec_ref(v_pmctx_723_);
lean_dec_ref(v_inputCtx_722_);
v___x_767_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_757_);
lean_dec_ref(v_stxStack_757_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_767_);
lean_ctor_set(v___x_743_, 0, v___x_764_);
v___x_769_ = v___x_743_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_777_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = lean_box(v___y_766_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_769_);
lean_ctor_set(v___x_738_, 0, v___x_770_);
v___x_772_ = v___x_738_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_769_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_772_);
lean_ctor_set(v___x_734_, 0, v_pos_758_);
v___x_774_ = v___x_734_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_pos_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_val_778_; uint8_t v_decide_779_; 
lean_del_object(v___x_743_);
lean_del_object(v___x_738_);
lean_del_object(v___x_734_);
v_val_778_ = lean_ctor_get(v_errorMsg_759_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_errorMsg_759_, 1);
v_decide_779_ = lean_nat_dec_eq(v_pos_758_, v_fst_732_);
lean_dec(v_fst_732_);
if (v_decide_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
lean_inc(v_pos_758_);
lean_inc_ref(v_inputCtx_722_);
v___x_781_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_757_, v___x_761_, v_snd_741_, v_inputCtx_722_, v_pos_758_, v_val_778_, v___x_764_, v_fst_736_, v___x_745_, v___y_766_, v___x_780_, v_pos_758_);
lean_dec(v_fst_736_);
v___y_726_ = v___x_781_;
goto v___jp_725_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc(v_pos_758_);
lean_inc_ref(v_pmctx_723_);
lean_inc_ref_n(v_inputCtx_722_, 2);
v___x_782_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(v_inputCtx_722_, v_pmctx_723_, v_pos_758_);
v___x_783_ = lean_box(0);
v___x_784_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_stxStack_757_, v___x_761_, v_snd_741_, v_inputCtx_722_, v_pos_758_, v_val_778_, v___x_764_, v_fst_736_, v___x_745_, v___y_766_, v___x_783_, v___x_782_);
lean_dec(v_fst_736_);
v___y_726_ = v___x_784_;
goto v___jp_725_;
}
}
}
else
{
lean_object* v___x_786_; 
lean_dec(v_errorMsg_759_);
lean_dec_ref(v_stxStack_757_);
lean_dec(v_fst_732_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_764_);
v___x_786_ = v___x_743_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_741_);
v___x_786_ = v_reuseFailAlloc_794_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_786_);
v___x_788_ = v___x_738_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_788_);
lean_ctor_set(v___x_734_, 0, v_pos_758_);
v___x_790_ = v___x_734_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_pos_758_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_a_724_ = v___x_790_;
goto _start;
}
}
}
}
}
v___jp_795_:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_757_);
v___x_797_ = l_Lean_Syntax_isAntiquot(v___x_796_);
lean_dec(v___x_796_);
v___y_766_ = v___x_797_;
goto v___jp_765_;
}
v___jp_798_:
{
if (v___y_799_ == 0)
{
v___y_766_ = v___x_745_;
goto v___jp_765_;
}
else
{
goto v___jp_795_;
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_snd_741_);
lean_dec_ref(v_pmctx_723_);
lean_inc(v_fst_732_);
v___x_802_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_722_, v_fst_732_);
lean_dec_ref(v_inputCtx_722_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_802_);
v___x_804_ = v___x_743_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_740_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_802_);
v___x_804_ = v_reuseFailAlloc_811_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_804_);
v___x_806_ = v___x_738_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_806_);
v___x_808_ = v___x_734_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fst_732_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* v_inputCtx_817_, lean_object* v_pmctx_818_, lean_object* v_mps_819_, lean_object* v_messages_820_){
_start:
{
lean_object* v_pos_821_; uint8_t v_recovering_822_; uint8_t v_hasLeading_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_863_; 
v_pos_821_ = lean_ctor_get(v_mps_819_, 0);
v_recovering_822_ = lean_ctor_get_uint8(v_mps_819_, sizeof(void*)*1);
v_hasLeading_823_ = lean_ctor_get_uint8(v_mps_819_, sizeof(void*)*1 + 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_mps_819_);
if (v_isSharedCheck_863_ == 0)
{
v___x_825_ = v_mps_819_;
v_isShared_826_ = v_isSharedCheck_863_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_pos_821_);
lean_dec(v_mps_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_863_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_stx_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_snd_833_; lean_object* v_snd_834_; lean_object* v_fst_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_861_; 
v_stx_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_messages_820_);
lean_ctor_set(v___x_828_, 1, v_stx_827_);
v___x_829_ = lean_box(v_recovering_822_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_pos_821_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_817_, v_pmctx_818_, v___x_831_);
v_snd_833_ = lean_ctor_get(v___x_832_, 1);
lean_inc(v_snd_833_);
v_snd_834_ = lean_ctor_get(v_snd_833_, 1);
lean_inc(v_snd_834_);
v_fst_835_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_fst_835_);
lean_dec_ref(v___x_832_);
v_fst_836_ = lean_ctor_get(v_snd_833_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v_snd_833_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_snd_833_, 1);
lean_dec(v_unused_862_);
v___x_838_ = v_snd_833_;
v_isShared_839_ = v_isSharedCheck_861_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_fst_836_);
lean_dec(v_snd_833_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_861_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_860_; 
v_fst_840_ = lean_ctor_get(v_snd_834_, 0);
v_snd_841_ = lean_ctor_get(v_snd_834_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_snd_834_);
if (v_isSharedCheck_860_ == 0)
{
v___x_843_ = v_snd_834_;
v_isShared_844_ = v_isSharedCheck_860_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_840_);
lean_dec(v_snd_834_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_860_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_stx_846_; 
if (v_hasLeading_823_ == 0)
{
v_stx_846_ = v_snd_841_;
goto v___jp_845_;
}
else
{
lean_object* v___x_858_; lean_object* v_fst_859_; 
v___x_858_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(v_snd_841_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
lean_dec_ref(v___x_858_);
v_stx_846_ = v_fst_859_;
goto v___jp_845_;
}
v___jp_845_:
{
uint8_t v___x_847_; lean_object* v___x_849_; 
v___x_847_ = 0;
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_fst_835_);
v___x_849_ = v___x_825_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_fst_835_);
v___x_849_ = v_reuseFailAlloc_857_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
uint8_t v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_unbox(v_fst_836_);
lean_dec(v_fst_836_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_850_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1 + 1, v___x_847_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_fst_840_);
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_852_ = v___x_843_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_fst_840_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_852_);
lean_ctor_set(v___x_838_, 0, v_stx_846_);
v___x_854_ = v___x_838_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_stx_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1(lean_object* v_inputCtx_864_, lean_object* v_pmctx_865_, lean_object* v_inst_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_864_, v_pmctx_865_, v_a_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* v_s_869_){
_start:
{
lean_object* v___x_871_; lean_object* v_putStr_872_; lean_object* v___x_873_; 
v___x_871_ = lean_get_stdout();
v_putStr_872_ = lean_ctor_get(v___x_871_, 4);
lean_inc_ref(v_putStr_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = lean_apply_2(v_putStr_872_, v_s_869_, lean_box(0));
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* v_s_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* v_s_877_){
_start:
{
uint32_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = 10;
v___x_880_ = lean_string_push(v_s_877_, v___x_879_);
v___x_881_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* v_s_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t v___y_885_, lean_object* v_msg_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = l_Lean_Message_toString(v_msg_886_, v___y_885_);
v___x_889_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* v___y_890_, lean_object* v_msg_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___y_1213__boxed_893_; lean_object* v_res_894_; 
v___y_1213__boxed_893_ = lean_unbox(v___y_890_);
v_res_894_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(v___y_1213__boxed_893_, v_msg_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(lean_object* v_f_895_, lean_object* v_as_896_, size_t v_i_897_, size_t v_stop_898_, lean_object* v_b_899_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_eq(v_i_897_, v_stop_898_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_array_uget_borrowed(v_as_896_, v_i_897_);
lean_inc_ref(v_f_895_);
lean_inc(v___x_902_);
v___x_903_ = lean_apply_2(v_f_895_, v___x_902_, lean_box(0));
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; size_t v___x_905_; size_t v___x_906_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = ((size_t)1ULL);
v___x_906_ = lean_usize_add(v_i_897_, v___x_905_);
v_i_897_ = v___x_906_;
v_b_899_ = v_a_904_;
goto _start;
}
else
{
lean_dec_ref(v_f_895_);
return v___x_903_;
}
}
else
{
lean_object* v___x_908_; 
lean_dec_ref(v_f_895_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_b_899_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(lean_object* v_f_909_, lean_object* v_as_910_, lean_object* v_i_911_, lean_object* v_stop_912_, lean_object* v_b_913_, lean_object* v___y_914_){
_start:
{
size_t v_i_boxed_915_; size_t v_stop_boxed_916_; lean_object* v_res_917_; 
v_i_boxed_915_ = lean_unbox_usize(v_i_911_);
lean_dec(v_i_911_);
v_stop_boxed_916_ = lean_unbox_usize(v_stop_912_);
lean_dec(v_stop_912_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_909_, v_as_910_, v_i_boxed_915_, v_stop_boxed_916_, v_b_913_);
lean_dec_ref(v_as_910_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(lean_object* v_f_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v_cs_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_935_; 
v_cs_921_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_935_ == 0)
{
v___x_923_ = v_x_919_;
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_cs_921_);
lean_dec(v_x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_array_get_size(v_cs_921_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_nat_dec_lt(v___x_925_, v___x_926_);
if (v___x_928_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v_cs_921_);
lean_dec_ref(v_f_918_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_930_ = v___x_923_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_927_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; 
lean_del_object(v___x_923_);
v___x_932_ = ((size_t)0ULL);
v___x_933_ = lean_usize_of_nat(v___x_926_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_918_, v_cs_921_, v___x_932_, v___x_933_, v___x_927_);
lean_dec_ref(v_cs_921_);
return v___x_934_;
}
}
}
else
{
lean_object* v_vs_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_950_; 
v_vs_936_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_950_ == 0)
{
v___x_938_ = v_x_919_;
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_vs_936_);
lean_dec(v_x_919_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_array_get_size(v_vs_936_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_943_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v_vs_936_);
lean_dec_ref(v_f_918_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 0);
lean_ctor_set(v___x_938_, 0, v___x_942_);
v___x_945_ = v___x_938_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_942_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_938_);
v___x_947_ = ((size_t)0ULL);
v___x_948_ = lean_usize_of_nat(v___x_941_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_918_, v_vs_936_, v___x_947_, v___x_948_, v___x_942_);
lean_dec_ref(v_vs_936_);
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(lean_object* v_f_951_, lean_object* v_as_952_, size_t v_i_953_, size_t v_stop_954_, lean_object* v_b_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_eq(v_i_953_, v_stop_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_array_uget_borrowed(v_as_952_, v_i_953_);
lean_inc(v___x_958_);
lean_inc_ref(v_f_951_);
v___x_959_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_951_, v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; size_t v___x_961_; size_t v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_953_, v___x_961_);
v_i_953_ = v___x_962_;
v_b_955_ = v_a_960_;
goto _start;
}
else
{
lean_dec_ref(v_f_951_);
return v___x_959_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_f_951_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_b_955_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_f_965_, lean_object* v_as_966_, lean_object* v_i_967_, lean_object* v_stop_968_, lean_object* v_b_969_, lean_object* v___y_970_){
_start:
{
size_t v_i_boxed_971_; size_t v_stop_boxed_972_; lean_object* v_res_973_; 
v_i_boxed_971_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_stop_boxed_972_ = lean_unbox_usize(v_stop_968_);
lean_dec(v_stop_968_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_965_, v_as_966_, v_i_boxed_971_, v_stop_boxed_972_, v_b_969_);
lean_dec_ref(v_as_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_f_974_, lean_object* v_x_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_974_, v_x_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(lean_object* v_f_978_, lean_object* v_t_979_){
_start:
{
lean_object* v_root_981_; lean_object* v_tail_982_; lean_object* v___x_983_; 
v_root_981_ = lean_ctor_get(v_t_979_, 0);
lean_inc_ref(v_root_981_);
v_tail_982_ = lean_ctor_get(v_t_979_, 1);
lean_inc_ref(v_tail_982_);
lean_dec_ref(v_t_979_);
lean_inc_ref(v_f_978_);
v___x_983_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_978_, v_root_981_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_997_; 
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_998_);
v___x_985_ = v___x_983_;
v_isShared_986_ = v_isSharedCheck_997_;
goto v_resetjp_984_;
}
else
{
lean_dec(v___x_983_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_997_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_array_get_size(v_tail_982_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
if (v___x_990_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v_tail_982_);
lean_dec_ref(v_f_978_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_989_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_989_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_985_);
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_988_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_978_, v_tail_982_, v___x_994_, v___x_995_, v___x_989_);
lean_dec_ref(v_tail_982_);
return v___x_996_;
}
}
}
else
{
lean_dec_ref(v_tail_982_);
lean_dec_ref(v_f_978_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(lean_object* v_f_999_, lean_object* v_t_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_999_, v_t_1000_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(lean_object* v_f_1004_, lean_object* v_x_1005_, size_t v_x_1006_, size_t v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_cs_1009_; lean_object* v___x_1010_; size_t v___x_1011_; lean_object* v_j_1012_; lean_object* v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v_cs_1009_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_cs_1009_);
lean_dec_ref_known(v_x_1005_, 1);
v___x_1010_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
v___x_1011_ = lean_usize_shift_right(v_x_1006_, v_x_1007_);
v_j_1012_ = lean_usize_to_nat(v___x_1011_);
v___x_1013_ = lean_array_get_borrowed(v___x_1010_, v_cs_1009_, v_j_1012_);
v___x_1014_ = ((size_t)1ULL);
v___x_1015_ = lean_usize_shift_left(v___x_1014_, v_x_1007_);
v___x_1016_ = lean_usize_sub(v___x_1015_, v___x_1014_);
v___x_1017_ = lean_usize_land(v_x_1006_, v___x_1016_);
v___x_1018_ = ((size_t)5ULL);
v___x_1019_ = lean_usize_sub(v_x_1007_, v___x_1018_);
lean_inc(v___x_1013_);
lean_inc_ref(v_f_1004_);
v___x_1020_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1004_, v___x_1013_, v___x_1017_, v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1035_; 
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1020_, 0);
lean_dec(v_unused_1036_);
v___x_1022_ = v___x_1020_;
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v___x_1020_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_add(v_j_1012_, v___x_1024_);
lean_dec(v_j_1012_);
v___x_1026_ = lean_array_get_size(v_cs_1009_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1030_; 
lean_dec(v___x_1025_);
lean_dec_ref(v_cs_1009_);
lean_dec_ref(v_f_1004_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1027_);
v___x_1030_ = v___x_1022_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1027_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
lean_del_object(v___x_1022_);
v___x_1032_ = lean_usize_of_nat(v___x_1025_);
lean_dec(v___x_1025_);
v___x_1033_ = lean_usize_of_nat(v___x_1026_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_1004_, v_cs_1009_, v___x_1032_, v___x_1033_, v___x_1027_);
lean_dec_ref(v_cs_1009_);
return v___x_1034_;
}
}
}
else
{
lean_dec(v_j_1012_);
lean_dec_ref(v_cs_1009_);
lean_dec_ref(v_f_1004_);
return v___x_1020_;
}
}
else
{
lean_object* v_vs_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1051_; 
v_vs_1037_ = lean_ctor_get(v_x_1005_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1039_ = v_x_1005_;
v_isShared_1040_ = v_isSharedCheck_1051_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_vs_1037_);
lean_dec(v_x_1005_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1051_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1041_ = lean_usize_to_nat(v_x_1006_);
v___x_1042_ = lean_array_get_size(v_vs_1037_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v___x_1041_);
lean_dec_ref(v_vs_1037_);
lean_dec_ref(v_f_1004_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1043_);
v___x_1046_ = v___x_1039_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
lean_del_object(v___x_1039_);
v___x_1048_ = lean_usize_of_nat(v___x_1041_);
lean_dec(v___x_1041_);
v___x_1049_ = lean_usize_of_nat(v___x_1042_);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1004_, v_vs_1037_, v___x_1048_, v___x_1049_, v___x_1043_);
lean_dec_ref(v_vs_1037_);
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(lean_object* v_f_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_x_1369__boxed_1057_; size_t v_x_1370__boxed_1058_; lean_object* v_res_1059_; 
v_x_1369__boxed_1057_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_x_1370__boxed_1058_ = lean_unbox_usize(v_x_1055_);
lean_dec(v_x_1055_);
v_res_1059_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1052_, v_x_1053_, v_x_1369__boxed_1057_, v_x_1370__boxed_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(lean_object* v_f_1060_, lean_object* v_t_1061_, lean_object* v_start_1062_){
_start:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_nat_dec_eq(v_start_1062_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v_root_1066_; lean_object* v_tail_1067_; size_t v_shift_1068_; lean_object* v_tailOff_1069_; uint8_t v___x_1070_; 
v_root_1066_ = lean_ctor_get(v_t_1061_, 0);
lean_inc_ref(v_root_1066_);
v_tail_1067_ = lean_ctor_get(v_t_1061_, 1);
lean_inc_ref(v_tail_1067_);
v_shift_1068_ = lean_ctor_get_usize(v_t_1061_, 4);
v_tailOff_1069_ = lean_ctor_get(v_t_1061_, 3);
lean_inc(v_tailOff_1069_);
lean_dec_ref(v_t_1061_);
v___x_1070_ = lean_nat_dec_le(v_tailOff_1069_, v_start_1062_);
if (v___x_1070_ == 0)
{
size_t v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v_tailOff_1069_);
v___x_1071_ = lean_usize_of_nat(v_start_1062_);
lean_inc_ref(v_f_1060_);
v___x_1072_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_1060_, v_root_1066_, v___x_1071_, v_shift_1068_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1085_; 
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_1072_, 0);
lean_dec(v_unused_1086_);
v___x_1074_ = v___x_1072_;
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___x_1072_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_array_get_size(v_tail_1067_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_nat_dec_lt(v___x_1064_, v___x_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1080_; 
lean_dec_ref(v_tail_1067_);
lean_dec_ref(v_f_1060_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1077_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
lean_del_object(v___x_1074_);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = lean_usize_of_nat(v___x_1076_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1060_, v_tail_1067_, v___x_1082_, v___x_1083_, v___x_1077_);
lean_dec_ref(v_tail_1067_);
return v___x_1084_;
}
}
}
else
{
lean_dec_ref(v_tail_1067_);
lean_dec_ref(v_f_1060_);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
lean_dec_ref(v_root_1066_);
v___x_1087_ = lean_nat_sub(v_start_1062_, v_tailOff_1069_);
lean_dec(v_tailOff_1069_);
v___x_1088_ = lean_array_get_size(v_tail_1067_);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_nat_dec_lt(v___x_1087_, v___x_1088_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec(v___x_1087_);
lean_dec_ref(v_tail_1067_);
lean_dec_ref(v_f_1060_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
return v___x_1091_;
}
else
{
size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_usize_of_nat(v___x_1087_);
lean_dec(v___x_1087_);
v___x_1093_ = lean_usize_of_nat(v___x_1088_);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_1060_, v_tail_1067_, v___x_1092_, v___x_1093_, v___x_1089_);
lean_dec_ref(v_tail_1067_);
return v___x_1094_;
}
}
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_1060_, v_t_1061_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(lean_object* v_f_1096_, lean_object* v_t_1097_, lean_object* v_start_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1096_, v_t_1097_, v_start_1098_);
lean_dec(v_start_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(lean_object* v_log_1101_, lean_object* v_f_1102_){
_start:
{
lean_object* v_unreported_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_unreported_1104_ = lean_ctor_get(v_log_1101_, 1);
lean_inc_ref(v_unreported_1104_);
lean_dec_ref(v_log_1101_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_1102_, v_unreported_1104_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(lean_object* v_log_1107_, lean_object* v_f_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_1107_, v_f_1108_);
return v_res_1110_;
}
}
static lean_object* _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0));
v___x_1113_ = lean_mk_io_user_error(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(lean_object* v_env_1114_, lean_object* v_inputCtx_1115_, lean_object* v_state_1116_, lean_object* v_msgs_1117_, lean_object* v_stxs_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_snd_1125_; lean_object* v_fst_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; uint8_t v___y_1130_; uint8_t v___x_1151_; 
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
v___x_1151_ = l_Lean_Parser_isTerminalCommand(v_fst_1126_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_array_push(v_stxs_1118_, v_fst_1126_);
v_state_1116_ = v_fst_1127_;
v_msgs_1117_ = v_snd_1128_;
v_stxs_1118_ = v___x_1152_;
goto _start;
}
else
{
uint8_t v___x_1154_; 
lean_dec(v_fst_1127_);
lean_dec_ref(v_inputCtx_1115_);
lean_dec_ref(v_env_1114_);
v___x_1154_ = l_Lean_MessageLog_hasUnreported(v_snd_1128_);
if (v___x_1154_ == 0)
{
if (v___x_1151_ == 0)
{
lean_dec(v_fst_1126_);
lean_dec_ref(v_stxs_1118_);
v___y_1130_ = v___x_1151_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_snd_1128_);
v___x_1155_ = lean_array_push(v_stxs_1118_, v_fst_1126_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
else
{
uint8_t v___x_1157_; 
lean_dec(v_fst_1126_);
lean_dec_ref(v_stxs_1118_);
v___x_1157_ = 0;
v___y_1130_ = v___x_1157_;
goto v___jp_1129_;
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_box(v___y_1130_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1132_, 0, v___x_1131_);
v___x_1133_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_1128_, v___f_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1133_, 0);
lean_dec(v_unused_1142_);
v___x_1135_ = v___x_1133_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v___x_1133_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_obj_once(&l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1, &l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once, _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1133_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1133_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(lean_object* v_env_1158_, lean_object* v_inputCtx_1159_, lean_object* v_state_1160_, lean_object* v_msgs_1161_, lean_object* v_stxs_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1158_, v_inputCtx_1159_, v_state_1160_, v_msgs_1161_, v_stxs_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* v_env_1165_, lean_object* v_inputCtx_1166_, lean_object* v_s_1167_, lean_object* v_msgs_1168_, lean_object* v_stxs_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1165_, v_inputCtx_1166_, v_s_1167_, v_msgs_1168_, v_stxs_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux___boxed(lean_object* v_env_1172_, lean_object* v_inputCtx_1173_, lean_object* v_s_1174_, lean_object* v_msgs_1175_, lean_object* v_stxs_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Parser_testParseModuleAux(v_env_1172_, v_inputCtx_1173_, v_s_1174_, v_msgs_1175_, v_stxs_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* v_env_1187_, lean_object* v_fname_1188_, lean_object* v_contents_1189_){
_start:
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v_inputCtx_1193_; lean_object* v___x_1194_; 
v___x_1191_ = 1;
v___x_1192_ = lean_string_utf8_byte_size(v_contents_1189_);
v_inputCtx_1193_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1189_, v_fname_1188_, v___x_1191_, v___x_1192_);
lean_inc_ref(v_inputCtx_1193_);
v___x_1194_ = l_Lean_Parser_parseHeader(v_inputCtx_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_snd_1196_; lean_object* v_fst_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_snd_1196_ = lean_ctor_get(v_a_1195_, 1);
lean_inc(v_snd_1196_);
v_fst_1197_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_fst_1197_);
lean_dec(v_a_1195_);
v_fst_1198_ = lean_ctor_get(v_snd_1196_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v_snd_1196_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_snd_1196_);
v___x_1200_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__0));
v___x_1201_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(v_env_1187_, v_inputCtx_1193_, v_fst_1198_, v_snd_1199_, v___x_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1217_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1217_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1217_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1206_ = ((lean_object*)(l_Lean_Parser_testParseModule___closed__2));
v___x_1207_ = l_Lean_mkListNode(v_a_1202_);
v___x_1208_ = lean_unsigned_to_nat(2u);
v___x_1209_ = lean_mk_empty_array_with_capacity(v___x_1208_);
v___x_1210_ = lean_array_push(v___x_1209_, v_fst_1197_);
v___x_1211_ = lean_array_push(v___x_1210_, v___x_1207_);
v___x_1212_ = lean_box(2);
v___x_1213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1206_);
lean_ctor_set(v___x_1213_, 2, v___x_1211_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1213_);
v___x_1215_ = v___x_1204_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_fst_1197_);
v_a_1218_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1201_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1201_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_inputCtx_1193_);
lean_dec_ref(v_env_1187_);
v_a_1226_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1194_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1194_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule___boxed(lean_object* v_env_1234_, lean_object* v_fname_1235_, lean_object* v_contents_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Parser_testParseModule(v_env_1234_, v_fname_1235_, v_contents_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* v_env_1239_, lean_object* v_fname_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_IO_FS_readFile(v_fname_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Parser_testParseModule(v_env_1239_, v_fname_1240_, v_a_1243_);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_fname_1240_);
lean_dec_ref(v_env_1239_);
v_a_1245_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1242_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1242_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile___boxed(lean_object* v_env_1253_, lean_object* v_fname_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Parser_testParseFile(v_env_1253_, v_fname_1254_);
return v_res_1256_;
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
