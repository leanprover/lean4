// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: public import Lean.Parser.Module
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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_String_toFileMap(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static const lean_array_object l_Lean_ParseImports_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParseImports_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_ParseImports_instInhabitedState_default___closed__0_value;
static const lean_ctor_object l_Lean_ParseImports_instInhabitedState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParseImports_instInhabitedState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_ParseImports_instInhabitedState_default___closed__1 = (const lean_object*)&l_Lean_ParseImports_instInhabitedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_ParseImports_instInhabitedState_default = (const lean_object*)&l_Lean_ParseImports_instInhabitedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_ParseImports_instInhabitedState = (const lean_object*)&l_Lean_ParseImports_instInhabitedState_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ParseImports_instInhabitedParser_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParseImports_skip___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_ParseImports_instInhabitedParser = (const lean_object*)&l_Lean_ParseImports_instInhabitedParser_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_State_mkEOIError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected end of input"};
static const lean_object* l_Lean_ParseImports_State_mkEOIError___closed__0 = (const lean_object*)&l_Lean_ParseImports_State_mkEOIError___closed__0_value;
static const lean_ctor_object l_Lean_ParseImports_State_mkEOIError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParseImports_State_mkEOIError___closed__0_value)}};
static const lean_object* l_Lean_ParseImports_State_mkEOIError___closed__1 = (const lean_object*)&l_Lean_ParseImports_State_mkEOIError___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_clearError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unterminated comment"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ParseImports_instAndThenParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParseImports_instAndThenParser___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParseImports_instAndThenParser___closed__0 = (const lean_object*)&l_Lean_ParseImports_instAndThenParser___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ParseImports_instAndThenParser = (const lean_object*)&l_Lean_ParseImports_instAndThenParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_whitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "tabs are not allowed; please configure your editor to expand them"};
static const lean_object* l_Lean_ParseImports_whitespace___closed__0 = (const lean_object*)&l_Lean_ParseImports_whitespace___closed__0_value;
static const lean_ctor_object l_Lean_ParseImports_whitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParseImports_whitespace___closed__0_value)}};
static const lean_object* l_Lean_ParseImports_whitespace___closed__1 = (const lean_object*)&l_Lean_ParseImports_whitespace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_keyword___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_ParseImports_keyword___lam__0___closed__0 = (const lean_object*)&l_Lean_ParseImports_keyword___lam__0___closed__0_value;
static const lean_string_object l_Lean_ParseImports_keyword___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` expected"};
static const lean_object* l_Lean_ParseImports_keyword___lam__0___closed__1 = (const lean_object*)&l_Lean_ParseImports_keyword___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected identifier"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unterminated identifier escape"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ParseImports_moduleIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParseImports_moduleIdent___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParseImports_moduleIdent___closed__0 = (const lean_object*)&l_Lean_ParseImports_moduleIdent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_manyImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "cannot use 'public', 'meta', or 'all' without 'module'"};
static const lean_object* l_Lean_ParseImports_manyImports___closed__0 = (const lean_object*)&l_Lean_ParseImports_manyImports___closed__0_value;
static const lean_ctor_object l_Lean_ParseImports_manyImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParseImports_manyImports___closed__0_value)}};
static const lean_object* l_Lean_ParseImports_manyImports___closed__1 = (const lean_object*)&l_Lean_ParseImports_manyImports___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`import` expected"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_ParseImports_main___closed__0 = (const lean_object*)&l_Lean_ParseImports_main___closed__0_value;
static const lean_string_object l_Lean_ParseImports_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_ParseImports_main___closed__1 = (const lean_object*)&l_Lean_ParseImports_main___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object*, lean_object*);
static const lean_string_object l_Lean_parseImports_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_parseImports_x27___closed__0 = (const lean_object*)&l_Lean_parseImports_x27___closed__0_value;
static const lean_string_object l_Lean_parseImports_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_parseImports_x27___closed__1 = (const lean_object*)&l_Lean_parseImports_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object*);
static const lean_string_object l_Lean_instToJsonPrintImportResult_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__0_value;
static const lean_string_object l_Lean_instToJsonPrintImportResult_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "errors"};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__1 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__1_value;
static const lean_array_object l_Lean_instToJsonPrintImportResult_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__2 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPrintImportResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPrintImportResult_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPrintImportResult___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPrintImportResult = (const lean_object*)&l_Lean_instToJsonPrintImportResult___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l_Lean_instToJsonPrintImportsResult_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPrintImportsResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPrintImportsResult_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPrintImportsResult___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportsResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPrintImportsResult = (const lean_object*)&l_Lean_instToJsonPrintImportsResult___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg(lean_object* v_s_10_){
_start:
{
lean_inc_ref(v_s_10_);
return v_s_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg___boxed(lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ParseImports_skip___redArg(v_s_11_);
lean_dec_ref(v_s_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip(lean_object* v_x_13_, lean_object* v_s_14_){
_start:
{
lean_inc_ref(v_s_14_);
return v_s_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___boxed(lean_object* v_x_15_, lean_object* v_s_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_ParseImports_skip(v_x_15_, v_s_16_);
lean_dec_ref(v_s_16_);
lean_dec_ref(v_x_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object* v_s_19_, lean_object* v_pos_20_){
_start:
{
lean_object* v_imports_21_; uint8_t v_badModifier_22_; lean_object* v_error_x3f_23_; uint8_t v_isModule_24_; uint8_t v_isMeta_25_; uint8_t v_isExported_26_; uint8_t v_importAll_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
v_imports_21_ = lean_ctor_get(v_s_19_, 0);
v_badModifier_22_ = lean_ctor_get_uint8(v_s_19_, sizeof(void*)*3);
v_error_x3f_23_ = lean_ctor_get(v_s_19_, 2);
v_isModule_24_ = lean_ctor_get_uint8(v_s_19_, sizeof(void*)*3 + 1);
v_isMeta_25_ = lean_ctor_get_uint8(v_s_19_, sizeof(void*)*3 + 2);
v_isExported_26_ = lean_ctor_get_uint8(v_s_19_, sizeof(void*)*3 + 3);
v_importAll_27_ = lean_ctor_get_uint8(v_s_19_, sizeof(void*)*3 + 4);
v_isSharedCheck_34_ = !lean_is_exclusive(v_s_19_);
if (v_isSharedCheck_34_ == 0)
{
lean_object* v_unused_35_; 
v_unused_35_ = lean_ctor_get(v_s_19_, 1);
lean_dec(v_unused_35_);
v___x_29_ = v_s_19_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_error_x3f_23_);
lean_inc(v_imports_21_);
lean_dec(v_s_19_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v_pos_20_);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_imports_21_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_pos_20_);
lean_ctor_set(v_reuseFailAlloc_33_, 2, v_error_x3f_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*3, v_badModifier_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*3 + 1, v_isModule_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*3 + 2, v_isMeta_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*3 + 3, v_isExported_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*3 + 4, v_importAll_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object* v_s_36_, lean_object* v_msg_37_){
_start:
{
lean_object* v_imports_38_; lean_object* v_pos_39_; uint8_t v_badModifier_40_; uint8_t v_isModule_41_; uint8_t v_isMeta_42_; uint8_t v_isExported_43_; uint8_t v_importAll_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_imports_38_ = lean_ctor_get(v_s_36_, 0);
v_pos_39_ = lean_ctor_get(v_s_36_, 1);
v_badModifier_40_ = lean_ctor_get_uint8(v_s_36_, sizeof(void*)*3);
v_isModule_41_ = lean_ctor_get_uint8(v_s_36_, sizeof(void*)*3 + 1);
v_isMeta_42_ = lean_ctor_get_uint8(v_s_36_, sizeof(void*)*3 + 2);
v_isExported_43_ = lean_ctor_get_uint8(v_s_36_, sizeof(void*)*3 + 3);
v_importAll_44_ = lean_ctor_get_uint8(v_s_36_, sizeof(void*)*3 + 4);
v_isSharedCheck_52_ = !lean_is_exclusive(v_s_36_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v_s_36_, 2);
lean_dec(v_unused_53_);
v___x_46_ = v_s_36_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_pos_39_);
lean_inc(v_imports_38_);
lean_dec(v_s_36_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v_msg_37_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 2, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_imports_38_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_pos_39_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v___x_48_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*3, v_badModifier_40_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*3 + 1, v_isModule_41_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*3 + 2, v_isMeta_42_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*3 + 3, v_isExported_43_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*3 + 4, v_importAll_44_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object* v_s_57_){
_start:
{
lean_object* v_imports_58_; lean_object* v_pos_59_; uint8_t v_badModifier_60_; uint8_t v_isModule_61_; uint8_t v_isMeta_62_; uint8_t v_isExported_63_; uint8_t v_importAll_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_72_; 
v_imports_58_ = lean_ctor_get(v_s_57_, 0);
v_pos_59_ = lean_ctor_get(v_s_57_, 1);
v_badModifier_60_ = lean_ctor_get_uint8(v_s_57_, sizeof(void*)*3);
v_isModule_61_ = lean_ctor_get_uint8(v_s_57_, sizeof(void*)*3 + 1);
v_isMeta_62_ = lean_ctor_get_uint8(v_s_57_, sizeof(void*)*3 + 2);
v_isExported_63_ = lean_ctor_get_uint8(v_s_57_, sizeof(void*)*3 + 3);
v_importAll_64_ = lean_ctor_get_uint8(v_s_57_, sizeof(void*)*3 + 4);
v_isSharedCheck_72_ = !lean_is_exclusive(v_s_57_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v_s_57_, 2);
lean_dec(v_unused_73_);
v___x_66_ = v_s_57_;
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_pos_59_);
lean_inc(v_imports_58_);
lean_dec(v_s_57_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_72_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = ((lean_object*)(l_Lean_ParseImports_State_mkEOIError___closed__1));
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 2, v___x_68_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_imports_58_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_pos_59_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v___x_68_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*3, v_badModifier_60_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*3 + 1, v_isModule_61_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*3 + 2, v_isMeta_62_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*3 + 3, v_isExported_63_);
lean_ctor_set_uint8(v_reuseFailAlloc_71_, sizeof(void*)*3 + 4, v_importAll_64_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_clearError(lean_object* v_s_74_){
_start:
{
lean_object* v_imports_75_; lean_object* v_pos_76_; uint8_t v_isModule_77_; uint8_t v_isMeta_78_; uint8_t v_isExported_79_; uint8_t v_importAll_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v_imports_75_ = lean_ctor_get(v_s_74_, 0);
v_pos_76_ = lean_ctor_get(v_s_74_, 1);
v_isModule_77_ = lean_ctor_get_uint8(v_s_74_, sizeof(void*)*3 + 1);
v_isMeta_78_ = lean_ctor_get_uint8(v_s_74_, sizeof(void*)*3 + 2);
v_isExported_79_ = lean_ctor_get_uint8(v_s_74_, sizeof(void*)*3 + 3);
v_importAll_80_ = lean_ctor_get_uint8(v_s_74_, sizeof(void*)*3 + 4);
v_isSharedCheck_89_ = !lean_is_exclusive(v_s_74_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_s_74_, 2);
lean_dec(v_unused_90_);
v___x_82_ = v_s_74_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_pos_76_);
lean_inc(v_imports_75_);
lean_dec(v_s_74_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = 0;
v___x_85_ = lean_box(0);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 2, v___x_85_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_imports_75_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_pos_76_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v___x_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*3 + 1, v_isModule_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*3 + 2, v_isMeta_78_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*3 + 3, v_isExported_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*3 + 4, v_importAll_80_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*3, v___x_84_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object* v_s_91_, lean_object* v_input_92_, lean_object* v_pos_93_){
_start:
{
lean_object* v_imports_94_; uint8_t v_badModifier_95_; lean_object* v_error_x3f_96_; uint8_t v_isModule_97_; uint8_t v_isMeta_98_; uint8_t v_isExported_99_; uint8_t v_importAll_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v_imports_94_ = lean_ctor_get(v_s_91_, 0);
v_badModifier_95_ = lean_ctor_get_uint8(v_s_91_, sizeof(void*)*3);
v_error_x3f_96_ = lean_ctor_get(v_s_91_, 2);
v_isModule_97_ = lean_ctor_get_uint8(v_s_91_, sizeof(void*)*3 + 1);
v_isMeta_98_ = lean_ctor_get_uint8(v_s_91_, sizeof(void*)*3 + 2);
v_isExported_99_ = lean_ctor_get_uint8(v_s_91_, sizeof(void*)*3 + 3);
v_importAll_100_ = lean_ctor_get_uint8(v_s_91_, sizeof(void*)*3 + 4);
v_isSharedCheck_108_ = !lean_is_exclusive(v_s_91_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_s_91_, 1);
lean_dec(v_unused_109_);
v___x_102_ = v_s_91_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_error_x3f_96_);
lean_inc(v_imports_94_);
lean_dec(v_s_91_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_string_utf8_next(v_input_92_, v_pos_93_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_imports_94_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_error_x3f_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*3, v_badModifier_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*3 + 1, v_isModule_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*3 + 2, v_isMeta_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*3 + 3, v_isExported_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*3 + 4, v_importAll_100_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object* v_s_110_, lean_object* v_input_111_, lean_object* v_pos_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_ParseImports_State_next(v_s_110_, v_input_111_, v_pos_112_);
lean_dec(v_pos_112_);
lean_dec_ref(v_input_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object* v_s_114_, lean_object* v_input_115_, lean_object* v_pos_116_){
_start:
{
lean_object* v_imports_117_; uint8_t v_badModifier_118_; lean_object* v_error_x3f_119_; uint8_t v_isModule_120_; uint8_t v_isMeta_121_; uint8_t v_isExported_122_; uint8_t v_importAll_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_imports_117_ = lean_ctor_get(v_s_114_, 0);
v_badModifier_118_ = lean_ctor_get_uint8(v_s_114_, sizeof(void*)*3);
v_error_x3f_119_ = lean_ctor_get(v_s_114_, 2);
v_isModule_120_ = lean_ctor_get_uint8(v_s_114_, sizeof(void*)*3 + 1);
v_isMeta_121_ = lean_ctor_get_uint8(v_s_114_, sizeof(void*)*3 + 2);
v_isExported_122_ = lean_ctor_get_uint8(v_s_114_, sizeof(void*)*3 + 3);
v_importAll_123_ = lean_ctor_get_uint8(v_s_114_, sizeof(void*)*3 + 4);
v_isSharedCheck_131_ = !lean_is_exclusive(v_s_114_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v_s_114_, 1);
lean_dec(v_unused_132_);
v___x_125_ = v_s_114_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_error_x3f_119_);
lean_inc(v_imports_117_);
lean_dec(v_s_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_string_utf8_next_fast(v_input_115_, v_pos_116_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_imports_117_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_error_x3f_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*3, v_badModifier_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*3 + 1, v_isModule_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*3 + 2, v_isMeta_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*3 + 3, v_isExported_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*3 + 4, v_importAll_123_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object* v_s_133_, lean_object* v_input_134_, lean_object* v_pos_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_ParseImports_State_next_x27___redArg(v_s_133_, v_input_134_, v_pos_135_);
lean_dec(v_pos_135_);
lean_dec_ref(v_input_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object* v_s_137_, lean_object* v_input_138_, lean_object* v_pos_139_, lean_object* v_h_140_){
_start:
{
lean_object* v_imports_141_; uint8_t v_badModifier_142_; lean_object* v_error_x3f_143_; uint8_t v_isModule_144_; uint8_t v_isMeta_145_; uint8_t v_isExported_146_; uint8_t v_importAll_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_imports_141_ = lean_ctor_get(v_s_137_, 0);
v_badModifier_142_ = lean_ctor_get_uint8(v_s_137_, sizeof(void*)*3);
v_error_x3f_143_ = lean_ctor_get(v_s_137_, 2);
v_isModule_144_ = lean_ctor_get_uint8(v_s_137_, sizeof(void*)*3 + 1);
v_isMeta_145_ = lean_ctor_get_uint8(v_s_137_, sizeof(void*)*3 + 2);
v_isExported_146_ = lean_ctor_get_uint8(v_s_137_, sizeof(void*)*3 + 3);
v_importAll_147_ = lean_ctor_get_uint8(v_s_137_, sizeof(void*)*3 + 4);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_137_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_s_137_, 1);
lean_dec(v_unused_156_);
v___x_149_ = v_s_137_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_error_x3f_143_);
lean_inc(v_imports_141_);
lean_dec(v_s_137_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_string_utf8_next_fast(v_input_138_, v_pos_139_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_imports_141_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_error_x3f_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_154_, sizeof(void*)*3, v_badModifier_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_154_, sizeof(void*)*3 + 1, v_isModule_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_154_, sizeof(void*)*3 + 2, v_isMeta_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_154_, sizeof(void*)*3 + 3, v_isExported_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_154_, sizeof(void*)*3 + 4, v_importAll_147_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object* v_s_157_, lean_object* v_input_158_, lean_object* v_pos_159_, lean_object* v_h_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_ParseImports_State_next_x27(v_s_157_, v_input_158_, v_pos_159_, v_h_160_);
lean_dec(v_pos_159_);
lean_dec_ref(v_input_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(lean_object* v_s_165_){
_start:
{
lean_object* v_imports_166_; lean_object* v_pos_167_; uint8_t v_badModifier_168_; uint8_t v_isModule_169_; uint8_t v_isMeta_170_; uint8_t v_isExported_171_; uint8_t v_importAll_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_180_; 
v_imports_166_ = lean_ctor_get(v_s_165_, 0);
v_pos_167_ = lean_ctor_get(v_s_165_, 1);
v_badModifier_168_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*3);
v_isModule_169_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*3 + 1);
v_isMeta_170_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*3 + 2);
v_isExported_171_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*3 + 3);
v_importAll_172_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*3 + 4);
v_isSharedCheck_180_ = !lean_is_exclusive(v_s_165_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v_s_165_, 2);
lean_dec(v_unused_181_);
v___x_174_ = v_s_165_;
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_pos_167_);
lean_inc(v_imports_166_);
lean_dec(v_s_165_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_180_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1));
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 2, v___x_176_);
v___x_178_ = v___x_174_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_imports_166_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_pos_167_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v___x_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*3, v_badModifier_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*3 + 1, v_isModule_169_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*3 + 2, v_isMeta_170_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*3 + 3, v_isExported_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*3 + 4, v_importAll_172_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object* v_nesting_182_, lean_object* v_input_183_, lean_object* v_s_184_){
_start:
{
lean_object* v_imports_185_; lean_object* v_pos_186_; uint8_t v_badModifier_187_; lean_object* v_error_x3f_188_; uint8_t v_isModule_189_; uint8_t v_isMeta_190_; uint8_t v_isExported_191_; uint8_t v_importAll_192_; uint8_t v___x_193_; 
v_imports_185_ = lean_ctor_get(v_s_184_, 0);
v_pos_186_ = lean_ctor_get(v_s_184_, 1);
v_badModifier_187_ = lean_ctor_get_uint8(v_s_184_, sizeof(void*)*3);
v_error_x3f_188_ = lean_ctor_get(v_s_184_, 2);
v_isModule_189_ = lean_ctor_get_uint8(v_s_184_, sizeof(void*)*3 + 1);
v_isMeta_190_ = lean_ctor_get_uint8(v_s_184_, sizeof(void*)*3 + 2);
v_isExported_191_ = lean_ctor_get_uint8(v_s_184_, sizeof(void*)*3 + 3);
v_importAll_192_ = lean_ctor_get_uint8(v_s_184_, sizeof(void*)*3 + 4);
v___x_193_ = lean_string_utf8_at_end(v_input_183_, v_pos_186_);
if (v___x_193_ == 0)
{
uint32_t v_curr_194_; lean_object* v_i_195_; uint32_t v___x_196_; uint8_t v___x_197_; 
v_curr_194_ = lean_string_utf8_get_fast(v_input_183_, v_pos_186_);
v_i_195_ = lean_string_utf8_next_fast(v_input_183_, v_pos_186_);
v___x_196_ = 45;
v___x_197_ = lean_uint32_dec_eq(v_curr_194_, v___x_196_);
if (v___x_197_ == 0)
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 47;
v___x_199_ = lean_uint32_dec_eq(v_curr_194_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
lean_inc(v_error_x3f_188_);
lean_inc_ref(v_imports_185_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_s_184_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_208_ = lean_ctor_get(v_s_184_, 2);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_s_184_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_s_184_, 0);
lean_dec(v_unused_210_);
v___x_201_ = v_s_184_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_s_184_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 1, v_i_195_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_i_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
v_s_184_ = v___x_204_;
goto _start;
}
}
}
else
{
uint8_t v___x_211_; 
v___x_211_ = lean_string_utf8_at_end(v_input_183_, v_i_195_);
if (v___x_211_ == 0)
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_228_; 
lean_inc(v_error_x3f_188_);
lean_inc_ref(v_imports_185_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_s_184_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_229_ = lean_ctor_get(v_s_184_, 2);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_s_184_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_s_184_, 0);
lean_dec(v_unused_231_);
v___x_213_ = v_s_184_;
v_isShared_214_ = v_isSharedCheck_228_;
goto v_resetjp_212_;
}
else
{
lean_dec(v_s_184_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_228_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint32_t v_curr_215_; uint8_t v___x_216_; 
v_curr_215_ = lean_string_utf8_get_fast(v_input_183_, v_i_195_);
v___x_216_ = lean_uint32_dec_eq(v_curr_215_, v___x_196_);
if (v___x_216_ == 0)
{
lean_object* v___x_218_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_i_195_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_i_195_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
v_s_184_ = v___x_218_;
goto _start;
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_nesting_182_, v___x_221_);
lean_dec(v_nesting_182_);
v___x_223_ = lean_string_utf8_next_fast(v_input_183_, v_i_195_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_223_);
v___x_225_ = v___x_213_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
v_nesting_182_ = v___x_222_;
v_s_184_ = v___x_225_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_232_; 
lean_dec(v_nesting_182_);
v___x_232_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_184_);
return v___x_232_;
}
}
}
else
{
uint8_t v___x_233_; 
v___x_233_ = lean_string_utf8_at_end(v_input_183_, v_i_195_);
if (v___x_233_ == 0)
{
lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_256_; 
lean_inc(v_error_x3f_188_);
lean_inc_ref(v_imports_185_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_s_184_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_257_ = lean_ctor_get(v_s_184_, 2);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_s_184_, 1);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_s_184_, 0);
lean_dec(v_unused_259_);
v___x_235_ = v_s_184_;
v_isShared_236_ = v_isSharedCheck_256_;
goto v_resetjp_234_;
}
else
{
lean_dec(v_s_184_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_256_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint32_t v_curr_237_; uint32_t v___x_238_; uint8_t v___x_239_; 
v_curr_237_ = lean_string_utf8_get_fast(v_input_183_, v_i_195_);
v___x_238_ = 47;
v___x_239_ = lean_uint32_dec_eq(v_curr_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_241_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_i_195_);
v___x_241_ = v___x_235_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_i_195_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_s_184_ = v___x_241_;
goto _start;
}
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_dec_eq(v_nesting_182_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_246_ = lean_nat_sub(v_nesting_182_, v___x_244_);
lean_dec(v_nesting_182_);
v___x_247_ = lean_string_utf8_next_fast(v_input_183_, v_i_195_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_247_);
v___x_249_ = v___x_235_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
v_nesting_182_ = v___x_246_;
v_s_184_ = v___x_249_;
goto _start;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec(v_nesting_182_);
v___x_252_ = lean_string_utf8_next(v_input_183_, v_i_195_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_252_);
v___x_254_ = v___x_235_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_imports_185_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_error_x3f_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*3, v_badModifier_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*3 + 1, v_isModule_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*3 + 2, v_isMeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*3 + 3, v_isExported_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*3 + 4, v_importAll_192_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec(v_nesting_182_);
v___x_260_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_184_);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v_nesting_182_);
v___x_261_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_184_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object* v_nesting_262_, lean_object* v_input_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_ParseImports_finishCommentBlock(v_nesting_262_, v_input_263_, v_s_264_);
lean_dec_ref(v_input_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object* v_p_266_, lean_object* v_input_267_, lean_object* v_s_268_){
_start:
{
lean_object* v_imports_269_; lean_object* v_pos_270_; uint8_t v_badModifier_271_; lean_object* v_error_x3f_272_; uint8_t v_isModule_273_; uint8_t v_isMeta_274_; uint8_t v_isExported_275_; uint8_t v_importAll_276_; uint8_t v___x_277_; 
v_imports_269_ = lean_ctor_get(v_s_268_, 0);
v_pos_270_ = lean_ctor_get(v_s_268_, 1);
v_badModifier_271_ = lean_ctor_get_uint8(v_s_268_, sizeof(void*)*3);
v_error_x3f_272_ = lean_ctor_get(v_s_268_, 2);
v_isModule_273_ = lean_ctor_get_uint8(v_s_268_, sizeof(void*)*3 + 1);
v_isMeta_274_ = lean_ctor_get_uint8(v_s_268_, sizeof(void*)*3 + 2);
v_isExported_275_ = lean_ctor_get_uint8(v_s_268_, sizeof(void*)*3 + 3);
v_importAll_276_ = lean_ctor_get_uint8(v_s_268_, sizeof(void*)*3 + 4);
v___x_277_ = lean_string_utf8_at_end(v_input_267_, v_pos_270_);
if (v___x_277_ == 0)
{
uint32_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_278_ = lean_string_utf8_get_fast(v_input_267_, v_pos_270_);
v___x_279_ = lean_box_uint32(v___x_278_);
lean_inc_ref(v_p_266_);
v___x_280_ = lean_apply_1(v_p_266_, v___x_279_);
v___x_281_ = lean_unbox(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_290_; 
lean_inc(v_error_x3f_272_);
lean_inc(v_pos_270_);
lean_inc_ref(v_imports_269_);
v_isSharedCheck_290_ = !lean_is_exclusive(v_s_268_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_291_ = lean_ctor_get(v_s_268_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_268_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_s_268_, 0);
lean_dec(v_unused_293_);
v___x_283_ = v_s_268_;
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_s_268_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_string_utf8_next_fast(v_input_267_, v_pos_270_);
lean_dec(v_pos_270_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_imports_269_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_error_x3f_272_);
lean_ctor_set_uint8(v_reuseFailAlloc_289_, sizeof(void*)*3, v_badModifier_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_289_, sizeof(void*)*3 + 1, v_isModule_273_);
lean_ctor_set_uint8(v_reuseFailAlloc_289_, sizeof(void*)*3 + 2, v_isMeta_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_289_, sizeof(void*)*3 + 3, v_isExported_275_);
lean_ctor_set_uint8(v_reuseFailAlloc_289_, sizeof(void*)*3 + 4, v_importAll_276_);
v___x_287_ = v_reuseFailAlloc_289_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v_s_268_ = v___x_287_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_p_266_);
return v_s_268_;
}
}
else
{
lean_dec_ref(v_p_266_);
return v_s_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object* v_p_294_, lean_object* v_input_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_ParseImports_takeUntil(v_p_294_, v_input_295_, v_s_296_);
lean_dec_ref(v_input_295_);
return v_res_297_;
}
}
uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object* v_p_298_, uint32_t v_c_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_box_uint32(v_c_299_);
v___x_301_ = lean_apply_1(v_p_298_, v___x_300_);
v___x_302_ = lean_unbox(v___x_301_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 1;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_takeWhile___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_298_ = stack[0].m_obj;
uint32_t v_c_299_ = stack[1].m_num;
uint8_t v_res_305_;
v_res_305_ = l_Lean_ParseImports_takeWhile___lam__0(v_p_298_, v_c_299_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object* v_p_306_, lean_object* v_c_307_){
_start:
{
uint32_t v_c_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_c_boxed_308_ = lean_unbox_uint32(v_c_307_);
lean_dec(v_c_307_);
v_res_309_ = l_Lean_ParseImports_takeWhile___lam__0(v_p_306_, v_c_boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* v_p_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
v___f_314_ = lean_alloc_closure((void*)(l_Lean_ParseImports_takeWhile___lam__0___boxed), 2, 1);
lean_closure_set(v___f_314_, 0, v_p_311_);
v___x_315_ = l_Lean_ParseImports_takeUntil(v___f_314_, v_a_312_, v_a_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* v_p_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_ParseImports_takeWhile(v_p_316_, v_a_317_, v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* v_p_320_, lean_object* v_q_321_, lean_object* v_input_322_, lean_object* v_s_323_){
_start:
{
lean_object* v_s_324_; lean_object* v_error_x3f_325_; 
lean_inc_ref(v_input_322_);
v_s_324_ = lean_apply_2(v_p_320_, v_input_322_, v_s_323_);
v_error_x3f_325_ = lean_ctor_get(v_s_324_, 2);
lean_inc(v_error_x3f_325_);
if (lean_obj_tag(v_error_x3f_325_) == 1)
{
lean_dec_ref_known(v_error_x3f_325_, 1);
lean_dec_ref(v_input_322_);
lean_dec_ref(v_q_321_);
return v_s_324_;
}
else
{
lean_object* v___x_326_; 
lean_dec(v_error_x3f_325_);
v___x_326_ = lean_apply_2(v_q_321_, v_input_322_, v_s_324_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object* v_p_327_, lean_object* v_q_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_s_331_; lean_object* v_error_x3f_332_; 
lean_inc_ref(v___y_329_);
v_s_331_ = lean_apply_2(v_p_327_, v___y_329_, v___y_330_);
v_error_x3f_332_ = lean_ctor_get(v_s_331_, 2);
lean_inc(v_error_x3f_332_);
if (lean_obj_tag(v_error_x3f_332_) == 1)
{
lean_dec_ref_known(v_error_x3f_332_, 1);
lean_dec_ref(v___y_329_);
lean_dec_ref(v_q_328_);
return v_s_331_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_error_x3f_332_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_3(v_q_328_, v___x_333_, v___y_329_, v_s_331_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(lean_object* v_input_337_, lean_object* v_s_338_){
_start:
{
lean_object* v_imports_339_; lean_object* v_pos_340_; uint8_t v_badModifier_341_; lean_object* v_error_x3f_342_; uint8_t v_isModule_343_; uint8_t v_isMeta_344_; uint8_t v_isExported_345_; uint8_t v_importAll_346_; uint8_t v___x_347_; 
v_imports_339_ = lean_ctor_get(v_s_338_, 0);
v_pos_340_ = lean_ctor_get(v_s_338_, 1);
v_badModifier_341_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*3);
v_error_x3f_342_ = lean_ctor_get(v_s_338_, 2);
v_isModule_343_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*3 + 1);
v_isMeta_344_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*3 + 2);
v_isExported_345_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*3 + 3);
v_importAll_346_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*3 + 4);
v___x_347_ = lean_string_utf8_at_end(v_input_337_, v_pos_340_);
if (v___x_347_ == 0)
{
uint32_t v___x_348_; uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_348_ = lean_string_utf8_get_fast(v_input_337_, v_pos_340_);
v___x_349_ = 10;
v___x_350_ = lean_uint32_dec_eq(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_359_; 
lean_inc(v_error_x3f_342_);
lean_inc(v_pos_340_);
lean_inc_ref(v_imports_339_);
v_isSharedCheck_359_ = !lean_is_exclusive(v_s_338_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_360_ = lean_ctor_get(v_s_338_, 2);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_s_338_, 1);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_s_338_, 0);
lean_dec(v_unused_362_);
v___x_352_ = v_s_338_;
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_s_338_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_string_utf8_next_fast(v_input_337_, v_pos_340_);
lean_dec(v_pos_340_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_imports_339_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_error_x3f_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3, v_badModifier_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 1, v_isModule_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 2, v_isMeta_344_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 3, v_isExported_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 4, v_importAll_346_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_s_338_ = v___x_356_;
goto _start;
}
}
}
else
{
return v_s_338_;
}
}
else
{
return v_s_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(lean_object* v_input_363_, lean_object* v_s_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_363_, v_s_364_);
lean_dec_ref(v_input_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* v_input_369_, lean_object* v_s_370_){
_start:
{
lean_object* v_imports_371_; lean_object* v_pos_372_; uint8_t v_badModifier_373_; lean_object* v_error_x3f_374_; uint8_t v_isModule_375_; uint8_t v_isMeta_376_; uint8_t v_isExported_377_; uint8_t v_importAll_378_; uint8_t v___x_383_; 
v_imports_371_ = lean_ctor_get(v_s_370_, 0);
v_pos_372_ = lean_ctor_get(v_s_370_, 1);
v_badModifier_373_ = lean_ctor_get_uint8(v_s_370_, sizeof(void*)*3);
v_error_x3f_374_ = lean_ctor_get(v_s_370_, 2);
v_isModule_375_ = lean_ctor_get_uint8(v_s_370_, sizeof(void*)*3 + 1);
v_isMeta_376_ = lean_ctor_get_uint8(v_s_370_, sizeof(void*)*3 + 2);
v_isExported_377_ = lean_ctor_get_uint8(v_s_370_, sizeof(void*)*3 + 3);
v_importAll_378_ = lean_ctor_get_uint8(v_s_370_, sizeof(void*)*3 + 4);
v___x_383_ = lean_string_utf8_at_end(v_input_369_, v_pos_372_);
if (v___x_383_ == 0)
{
uint32_t v_curr_384_; uint32_t v___x_385_; uint8_t v___x_386_; 
v_curr_384_ = lean_string_utf8_get_fast(v_input_369_, v_pos_372_);
v___x_385_ = 9;
v___x_386_ = lean_uint32_dec_eq(v_curr_384_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 32;
v___x_388_ = lean_uint32_dec_eq(v_curr_384_, v___x_387_);
if (v___x_388_ == 0)
{
if (v___x_386_ == 0)
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 13;
v___x_390_ = lean_uint32_dec_eq(v_curr_384_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 10;
v___x_392_ = lean_uint32_dec_eq(v_curr_384_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 45;
v___x_394_ = lean_uint32_dec_eq(v_curr_384_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 47;
v___x_396_ = lean_uint32_dec_eq(v_curr_384_, v___x_395_);
if (v___x_396_ == 0)
{
return v_s_370_;
}
else
{
lean_object* v_i_397_; uint32_t v_curr_398_; uint8_t v___x_399_; 
v_i_397_ = lean_string_utf8_next_fast(v_input_369_, v_pos_372_);
v_curr_398_ = lean_string_utf8_get(v_input_369_, v_i_397_);
v___x_399_ = lean_uint32_dec_eq(v_curr_398_, v___x_393_);
if (v___x_399_ == 0)
{
return v_s_370_;
}
else
{
lean_object* v_i_400_; uint32_t v_curr_401_; uint8_t v___x_402_; 
v_i_400_ = lean_string_utf8_next(v_input_369_, v_i_397_);
v_curr_401_ = lean_string_utf8_get(v_input_369_, v_i_400_);
v___x_402_ = lean_uint32_dec_eq(v_curr_401_, v___x_393_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 33;
v___x_404_ = lean_uint32_dec_eq(v_curr_401_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
lean_inc(v_error_x3f_374_);
lean_inc_ref(v_imports_371_);
v_isSharedCheck_416_ = !lean_is_exclusive(v_s_370_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_417_ = lean_ctor_get(v_s_370_, 2);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_s_370_, 1);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_s_370_, 0);
lean_dec(v_unused_419_);
v___x_406_ = v_s_370_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_s_370_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_string_utf8_next(v_input_369_, v_i_400_);
lean_dec(v_i_400_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_409_);
v___x_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_imports_371_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_error_x3f_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3, v_badModifier_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 1, v_isModule_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 2, v_isMeta_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 3, v_isExported_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 4, v_importAll_378_);
v___x_411_ = v_reuseFailAlloc_415_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v_s_412_; lean_object* v_error_x3f_413_; 
v_s_412_ = l_Lean_ParseImports_finishCommentBlock(v___x_408_, v_input_369_, v___x_411_);
v_error_x3f_413_ = lean_ctor_get(v_s_412_, 2);
if (lean_obj_tag(v_error_x3f_413_) == 1)
{
return v_s_412_;
}
else
{
v_s_370_ = v_s_412_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_400_);
return v_s_370_;
}
}
else
{
lean_dec(v_i_400_);
return v_s_370_;
}
}
}
}
else
{
lean_object* v_i_420_; uint32_t v_curr_421_; uint8_t v___x_422_; 
v_i_420_ = lean_string_utf8_next_fast(v_input_369_, v_pos_372_);
v_curr_421_ = lean_string_utf8_get(v_input_369_, v_i_420_);
v___x_422_ = lean_uint32_dec_eq(v_curr_421_, v___x_393_);
if (v___x_422_ == 0)
{
return v_s_370_;
}
else
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_433_; 
lean_inc(v_error_x3f_374_);
lean_inc_ref(v_imports_371_);
v_isSharedCheck_433_ = !lean_is_exclusive(v_s_370_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_434_ = lean_ctor_get(v_s_370_, 2);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_s_370_, 1);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_s_370_, 0);
lean_dec(v_unused_436_);
v___x_424_ = v_s_370_;
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_s_370_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_string_utf8_next(v_input_369_, v_i_420_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_imports_371_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_error_x3f_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3, v_badModifier_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 1, v_isModule_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 2, v_isMeta_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 3, v_isExported_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3 + 4, v_importAll_378_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v_s_429_; lean_object* v_error_x3f_430_; 
v_s_429_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_369_, v___x_428_);
v_error_x3f_430_ = lean_ctor_get(v_s_429_, 2);
if (lean_obj_tag(v_error_x3f_430_) == 1)
{
return v_s_429_;
}
else
{
v_s_370_ = v_s_429_;
goto _start;
}
}
}
}
}
}
else
{
lean_inc(v_error_x3f_374_);
lean_inc(v_pos_372_);
lean_inc_ref(v_imports_371_);
lean_dec_ref(v_s_370_);
goto v___jp_379_;
}
}
else
{
lean_inc(v_error_x3f_374_);
lean_inc(v_pos_372_);
lean_inc_ref(v_imports_371_);
lean_dec_ref(v_s_370_);
goto v___jp_379_;
}
}
else
{
lean_inc(v_error_x3f_374_);
lean_inc(v_pos_372_);
lean_inc_ref(v_imports_371_);
lean_dec_ref(v_s_370_);
goto v___jp_379_;
}
}
else
{
lean_inc(v_error_x3f_374_);
lean_inc(v_pos_372_);
lean_inc_ref(v_imports_371_);
lean_dec_ref(v_s_370_);
goto v___jp_379_;
}
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
lean_inc(v_pos_372_);
lean_inc_ref(v_imports_371_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_s_370_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_445_ = lean_ctor_get(v_s_370_, 2);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_s_370_, 1);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_s_370_, 0);
lean_dec(v_unused_447_);
v___x_438_ = v_s_370_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_s_370_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = ((lean_object*)(l_Lean_ParseImports_whitespace___closed__1));
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 2, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_imports_371_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_pos_372_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v___x_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*3, v_badModifier_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*3 + 1, v_isModule_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*3 + 2, v_isMeta_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*3 + 3, v_isExported_377_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*3 + 4, v_importAll_378_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
return v_s_370_;
}
v___jp_379_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_string_utf8_next(v_input_369_, v_pos_372_);
lean_dec(v_pos_372_);
v___x_381_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_381_, 0, v_imports_371_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_ctor_set(v___x_381_, 2, v_error_x3f_374_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3, v_badModifier_373_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3 + 1, v_isModule_375_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3 + 2, v_isMeta_376_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3 + 3, v_isExported_377_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3 + 4, v_importAll_378_);
v_s_370_ = v___x_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* v_input_448_, lean_object* v_s_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_ParseImports_whitespace(v_input_448_, v_s_449_);
lean_dec_ref(v_input_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object* v_k_451_, lean_object* v_failure_452_, lean_object* v_success_453_, lean_object* v_input_454_, lean_object* v_s_455_, lean_object* v_i_456_, lean_object* v_j_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_string_utf8_at_end(v_k_451_, v_i_456_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = lean_string_utf8_at_end(v_input_454_, v_j_457_);
if (v___x_459_ == 0)
{
uint32_t v_curr_u2081_460_; uint32_t v_curr_u2082_461_; uint8_t v___x_462_; 
v_curr_u2081_460_ = lean_string_utf8_get_fast(v_k_451_, v_i_456_);
v_curr_u2082_461_ = lean_string_utf8_get_fast(v_input_454_, v_j_457_);
v___x_462_ = lean_uint32_dec_eq(v_curr_u2081_460_, v_curr_u2082_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_j_457_);
lean_dec(v_i_456_);
lean_dec_ref(v_success_453_);
v___x_463_ = lean_apply_2(v_failure_452_, v_input_454_, v_s_455_);
return v___x_463_;
}
else
{
if (v___x_459_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_string_utf8_next_fast(v_k_451_, v_i_456_);
lean_dec(v_i_456_);
v___x_465_ = lean_string_utf8_next_fast(v_input_454_, v_j_457_);
lean_dec(v_j_457_);
v_i_456_ = v___x_464_;
v_j_457_ = v___x_465_;
goto _start;
}
else
{
lean_object* v___x_467_; 
lean_dec(v_j_457_);
lean_dec(v_i_456_);
lean_dec_ref(v_success_453_);
v___x_467_ = lean_apply_2(v_failure_452_, v_input_454_, v_s_455_);
return v___x_467_;
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_j_457_);
lean_dec(v_i_456_);
lean_dec_ref(v_success_453_);
v___x_468_ = lean_apply_2(v_failure_452_, v_input_454_, v_s_455_);
return v___x_468_;
}
}
else
{
lean_object* v_imports_469_; uint8_t v_badModifier_470_; lean_object* v_error_x3f_471_; uint8_t v_isModule_472_; uint8_t v_isMeta_473_; uint8_t v_isExported_474_; uint8_t v_importAll_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_i_456_);
lean_dec_ref(v_failure_452_);
v_imports_469_ = lean_ctor_get(v_s_455_, 0);
v_badModifier_470_ = lean_ctor_get_uint8(v_s_455_, sizeof(void*)*3);
v_error_x3f_471_ = lean_ctor_get(v_s_455_, 2);
v_isModule_472_ = lean_ctor_get_uint8(v_s_455_, sizeof(void*)*3 + 1);
v_isMeta_473_ = lean_ctor_get_uint8(v_s_455_, sizeof(void*)*3 + 2);
v_isExported_474_ = lean_ctor_get_uint8(v_s_455_, sizeof(void*)*3 + 3);
v_importAll_475_ = lean_ctor_get_uint8(v_s_455_, sizeof(void*)*3 + 4);
v_isSharedCheck_484_ = !lean_is_exclusive(v_s_455_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_s_455_, 1);
lean_dec(v_unused_485_);
v___x_477_ = v_s_455_;
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_error_x3f_471_);
lean_inc(v_imports_469_);
lean_dec(v_s_455_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v_j_457_);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_imports_469_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_j_457_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_error_x3f_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3, v_badModifier_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3 + 1, v_isModule_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3 + 2, v_isMeta_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3 + 3, v_isExported_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*3 + 4, v_importAll_475_);
v___x_480_ = v_reuseFailAlloc_483_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = l_Lean_ParseImports_whitespace(v_input_454_, v___x_480_);
v___x_482_ = lean_apply_2(v_success_453_, v_input_454_, v___x_481_);
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* v_k_486_, lean_object* v_failure_487_, lean_object* v_success_488_, lean_object* v_input_489_, lean_object* v_s_490_, lean_object* v_i_491_, lean_object* v_j_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_486_, v_failure_487_, v_success_488_, v_input_489_, v_s_490_, v_i_491_, v_j_492_);
lean_dec_ref(v_k_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* v_k_494_, lean_object* v_failure_495_, lean_object* v_success_496_, lean_object* v_input_497_, lean_object* v_s_498_){
_start:
{
lean_object* v_pos_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_pos_499_ = lean_ctor_get(v_s_498_, 1);
lean_inc(v_pos_499_);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_494_, v_failure_495_, v_success_496_, v_input_497_, v_s_498_, v___x_500_, v_pos_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* v_k_502_, lean_object* v_failure_503_, lean_object* v_success_504_, lean_object* v_input_505_, lean_object* v_s_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_ParseImports_keywordCore(v_k_502_, v_failure_503_, v_success_504_, v_input_505_, v_s_506_);
lean_dec_ref(v_k_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* v_k_510_, lean_object* v_x_511_, lean_object* v_s_512_){
_start:
{
lean_object* v_imports_513_; lean_object* v_pos_514_; uint8_t v_badModifier_515_; uint8_t v_isModule_516_; uint8_t v_isMeta_517_; uint8_t v_isExported_518_; uint8_t v_importAll_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_imports_513_ = lean_ctor_get(v_s_512_, 0);
v_pos_514_ = lean_ctor_get(v_s_512_, 1);
v_badModifier_515_ = lean_ctor_get_uint8(v_s_512_, sizeof(void*)*3);
v_isModule_516_ = lean_ctor_get_uint8(v_s_512_, sizeof(void*)*3 + 1);
v_isMeta_517_ = lean_ctor_get_uint8(v_s_512_, sizeof(void*)*3 + 2);
v_isExported_518_ = lean_ctor_get_uint8(v_s_512_, sizeof(void*)*3 + 3);
v_importAll_519_ = lean_ctor_get_uint8(v_s_512_, sizeof(void*)*3 + 4);
v_isSharedCheck_531_ = !lean_is_exclusive(v_s_512_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_s_512_, 2);
lean_dec(v_unused_532_);
v___x_521_ = v_s_512_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_pos_514_);
lean_inc(v_imports_513_);
lean_dec(v_s_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_523_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
v___x_524_ = lean_string_append(v___x_523_, v_k_510_);
v___x_525_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_imports_513_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_pos_514_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v___x_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*3, v_badModifier_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*3 + 1, v_isModule_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*3 + 2, v_isMeta_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*3 + 3, v_isExported_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*3 + 4, v_importAll_519_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* v_k_533_, lean_object* v_x_534_, lean_object* v_s_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_ParseImports_keyword___lam__0(v_k_533_, v_x_534_, v_s_535_);
lean_dec_ref(v_x_534_);
lean_dec_ref(v_k_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* v_k_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_pos_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_pos_540_ = lean_ctor_get(v_a_539_, 1);
lean_inc(v_pos_540_);
lean_inc_ref(v_k_537_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(v___f_541_, 0, v_k_537_);
v___x_542_ = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_537_, v___f_541_, v___x_542_, v_a_538_, v_a_539_, v___x_543_, v_pos_540_);
lean_dec_ref(v_k_537_);
return v___x_544_;
}
}
uint8_t l_Lean_ParseImports_isIdCont(lean_object* v_input_545_, lean_object* v_s_546_){
_start:
{
lean_object* v_pos_547_; uint32_t v_curr_548_; uint32_t v___x_549_; uint8_t v___x_550_; 
v_pos_547_ = lean_ctor_get(v_s_546_, 1);
v_curr_548_ = lean_string_utf8_get(v_input_545_, v_pos_547_);
v___x_549_ = 46;
v___x_550_ = lean_uint32_dec_eq(v_curr_548_, v___x_549_);
if (v___x_550_ == 0)
{
return v___x_550_;
}
else
{
lean_object* v_i_551_; uint8_t v___x_552_; 
v_i_551_ = lean_string_utf8_next(v_input_545_, v_pos_547_);
v___x_552_ = lean_string_utf8_at_end(v_input_545_, v_i_551_);
if (v___x_552_ == 0)
{
uint32_t v_curr_553_; uint32_t v___x_565_; uint8_t v___x_566_; 
v_curr_553_ = lean_string_utf8_get_fast(v_input_545_, v_i_551_);
lean_dec(v_i_551_);
v___x_565_ = 65;
v___x_566_ = lean_uint32_dec_le(v___x_565_, v_curr_553_);
if (v___x_566_ == 0)
{
goto v___jp_560_;
}
else
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 90;
v___x_568_ = lean_uint32_dec_le(v_curr_553_, v___x_567_);
if (v___x_568_ == 0)
{
goto v___jp_560_;
}
else
{
return v___x_550_;
}
}
v___jp_554_:
{
uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 95;
v___x_556_ = lean_uint32_dec_eq(v_curr_553_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_isLetterLike(v_curr_553_);
if (v___x_557_ == 0)
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = l_Lean_idBeginEscape;
v___x_559_ = lean_uint32_dec_eq(v_curr_553_, v___x_558_);
return v___x_559_;
}
else
{
return v___x_550_;
}
}
else
{
return v___x_550_;
}
}
v___jp_560_:
{
uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 97;
v___x_562_ = lean_uint32_dec_le(v___x_561_, v_curr_553_);
if (v___x_562_ == 0)
{
goto v___jp_554_;
}
else
{
uint32_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 122;
v___x_564_ = lean_uint32_dec_le(v_curr_553_, v___x_563_);
if (v___x_564_ == 0)
{
goto v___jp_554_;
}
else
{
return v___x_550_;
}
}
}
}
else
{
uint8_t v___x_569_; 
lean_dec(v_i_551_);
v___x_569_ = 0;
return v___x_569_;
}
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_isIdCont_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_545_ = stack[0].m_obj;
lean_object* v_s_546_ = stack[1].m_obj;
uint8_t v_res_570_;
v_res_570_ = l_Lean_ParseImports_isIdCont(v_input_545_, v_s_546_);
stack->m_num = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_571_, lean_object* v_s_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_ParseImports_isIdCont(v_input_571_, v_s_572_);
lean_dec_ref(v_s_572_);
lean_dec_ref(v_input_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_575_, lean_object* v_s_576_){
_start:
{
lean_object* v_imports_577_; lean_object* v_pos_578_; uint8_t v_badModifier_579_; lean_object* v_error_x3f_580_; uint8_t v_isModule_581_; uint8_t v_isMeta_582_; uint8_t v_isExported_583_; uint8_t v_importAll_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_imports_577_ = lean_ctor_get(v_s_576_, 0);
v_pos_578_ = lean_ctor_get(v_s_576_, 1);
v_badModifier_579_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*3);
v_error_x3f_580_ = lean_ctor_get(v_s_576_, 2);
v_isModule_581_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*3 + 1);
v_isMeta_582_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*3 + 2);
v_isExported_583_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*3 + 3);
v_importAll_584_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*3 + 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_s_576_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_s_576_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_error_x3f_580_);
lean_inc(v_pos_578_);
lean_inc(v_imports_577_);
lean_dec(v_s_576_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_array_push(v_imports_577_, v_i_575_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_pos_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_error_x3f_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*3, v_badModifier_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*3 + 1, v_isModule_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*3 + 2, v_isMeta_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*3 + 3, v_isExported_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*3 + 4, v_importAll_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_593_){
_start:
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 95;
v___x_595_ = lean_uint32_dec_eq(v_c_593_, v___x_594_);
if (v___x_595_ == 0)
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 39;
v___x_597_ = lean_uint32_dec_eq(v_c_593_, v___x_596_);
if (v___x_597_ == 0)
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 33;
v___x_599_ = lean_uint32_dec_eq(v_c_593_, v___x_598_);
if (v___x_599_ == 0)
{
uint32_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 63;
v___x_601_ = lean_uint32_dec_eq(v_c_593_, v___x_600_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_isLetterLike(v_c_593_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_isSubScriptAlnum(v_c_593_);
return v___x_603_;
}
else
{
return v___x_602_;
}
}
else
{
return v___x_601_;
}
}
else
{
return v___x_599_;
}
}
else
{
return v___x_597_;
}
}
else
{
return v___x_595_;
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_isIdRestCold_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_593_ = stack[0].m_num;
uint8_t v_res_604_;
v_res_604_ = l_Lean_ParseImports_isIdRestCold(v_c_593_);
stack->m_num = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_605_){
_start:
{
uint32_t v_c_boxed_606_; uint8_t v_res_607_; lean_object* v_r_608_; 
v_c_boxed_606_ = lean_unbox_uint32(v_c_605_);
lean_dec(v_c_605_);
v_res_607_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_606_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_609_){
_start:
{
uint32_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 65;
v___x_639_ = lean_uint32_dec_le(v___x_638_, v_c_609_);
if (v___x_639_ == 0)
{
goto v___jp_633_;
}
else
{
uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 90;
v___x_641_ = lean_uint32_dec_le(v_c_609_, v___x_640_);
if (v___x_641_ == 0)
{
goto v___jp_633_;
}
else
{
return v___x_641_;
}
}
v___jp_610_:
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 46;
v___x_612_ = lean_uint32_dec_eq(v_c_609_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 10;
v___x_614_ = lean_uint32_dec_eq(v_c_609_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 32;
v___x_616_ = lean_uint32_dec_eq(v_c_609_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 95;
v___x_618_ = lean_uint32_dec_eq(v_c_609_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 39;
v___x_620_ = lean_uint32_dec_eq(v_c_609_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 33;
v___x_622_ = lean_uint32_dec_eq(v_c_609_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 63;
v___x_624_ = lean_uint32_dec_eq(v_c_609_, v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_isLetterLike(v_c_609_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_isSubScriptAlnum(v_c_609_);
return v___x_626_;
}
else
{
return v___x_625_;
}
}
else
{
return v___x_624_;
}
}
else
{
return v___x_622_;
}
}
else
{
return v___x_620_;
}
}
else
{
return v___x_618_;
}
}
else
{
return v___x_614_;
}
}
else
{
return v___x_612_;
}
}
else
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
v___jp_628_:
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 48;
v___x_630_ = lean_uint32_dec_le(v___x_629_, v_c_609_);
if (v___x_630_ == 0)
{
goto v___jp_610_;
}
else
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 57;
v___x_632_ = lean_uint32_dec_le(v_c_609_, v___x_631_);
if (v___x_632_ == 0)
{
goto v___jp_610_;
}
else
{
return v___x_632_;
}
}
}
v___jp_633_:
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 97;
v___x_635_ = lean_uint32_dec_le(v___x_634_, v_c_609_);
if (v___x_635_ == 0)
{
goto v___jp_628_;
}
else
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 122;
v___x_637_ = lean_uint32_dec_le(v_c_609_, v___x_636_);
if (v___x_637_ == 0)
{
goto v___jp_628_;
}
else
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_isIdRestFast_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_609_ = stack[0].m_num;
uint8_t v_res_642_;
v_res_642_ = l_Lean_ParseImports_isIdRestFast(v_c_609_);
stack->m_num = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_643_){
_start:
{
uint32_t v_c_boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_c_boxed_644_ = lean_unbox_uint32(v_c_643_);
lean_dec(v_c_643_);
v_res_645_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_647_, lean_object* v_s_648_){
_start:
{
lean_object* v_imports_649_; lean_object* v_pos_650_; uint8_t v_badModifier_651_; lean_object* v_error_x3f_652_; uint8_t v_isModule_653_; uint8_t v_isMeta_654_; uint8_t v_isExported_655_; uint8_t v_importAll_656_; uint8_t v___x_657_; 
v_imports_649_ = lean_ctor_get(v_s_648_, 0);
v_pos_650_ = lean_ctor_get(v_s_648_, 1);
v_badModifier_651_ = lean_ctor_get_uint8(v_s_648_, sizeof(void*)*3);
v_error_x3f_652_ = lean_ctor_get(v_s_648_, 2);
v_isModule_653_ = lean_ctor_get_uint8(v_s_648_, sizeof(void*)*3 + 1);
v_isMeta_654_ = lean_ctor_get_uint8(v_s_648_, sizeof(void*)*3 + 2);
v_isExported_655_ = lean_ctor_get_uint8(v_s_648_, sizeof(void*)*3 + 3);
v_importAll_656_ = lean_ctor_get_uint8(v_s_648_, sizeof(void*)*3 + 4);
v___x_657_ = lean_string_utf8_at_end(v_input_647_, v_pos_650_);
if (v___x_657_ == 0)
{
uint32_t v___x_658_; uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_string_utf8_get_fast(v_input_647_, v_pos_650_);
v___x_659_ = l_Lean_idEndEscape;
v___x_660_ = lean_uint32_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
lean_inc(v_error_x3f_652_);
lean_inc(v_pos_650_);
lean_inc_ref(v_imports_649_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_s_648_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_670_ = lean_ctor_get(v_s_648_, 2);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_s_648_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_s_648_, 0);
lean_dec(v_unused_672_);
v___x_662_ = v_s_648_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_s_648_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_string_utf8_next_fast(v_input_647_, v_pos_650_);
lean_dec(v_pos_650_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_imports_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_error_x3f_652_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3, v_badModifier_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 1, v_isModule_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 2, v_isMeta_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 3, v_isExported_655_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 4, v_importAll_656_);
v___x_666_ = v_reuseFailAlloc_668_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v_s_648_ = v___x_666_;
goto _start;
}
}
}
else
{
return v_s_648_;
}
}
else
{
return v_s_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_673_, lean_object* v_s_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_673_, v_s_674_);
lean_dec_ref(v_input_673_);
return v_res_675_;
}
}
lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_676_, uint32_t v___x_677_, lean_object* v_input_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_imports_680_; lean_object* v_pos_681_; uint8_t v_badModifier_682_; lean_object* v_error_x3f_683_; uint8_t v_isModule_684_; uint8_t v_isMeta_685_; uint8_t v_isExported_686_; uint8_t v_importAll_687_; uint8_t v___y_689_; uint8_t v___x_702_; 
v_imports_680_ = lean_ctor_get(v_s_679_, 0);
v_pos_681_ = lean_ctor_get(v_s_679_, 1);
v_badModifier_682_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*3);
v_error_x3f_683_ = lean_ctor_get(v_s_679_, 2);
v_isModule_684_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*3 + 1);
v_isMeta_685_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*3 + 2);
v_isExported_686_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*3 + 3);
v_importAll_687_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*3 + 4);
v___x_702_ = lean_string_utf8_at_end(v_input_678_, v_pos_681_);
if (v___x_702_ == 0)
{
uint32_t v___x_703_; uint8_t v___x_704_; uint32_t v___x_705_; uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_703_ = l_Lean_idBeginEscape;
v___x_704_ = lean_uint32_dec_eq(v___x_677_, v___x_703_);
v___x_705_ = lean_string_utf8_get_fast(v_input_678_, v_pos_681_);
v___x_733_ = 65;
v___x_734_ = lean_uint32_dec_le(v___x_733_, v___x_705_);
if (v___x_734_ == 0)
{
goto v___jp_728_;
}
else
{
uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 90;
v___x_736_ = lean_uint32_dec_le(v___x_705_, v___x_735_);
if (v___x_736_ == 0)
{
goto v___jp_728_;
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
v___jp_706_:
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 46;
v___x_708_ = lean_uint32_dec_eq(v___x_705_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 10;
v___x_710_ = lean_uint32_dec_eq(v___x_705_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 32;
v___x_712_ = lean_uint32_dec_eq(v___x_705_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 95;
v___x_714_ = lean_uint32_dec_eq(v___x_705_, v___x_713_);
if (v___x_714_ == 0)
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 39;
v___x_716_ = lean_uint32_dec_eq(v___x_705_, v___x_715_);
if (v___x_716_ == 0)
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 33;
v___x_718_ = lean_uint32_dec_eq(v___x_705_, v___x_717_);
if (v___x_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 63;
v___x_720_ = lean_uint32_dec_eq(v___x_705_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_isLetterLike(v___x_705_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_isSubScriptAlnum(v___x_705_);
if (v___x_722_ == 0)
{
v___y_689_ = v___y_676_;
goto v___jp_688_;
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
else
{
if (v___x_721_ == 0)
{
v___y_689_ = v___y_676_;
goto v___jp_688_;
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___y_676_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___y_676_;
goto v___jp_688_;
}
}
else
{
v___y_689_ = v___y_676_;
goto v___jp_688_;
}
}
v___jp_723_:
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 48;
v___x_725_ = lean_uint32_dec_le(v___x_724_, v___x_705_);
if (v___x_725_ == 0)
{
goto v___jp_706_;
}
else
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 57;
v___x_727_ = lean_uint32_dec_le(v___x_705_, v___x_726_);
if (v___x_727_ == 0)
{
goto v___jp_706_;
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
}
v___jp_728_:
{
uint32_t v___x_729_; uint8_t v___x_730_; 
v___x_729_ = 97;
v___x_730_ = lean_uint32_dec_le(v___x_729_, v___x_705_);
if (v___x_730_ == 0)
{
goto v___jp_723_;
}
else
{
uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 122;
v___x_732_ = lean_uint32_dec_le(v___x_705_, v___x_731_);
if (v___x_732_ == 0)
{
goto v___jp_723_;
}
else
{
v___y_689_ = v___x_704_;
goto v___jp_688_;
}
}
}
}
else
{
return v_s_679_;
}
v___jp_688_:
{
if (v___y_689_ == 0)
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_698_; 
lean_inc(v_error_x3f_683_);
lean_inc(v_pos_681_);
lean_inc_ref(v_imports_680_);
v_isSharedCheck_698_ = !lean_is_exclusive(v_s_679_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_699_ = lean_ctor_get(v_s_679_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_s_679_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_s_679_, 0);
lean_dec(v_unused_701_);
v___x_691_ = v_s_679_;
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_s_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_string_utf8_next_fast(v_input_678_, v_pos_681_);
lean_dec(v_pos_681_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_imports_680_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_error_x3f_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3, v_badModifier_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 1, v_isModule_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 2, v_isMeta_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 3, v_isExported_686_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 4, v_importAll_687_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_s_679_ = v___x_695_;
goto _start;
}
}
}
else
{
return v_s_679_;
}
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_676_ = stack[0].m_num;
uint32_t v___x_677_ = stack[1].m_num;
lean_object* v_input_678_ = stack[2].m_obj;
lean_object* v_s_679_ = stack[3].m_obj;
lean_object* v_res_737_;
v_res_737_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_676_, v___x_677_, v_input_678_, v_s_679_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_738_, lean_object* v___x_739_, lean_object* v_input_740_, lean_object* v_s_741_){
_start:
{
uint8_t v___y_1028__boxed_742_; uint32_t v___x_1029__boxed_743_; lean_object* v_res_744_; 
v___y_1028__boxed_742_ = lean_unbox(v___y_738_);
v___x_1029__boxed_743_ = lean_unbox_uint32(v___x_739_);
lean_dec(v___x_739_);
v_res_744_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_1028__boxed_742_, v___x_1029__boxed_743_, v_input_740_, v_s_741_);
lean_dec_ref(v_input_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_751_, lean_object* v_finalize_752_, lean_object* v_module_753_, lean_object* v_s_754_){
_start:
{
lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; uint8_t v___y_760_; uint8_t v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v_imports_768_; lean_object* v_pos_769_; uint8_t v_badModifier_770_; lean_object* v_error_x3f_771_; uint8_t v_isModule_772_; uint8_t v_isMeta_773_; uint8_t v_isExported_774_; uint8_t v_importAll_775_; uint8_t v___x_776_; 
v_imports_768_ = lean_ctor_get(v_s_754_, 0);
v_pos_769_ = lean_ctor_get(v_s_754_, 1);
v_badModifier_770_ = lean_ctor_get_uint8(v_s_754_, sizeof(void*)*3);
v_error_x3f_771_ = lean_ctor_get(v_s_754_, 2);
v_isModule_772_ = lean_ctor_get_uint8(v_s_754_, sizeof(void*)*3 + 1);
v_isMeta_773_ = lean_ctor_get_uint8(v_s_754_, sizeof(void*)*3 + 2);
v_isExported_774_ = lean_ctor_get_uint8(v_s_754_, sizeof(void*)*3 + 3);
v_importAll_775_ = lean_ctor_get_uint8(v_s_754_, sizeof(void*)*3 + 4);
v___x_776_ = lean_string_utf8_at_end(v_input_751_, v_pos_769_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_914_; 
lean_inc(v_error_x3f_771_);
lean_inc(v_pos_769_);
lean_inc_ref(v_imports_768_);
v_isSharedCheck_914_ = !lean_is_exclusive(v_s_754_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_915_ = lean_ctor_get(v_s_754_, 2);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_s_754_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_s_754_, 0);
lean_dec(v_unused_917_);
v___x_778_ = v_s_754_;
v_isShared_779_ = v_isSharedCheck_914_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_s_754_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_914_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
uint32_t v_curr_780_; uint32_t v___x_781_; lean_object* v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; uint32_t v___y_788_; uint8_t v___y_789_; uint8_t v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; uint32_t v___y_805_; uint8_t v___y_806_; uint8_t v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___y_816_; uint8_t v___x_855_; 
v_curr_780_ = lean_string_utf8_get_fast(v_input_751_, v_pos_769_);
v___x_781_ = l_Lean_idBeginEscape;
v___x_855_ = lean_uint32_dec_eq(v_curr_780_, v___x_781_);
if (v___x_855_ == 0)
{
uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_856_ = 65;
v___x_857_ = lean_uint32_dec_le(v___x_856_, v_curr_780_);
if (v___x_857_ == 0)
{
goto v___jp_850_;
}
else
{
uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = 90;
v___x_859_ = lean_uint32_dec_le(v_curr_780_, v___x_858_);
if (v___x_859_ == 0)
{
goto v___jp_850_;
}
else
{
v___y_816_ = v___x_859_;
goto v___jp_815_;
}
}
}
else
{
lean_object* v_startPart_860_; lean_object* v___x_861_; lean_object* v_s_862_; lean_object* v_imports_863_; lean_object* v_pos_864_; uint8_t v_badModifier_865_; lean_object* v_error_x3f_866_; uint8_t v_isModule_867_; uint8_t v_isMeta_868_; uint8_t v_isExported_869_; uint8_t v_importAll_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_913_; 
lean_del_object(v___x_778_);
v_startPart_860_ = lean_string_utf8_next_fast(v_input_751_, v_pos_769_);
lean_dec(v_pos_769_);
v___x_861_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_861_, 0, v_imports_768_);
lean_ctor_set(v___x_861_, 1, v_startPart_860_);
lean_ctor_set(v___x_861_, 2, v_error_x3f_771_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3, v_badModifier_770_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 1, v_isModule_772_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 2, v_isMeta_773_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 3, v_isExported_774_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 4, v_importAll_775_);
v_s_862_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_751_, v___x_861_);
v_imports_863_ = lean_ctor_get(v_s_862_, 0);
v_pos_864_ = lean_ctor_get(v_s_862_, 1);
v_badModifier_865_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3);
v_error_x3f_866_ = lean_ctor_get(v_s_862_, 2);
v_isModule_867_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 1);
v_isMeta_868_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 2);
v_isExported_869_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 3);
v_importAll_870_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 4);
v_isSharedCheck_913_ = !lean_is_exclusive(v_s_862_);
if (v_isSharedCheck_913_ == 0)
{
v___x_872_ = v_s_862_;
v_isShared_873_ = v_isSharedCheck_913_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_error_x3f_866_);
lean_inc(v_pos_864_);
lean_inc(v_imports_863_);
lean_dec(v_s_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_913_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_string_utf8_at_end(v_input_751_, v_pos_864_);
if (v___x_874_ == 0)
{
lean_object* v_i_875_; lean_object* v_s_877_; 
v_i_875_ = lean_string_utf8_next_fast(v_input_751_, v_pos_864_);
lean_inc(v_error_x3f_866_);
lean_inc_ref(v_imports_863_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v_i_875_);
v_s_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_imports_863_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_i_875_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_error_x3f_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*3 + 4, v_importAll_870_);
v_s_877_ = v_reuseFailAlloc_908_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v_module_879_; uint8_t v___y_885_; uint32_t v_curr_887_; uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_878_ = lean_string_utf8_extract(v_input_751_, v_startPart_860_, v_pos_864_);
lean_dec(v_pos_864_);
v_module_879_ = l_Lean_Name_str___override(v_module_753_, v___x_878_);
v_curr_887_ = lean_string_utf8_get(v_input_751_, v_i_875_);
v___x_888_ = 46;
v___x_889_ = lean_uint32_dec_eq(v_curr_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_error_x3f_866_);
lean_dec_ref(v_imports_863_);
v___x_890_ = lean_apply_3(v_finalize_752_, v_module_879_, v_input_751_, v_s_877_);
return v___x_890_;
}
else
{
lean_object* v_i_891_; uint8_t v___x_892_; 
v_i_891_ = lean_string_utf8_next(v_input_751_, v_i_875_);
v___x_892_ = lean_string_utf8_at_end(v_input_751_, v_i_891_);
if (v___x_892_ == 0)
{
uint32_t v_curr_893_; uint32_t v___x_904_; uint8_t v___x_905_; 
v_curr_893_ = lean_string_utf8_get_fast(v_input_751_, v_i_891_);
lean_dec(v_i_891_);
v___x_904_ = 65;
v___x_905_ = lean_uint32_dec_le(v___x_904_, v_curr_893_);
if (v___x_905_ == 0)
{
goto v___jp_899_;
}
else
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 90;
v___x_907_ = lean_uint32_dec_le(v_curr_893_, v___x_906_);
if (v___x_907_ == 0)
{
goto v___jp_899_;
}
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
}
}
v___jp_894_:
{
uint32_t v___x_895_; uint8_t v___x_896_; 
v___x_895_ = 95;
v___x_896_ = lean_uint32_dec_eq(v_curr_893_, v___x_895_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_isLetterLike(v_curr_893_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
v___x_898_ = lean_uint32_dec_eq(v_curr_893_, v___x_781_);
v___y_885_ = v___x_898_;
goto v___jp_884_;
}
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
}
}
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
}
}
v___jp_899_:
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 97;
v___x_901_ = lean_uint32_dec_le(v___x_900_, v_curr_893_);
if (v___x_901_ == 0)
{
goto v___jp_894_;
}
else
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 122;
v___x_903_ = lean_uint32_dec_le(v_curr_893_, v___x_902_);
if (v___x_903_ == 0)
{
goto v___jp_894_;
}
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
}
}
}
}
else
{
lean_dec(v_i_891_);
v___y_885_ = v___x_874_;
goto v___jp_884_;
}
}
v___jp_880_:
{
lean_object* v___x_881_; lean_object* v_s_882_; 
v___x_881_ = lean_string_utf8_next(v_input_751_, v_i_875_);
v_s_882_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_882_, 0, v_imports_863_);
lean_ctor_set(v_s_882_, 1, v___x_881_);
lean_ctor_set(v_s_882_, 2, v_error_x3f_866_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 4, v_importAll_870_);
v_module_753_ = v_module_879_;
v_s_754_ = v_s_882_;
goto _start;
}
v___jp_884_:
{
if (v___y_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_error_x3f_866_);
lean_dec_ref(v_imports_863_);
v___x_886_ = lean_apply_3(v_finalize_752_, v_module_879_, v_input_751_, v_s_877_);
return v___x_886_;
}
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
}
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_error_x3f_866_);
lean_dec(v_module_753_);
lean_dec_ref(v_finalize_752_);
lean_dec_ref(v_input_751_);
v___x_909_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 2, v___x_909_);
v___x_911_ = v___x_872_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_imports_863_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_pos_864_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v___x_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 4, v_importAll_870_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
v___jp_782_:
{
uint32_t v___x_794_; uint8_t v___x_795_; 
v___x_794_ = 95;
v___x_795_ = lean_uint32_dec_eq(v___y_788_, v___x_794_);
if (v___x_795_ == 0)
{
uint8_t v___x_796_; 
v___x_796_ = l_Lean_isLetterLike(v___y_788_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; 
v___x_797_ = lean_uint32_dec_eq(v___y_788_, v___x_781_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_783_);
v___x_798_ = lean_apply_3(v_finalize_752_, v___y_785_, v_input_751_, v___y_787_);
return v___x_798_;
}
else
{
lean_dec_ref(v___y_787_);
v___y_756_ = v___y_783_;
v___y_757_ = v___y_784_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_786_;
v___y_760_ = v___y_789_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v___y_793_;
v___y_764_ = v___y_792_;
goto v___jp_755_;
}
}
else
{
lean_dec_ref(v___y_787_);
v___y_756_ = v___y_783_;
v___y_757_ = v___y_784_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_786_;
v___y_760_ = v___y_789_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v___y_793_;
v___y_764_ = v___y_792_;
goto v___jp_755_;
}
}
else
{
lean_dec_ref(v___y_787_);
v___y_756_ = v___y_783_;
v___y_757_ = v___y_784_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_786_;
v___y_760_ = v___y_789_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v___y_793_;
v___y_764_ = v___y_792_;
goto v___jp_755_;
}
}
v___jp_799_:
{
uint32_t v___x_811_; uint8_t v___x_812_; 
v___x_811_ = 97;
v___x_812_ = lean_uint32_dec_le(v___x_811_, v___y_805_);
if (v___x_812_ == 0)
{
v___y_783_ = v___y_800_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_804_;
v___y_787_ = v___y_803_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
v___y_792_ = v___y_810_;
v___y_793_ = v___y_809_;
goto v___jp_782_;
}
else
{
uint32_t v___x_813_; uint8_t v___x_814_; 
v___x_813_ = 122;
v___x_814_ = lean_uint32_dec_le(v___y_805_, v___x_813_);
if (v___x_814_ == 0)
{
v___y_783_ = v___y_800_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_804_;
v___y_787_ = v___y_803_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
v___y_792_ = v___y_810_;
v___y_793_ = v___y_809_;
goto v___jp_782_;
}
else
{
lean_dec_ref(v___y_803_);
v___y_756_ = v___y_800_;
v___y_757_ = v___y_801_;
v___y_758_ = v___y_802_;
v___y_759_ = v___y_804_;
v___y_760_ = v___y_806_;
v___y_761_ = v___y_807_;
v___y_762_ = v___y_808_;
v___y_763_ = v___y_809_;
v___y_764_ = v___y_810_;
goto v___jp_755_;
}
}
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_string_utf8_next_fast(v_input_751_, v_pos_769_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_817_);
v___x_819_ = v___x_778_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_imports_768_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_error_x3f_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*3, v_badModifier_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*3 + 1, v_isModule_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*3 + 2, v_isMeta_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*3 + 3, v_isExported_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*3 + 4, v_importAll_775_);
v___x_819_ = v_reuseFailAlloc_843_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v_s_820_; lean_object* v_imports_821_; lean_object* v_pos_822_; uint8_t v_badModifier_823_; lean_object* v_error_x3f_824_; uint8_t v_isModule_825_; uint8_t v_isMeta_826_; uint8_t v_isExported_827_; uint8_t v_importAll_828_; lean_object* v___x_829_; lean_object* v_module_830_; uint32_t v_curr_831_; uint32_t v___x_832_; uint8_t v___x_833_; 
v_s_820_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_816_, v_curr_780_, v_input_751_, v___x_819_);
v_imports_821_ = lean_ctor_get(v_s_820_, 0);
v_pos_822_ = lean_ctor_get(v_s_820_, 1);
v_badModifier_823_ = lean_ctor_get_uint8(v_s_820_, sizeof(void*)*3);
v_error_x3f_824_ = lean_ctor_get(v_s_820_, 2);
v_isModule_825_ = lean_ctor_get_uint8(v_s_820_, sizeof(void*)*3 + 1);
v_isMeta_826_ = lean_ctor_get_uint8(v_s_820_, sizeof(void*)*3 + 2);
v_isExported_827_ = lean_ctor_get_uint8(v_s_820_, sizeof(void*)*3 + 3);
v_importAll_828_ = lean_ctor_get_uint8(v_s_820_, sizeof(void*)*3 + 4);
v___x_829_ = lean_string_utf8_extract(v_input_751_, v_pos_769_, v_pos_822_);
lean_dec(v_pos_769_);
v_module_830_ = l_Lean_Name_str___override(v_module_753_, v___x_829_);
v_curr_831_ = lean_string_utf8_get(v_input_751_, v_pos_822_);
v___x_832_ = 46;
v___x_833_ = lean_uint32_dec_eq(v_curr_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_apply_3(v_finalize_752_, v_module_830_, v_input_751_, v_s_820_);
return v___x_834_;
}
else
{
lean_object* v_i_835_; uint8_t v___x_836_; 
v_i_835_ = lean_string_utf8_next(v_input_751_, v_pos_822_);
v___x_836_ = lean_string_utf8_at_end(v_input_751_, v_i_835_);
if (v___x_836_ == 0)
{
uint32_t v_curr_837_; uint32_t v___x_838_; uint8_t v___x_839_; 
lean_inc(v_error_x3f_824_);
lean_inc(v_pos_822_);
lean_inc_ref(v_imports_821_);
v_curr_837_ = lean_string_utf8_get_fast(v_input_751_, v_i_835_);
lean_dec(v_i_835_);
v___x_838_ = 65;
v___x_839_ = lean_uint32_dec_le(v___x_838_, v_curr_837_);
if (v___x_839_ == 0)
{
v___y_800_ = v_pos_822_;
v___y_801_ = v_importAll_828_;
v___y_802_ = v_module_830_;
v___y_803_ = v_s_820_;
v___y_804_ = v_isExported_827_;
v___y_805_ = v_curr_837_;
v___y_806_ = v_isModule_825_;
v___y_807_ = v_isMeta_826_;
v___y_808_ = v_badModifier_823_;
v___y_809_ = v_error_x3f_824_;
v___y_810_ = v_imports_821_;
goto v___jp_799_;
}
else
{
uint32_t v___x_840_; uint8_t v___x_841_; 
v___x_840_ = 90;
v___x_841_ = lean_uint32_dec_le(v_curr_837_, v___x_840_);
if (v___x_841_ == 0)
{
v___y_800_ = v_pos_822_;
v___y_801_ = v_importAll_828_;
v___y_802_ = v_module_830_;
v___y_803_ = v_s_820_;
v___y_804_ = v_isExported_827_;
v___y_805_ = v_curr_837_;
v___y_806_ = v_isModule_825_;
v___y_807_ = v_isMeta_826_;
v___y_808_ = v_badModifier_823_;
v___y_809_ = v_error_x3f_824_;
v___y_810_ = v_imports_821_;
goto v___jp_799_;
}
else
{
lean_dec_ref(v_s_820_);
v___y_756_ = v_pos_822_;
v___y_757_ = v_importAll_828_;
v___y_758_ = v_module_830_;
v___y_759_ = v_isExported_827_;
v___y_760_ = v_isModule_825_;
v___y_761_ = v_isMeta_826_;
v___y_762_ = v_badModifier_823_;
v___y_763_ = v_error_x3f_824_;
v___y_764_ = v_imports_821_;
goto v___jp_755_;
}
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v_i_835_);
v___x_842_ = lean_apply_3(v_finalize_752_, v_module_830_, v_input_751_, v_s_820_);
return v___x_842_;
}
}
}
}
v___jp_844_:
{
uint32_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 95;
v___x_846_ = lean_uint32_dec_eq(v_curr_780_, v___x_845_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_isLetterLike(v_curr_780_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_del_object(v___x_778_);
lean_dec(v_error_x3f_771_);
lean_dec(v_module_753_);
lean_dec_ref(v_finalize_752_);
lean_dec_ref(v_input_751_);
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_849_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_849_, 0, v_imports_768_);
lean_ctor_set(v___x_849_, 1, v_pos_769_);
lean_ctor_set(v___x_849_, 2, v___x_848_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3, v_badModifier_770_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3 + 1, v_isModule_772_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3 + 2, v_isMeta_773_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3 + 3, v_isExported_774_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3 + 4, v_importAll_775_);
return v___x_849_;
}
else
{
v___y_816_ = v___x_847_;
goto v___jp_815_;
}
}
else
{
v___y_816_ = v___x_846_;
goto v___jp_815_;
}
}
v___jp_850_:
{
uint32_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 97;
v___x_852_ = lean_uint32_dec_le(v___x_851_, v_curr_780_);
if (v___x_852_ == 0)
{
goto v___jp_844_;
}
else
{
uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 122;
v___x_854_ = lean_uint32_dec_le(v_curr_780_, v___x_853_);
if (v___x_854_ == 0)
{
goto v___jp_844_;
}
else
{
v___y_816_ = v___x_854_;
goto v___jp_815_;
}
}
}
}
}
else
{
lean_object* v___x_918_; 
lean_dec(v_module_753_);
lean_dec_ref(v_finalize_752_);
lean_dec_ref(v_input_751_);
v___x_918_ = l_Lean_ParseImports_State_mkEOIError(v_s_754_);
return v___x_918_;
}
v___jp_755_:
{
lean_object* v___x_765_; lean_object* v_s_766_; 
v___x_765_ = lean_string_utf8_next(v_input_751_, v___y_756_);
lean_dec(v___y_756_);
v_s_766_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_766_, 0, v___y_764_);
lean_ctor_set(v_s_766_, 1, v___x_765_);
lean_ctor_set(v_s_766_, 2, v___y_763_);
lean_ctor_set_uint8(v_s_766_, sizeof(void*)*3, v___y_762_);
lean_ctor_set_uint8(v_s_766_, sizeof(void*)*3 + 1, v___y_760_);
lean_ctor_set_uint8(v_s_766_, sizeof(void*)*3 + 2, v___y_761_);
lean_ctor_set_uint8(v_s_766_, sizeof(void*)*3 + 3, v___y_759_);
lean_ctor_set_uint8(v_s_766_, sizeof(void*)*3 + 4, v___y_757_);
v_module_753_ = v___y_758_;
v_s_754_ = v_s_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_919_, lean_object* v_input_920_, lean_object* v_s_921_){
_start:
{
uint8_t v_isMeta_922_; uint8_t v_isExported_923_; uint8_t v_importAll_924_; lean_object* v_imp_925_; lean_object* v___x_926_; lean_object* v_s_927_; lean_object* v_imports_928_; lean_object* v_pos_929_; uint8_t v_badModifier_930_; lean_object* v_error_x3f_931_; uint8_t v_isModule_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_944_; 
v_isMeta_922_ = lean_ctor_get_uint8(v_s_921_, sizeof(void*)*3 + 2);
v_isExported_923_ = lean_ctor_get_uint8(v_s_921_, sizeof(void*)*3 + 3);
v_importAll_924_ = lean_ctor_get_uint8(v_s_921_, sizeof(void*)*3 + 4);
v_imp_925_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_925_, 0, v_module_919_);
lean_ctor_set_uint8(v_imp_925_, sizeof(void*)*1, v_importAll_924_);
lean_ctor_set_uint8(v_imp_925_, sizeof(void*)*1 + 1, v_isExported_923_);
lean_ctor_set_uint8(v_imp_925_, sizeof(void*)*1 + 2, v_isMeta_922_);
v___x_926_ = l_Lean_ParseImports_State_pushImport(v_imp_925_, v_s_921_);
v_s_927_ = l_Lean_ParseImports_whitespace(v_input_920_, v___x_926_);
v_imports_928_ = lean_ctor_get(v_s_927_, 0);
v_pos_929_ = lean_ctor_get(v_s_927_, 1);
v_badModifier_930_ = lean_ctor_get_uint8(v_s_927_, sizeof(void*)*3);
v_error_x3f_931_ = lean_ctor_get(v_s_927_, 2);
v_isModule_932_ = lean_ctor_get_uint8(v_s_927_, sizeof(void*)*3 + 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_s_927_);
if (v_isSharedCheck_944_ == 0)
{
v___x_934_ = v_s_927_;
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_error_x3f_931_);
lean_inc(v_pos_929_);
lean_inc(v_imports_928_);
lean_dec(v_s_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v___x_936_; 
v___x_936_ = 0;
if (v_isModule_932_ == 0)
{
uint8_t v___x_937_; lean_object* v___x_939_; 
v___x_937_ = 1;
if (v_isShared_935_ == 0)
{
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_imports_928_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_pos_929_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_error_x3f_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3, v_badModifier_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3 + 1, v_isModule_932_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 2, v___x_936_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 3, v___x_937_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3 + 4, v___x_936_);
return v___x_939_;
}
}
else
{
lean_object* v___x_942_; 
if (v_isShared_935_ == 0)
{
v___x_942_ = v___x_934_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_imports_928_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_pos_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_error_x3f_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3, v_badModifier_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3 + 1, v_isModule_932_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*3 + 2, v___x_936_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*3 + 3, v___x_936_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*3 + 4, v___x_936_);
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_945_, lean_object* v_input_946_, lean_object* v_s_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_945_, v_input_946_, v_s_947_);
lean_dec_ref(v_input_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_950_, lean_object* v_s_951_){
_start:
{
lean_object* v_finalize_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_finalize_952_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_953_ = lean_box(0);
v___x_954_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_950_, v_finalize_952_, v___x_953_, v_s_951_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_955_, lean_object* v_input_956_, lean_object* v_s_957_){
_start:
{
lean_object* v_pos_958_; lean_object* v_s_959_; lean_object* v_error_x3f_960_; 
v_pos_958_ = lean_ctor_get(v_s_957_, 1);
lean_inc(v_pos_958_);
v_s_959_ = lean_apply_2(v_p_955_, v_input_956_, v_s_957_);
v_error_x3f_960_ = lean_ctor_get(v_s_959_, 2);
lean_inc(v_error_x3f_960_);
if (lean_obj_tag(v_error_x3f_960_) == 1)
{
lean_object* v_imports_961_; uint8_t v_badModifier_962_; uint8_t v_isModule_963_; uint8_t v_isMeta_964_; uint8_t v_isExported_965_; uint8_t v_importAll_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_imports_961_ = lean_ctor_get(v_s_959_, 0);
v_badModifier_962_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3);
v_isModule_963_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3 + 1);
v_isMeta_964_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3 + 2);
v_isExported_965_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3 + 3);
v_importAll_966_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3 + 4);
v_isSharedCheck_973_ = !lean_is_exclusive(v_s_959_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v_s_959_, 2);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_s_959_, 1);
lean_dec(v_unused_975_);
v___x_968_ = v_s_959_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_imports_961_);
lean_dec(v_s_959_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_pos_958_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_imports_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_pos_958_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_error_x3f_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_badModifier_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_isModule_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 2, v_isMeta_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 3, v_isExported_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 4, v_importAll_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_dec(v_error_x3f_960_);
lean_dec(v_pos_958_);
return v_s_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_979_, lean_object* v_input_980_, lean_object* v_s_981_){
_start:
{
lean_object* v_pos_982_; lean_object* v_s_983_; lean_object* v_error_x3f_984_; 
v_pos_982_ = lean_ctor_get(v_s_981_, 1);
lean_inc(v_pos_982_);
lean_inc_ref(v_p_979_);
lean_inc_ref(v_input_980_);
v_s_983_ = lean_apply_2(v_p_979_, v_input_980_, v_s_981_);
v_error_x3f_984_ = lean_ctor_get(v_s_983_, 2);
lean_inc(v_error_x3f_984_);
if (lean_obj_tag(v_error_x3f_984_) == 1)
{
lean_object* v_imports_985_; lean_object* v_pos_986_; uint8_t v_isModule_987_; uint8_t v_isMeta_988_; uint8_t v_isExported_989_; uint8_t v_importAll_990_; uint8_t v_decide_991_; 
lean_dec_ref_known(v_error_x3f_984_, 1);
lean_dec_ref(v_input_980_);
lean_dec_ref(v_p_979_);
v_imports_985_ = lean_ctor_get(v_s_983_, 0);
lean_inc_ref(v_imports_985_);
v_pos_986_ = lean_ctor_get(v_s_983_, 1);
lean_inc(v_pos_986_);
v_isModule_987_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 1);
v_isMeta_988_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 2);
v_isExported_989_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 3);
v_importAll_990_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 4);
v_decide_991_ = lean_nat_dec_eq(v_pos_986_, v_pos_982_);
lean_dec(v_pos_982_);
if (v_decide_991_ == 0)
{
lean_dec(v_pos_986_);
lean_dec_ref(v_imports_985_);
return v_s_983_;
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v_s_983_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; lean_object* v_unused_1003_; 
v_unused_1001_ = lean_ctor_get(v_s_983_, 2);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_s_983_, 1);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_s_983_, 0);
lean_dec(v_unused_1003_);
v___x_993_ = v_s_983_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_s_983_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_995_ = 0;
v___x_996_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 2, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_imports_985_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_pos_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3 + 1, v_isModule_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3 + 2, v_isMeta_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3 + 3, v_isExported_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3 + 4, v_importAll_990_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*3, v___x_995_);
return v___x_998_;
}
}
}
}
else
{
uint8_t v_badModifier_1004_; 
lean_dec(v_error_x3f_984_);
v_badModifier_1004_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3);
if (v_badModifier_1004_ == 0)
{
lean_dec(v_pos_982_);
v_s_981_ = v_s_983_;
goto _start;
}
else
{
lean_object* v_imports_1006_; uint8_t v_isModule_1007_; uint8_t v_isMeta_1008_; uint8_t v_isExported_1009_; uint8_t v_importAll_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_input_980_);
lean_dec_ref(v_p_979_);
v_imports_1006_ = lean_ctor_get(v_s_983_, 0);
v_isModule_1007_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 1);
v_isMeta_1008_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 2);
v_isExported_1009_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 3);
v_importAll_1010_ = lean_ctor_get_uint8(v_s_983_, sizeof(void*)*3 + 4);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_s_983_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; 
v_unused_1020_ = lean_ctor_get(v_s_983_, 2);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_s_983_, 1);
lean_dec(v_unused_1021_);
v___x_1012_ = v_s_983_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_imports_1006_);
lean_dec(v_s_983_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = 0;
v___x_1015_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v___x_1015_);
lean_ctor_set(v___x_1012_, 1, v_pos_982_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_imports_1006_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_pos_982_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v___x_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 1, v_isModule_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 2, v_isMeta_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 3, v_isExported_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 4, v_importAll_1010_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*3, v___x_1014_);
return v___x_1017_;
}
}
}
}
}
}
lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1022_, lean_object* v_s_1023_){
_start:
{
if (v_isModule_1022_ == 0)
{
lean_object* v_imports_1024_; lean_object* v_pos_1025_; uint8_t v_badModifier_1026_; lean_object* v_error_x3f_1027_; uint8_t v_isMeta_1028_; uint8_t v_importAll_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_imports_1024_ = lean_ctor_get(v_s_1023_, 0);
v_pos_1025_ = lean_ctor_get(v_s_1023_, 1);
v_badModifier_1026_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3);
v_error_x3f_1027_ = lean_ctor_get(v_s_1023_, 2);
v_isMeta_1028_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3 + 2);
v_importAll_1029_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3 + 4);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_s_1023_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1031_ = v_s_1023_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_error_x3f_1027_);
lean_inc(v_pos_1025_);
lean_inc(v_imports_1024_);
lean_dec(v_s_1023_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
uint8_t v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = 1;
if (v_isShared_1032_ == 0)
{
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_imports_1024_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_pos_1025_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_error_x3f_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3, v_badModifier_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 2, v_isMeta_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3 + 4, v_importAll_1029_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*3 + 1, v_isModule_1022_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*3 + 3, v___x_1033_);
return v___x_1035_;
}
}
}
else
{
lean_object* v_imports_1038_; lean_object* v_pos_1039_; uint8_t v_badModifier_1040_; lean_object* v_error_x3f_1041_; uint8_t v_isMeta_1042_; uint8_t v_importAll_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_imports_1038_ = lean_ctor_get(v_s_1023_, 0);
v_pos_1039_ = lean_ctor_get(v_s_1023_, 1);
v_badModifier_1040_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3);
v_error_x3f_1041_ = lean_ctor_get(v_s_1023_, 2);
v_isMeta_1042_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3 + 2);
v_importAll_1043_ = lean_ctor_get_uint8(v_s_1023_, sizeof(void*)*3 + 4);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1023_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1045_ = v_s_1023_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_error_x3f_1041_);
lean_inc(v_pos_1039_);
lean_inc(v_imports_1038_);
lean_dec(v_s_1023_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
uint8_t v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = 0;
if (v_isShared_1046_ == 0)
{
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_imports_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_pos_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_error_x3f_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3, v_badModifier_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 2, v_isMeta_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 4, v_importAll_1043_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*3 + 1, v_isModule_1022_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*3 + 3, v___x_1047_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ParseImports_setIsModule___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_isModule_1022_ = stack[0].m_num;
lean_object* v_s_1023_ = stack[1].m_obj;
lean_object* v_res_1052_;
v_res_1052_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1022_, v_s_1023_);
stack->m_obj
 = v_res_1052_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* v_isModule_1053_, lean_object* v_s_1054_){
_start:
{
uint8_t v_isModule_boxed_1055_; lean_object* v_res_1056_; 
v_isModule_boxed_1055_ = lean_unbox(v_isModule_1053_);
v_res_1056_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_1055_, v_s_1054_);
return v_res_1056_;
}
}
lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1057_, lean_object* v_x_1058_, lean_object* v_s_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1057_, v_s_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT void l_Lean_ParseImports_setIsModule_0interp(lean_interpreter_value* stack)
{
uint8_t v_isModule_1057_ = stack[0].m_num;
lean_object* v_x_1058_ = stack[1].m_obj;
lean_object* v_s_1059_ = stack[2].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l_Lean_ParseImports_setIsModule(v_isModule_1057_, v_x_1058_, v_s_1059_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1062_, lean_object* v_x_1063_, lean_object* v_s_1064_){
_start:
{
uint8_t v_isModule_boxed_1065_; lean_object* v_res_1066_; 
v_isModule_boxed_1065_ = lean_unbox(v_isModule_1062_);
v_res_1066_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1065_, v_x_1063_, v_s_1064_);
lean_dec_ref(v_x_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1067_){
_start:
{
lean_object* v_imports_1068_; lean_object* v_pos_1069_; uint8_t v_badModifier_1070_; lean_object* v_error_x3f_1071_; uint8_t v_isModule_1072_; uint8_t v_isMeta_1073_; uint8_t v_isExported_1074_; uint8_t v_importAll_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v_imports_1068_ = lean_ctor_get(v_s_1067_, 0);
v_pos_1069_ = lean_ctor_get(v_s_1067_, 1);
v_badModifier_1070_ = lean_ctor_get_uint8(v_s_1067_, sizeof(void*)*3);
v_error_x3f_1071_ = lean_ctor_get(v_s_1067_, 2);
v_isModule_1072_ = lean_ctor_get_uint8(v_s_1067_, sizeof(void*)*3 + 1);
v_isMeta_1073_ = lean_ctor_get_uint8(v_s_1067_, sizeof(void*)*3 + 2);
v_isExported_1074_ = lean_ctor_get_uint8(v_s_1067_, sizeof(void*)*3 + 3);
v_importAll_1075_ = lean_ctor_get_uint8(v_s_1067_, sizeof(void*)*3 + 4);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_s_1067_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v_s_1067_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_error_x3f_1071_);
lean_inc(v_pos_1069_);
lean_inc(v_imports_1068_);
lean_dec(v_s_1067_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint8_t v___x_1079_; 
v___x_1079_ = 1;
if (v_isModule_1072_ == 0)
{
lean_object* v___x_1081_; 
if (v_isShared_1078_ == 0)
{
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_imports_1068_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_pos_1069_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_error_x3f_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 1, v_isModule_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 2, v_isMeta_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 3, v_isExported_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 4, v_importAll_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3, v___x_1079_);
return v___x_1081_;
}
}
else
{
lean_object* v___x_1084_; 
if (v_isShared_1078_ == 0)
{
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_imports_1068_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_pos_1069_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_error_x3f_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3, v_badModifier_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3 + 1, v_isModule_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3 + 3, v_isExported_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3 + 4, v_importAll_1075_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*3 + 2, v___x_1079_);
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1087_, lean_object* v_s_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_ParseImports_setMeta___redArg(v_s_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1090_, lean_object* v_s_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_ParseImports_setMeta(v_x_1090_, v_s_1091_);
lean_dec_ref(v_x_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1093_){
_start:
{
lean_object* v_imports_1094_; lean_object* v_pos_1095_; uint8_t v_badModifier_1096_; lean_object* v_error_x3f_1097_; uint8_t v_isModule_1098_; uint8_t v_isMeta_1099_; uint8_t v_isExported_1100_; uint8_t v_importAll_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1112_; 
v_imports_1094_ = lean_ctor_get(v_s_1093_, 0);
v_pos_1095_ = lean_ctor_get(v_s_1093_, 1);
v_badModifier_1096_ = lean_ctor_get_uint8(v_s_1093_, sizeof(void*)*3);
v_error_x3f_1097_ = lean_ctor_get(v_s_1093_, 2);
v_isModule_1098_ = lean_ctor_get_uint8(v_s_1093_, sizeof(void*)*3 + 1);
v_isMeta_1099_ = lean_ctor_get_uint8(v_s_1093_, sizeof(void*)*3 + 2);
v_isExported_1100_ = lean_ctor_get_uint8(v_s_1093_, sizeof(void*)*3 + 3);
v_importAll_1101_ = lean_ctor_get_uint8(v_s_1093_, sizeof(void*)*3 + 4);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_s_1093_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1103_ = v_s_1093_;
v_isShared_1104_ = v_isSharedCheck_1112_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_error_x3f_1097_);
lean_inc(v_pos_1095_);
lean_inc(v_imports_1094_);
lean_dec(v_s_1093_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1112_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = 1;
if (v_isModule_1098_ == 0)
{
lean_object* v___x_1107_; 
if (v_isShared_1104_ == 0)
{
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_imports_1094_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_pos_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_error_x3f_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*3 + 1, v_isModule_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*3 + 2, v_isMeta_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*3 + 3, v_isExported_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*3 + 4, v_importAll_1101_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*3, v___x_1105_);
return v___x_1107_;
}
}
else
{
lean_object* v___x_1110_; 
if (v_isShared_1104_ == 0)
{
v___x_1110_ = v___x_1103_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_imports_1094_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_pos_1095_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_error_x3f_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*3, v_badModifier_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*3 + 1, v_isModule_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*3 + 2, v_isMeta_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*3 + 4, v_importAll_1101_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*3 + 3, v___x_1105_);
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1113_, lean_object* v_s_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_ParseImports_setExported___redArg(v_s_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1116_, lean_object* v_s_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_ParseImports_setExported(v_x_1116_, v_s_1117_);
lean_dec_ref(v_x_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1119_){
_start:
{
lean_object* v_imports_1120_; lean_object* v_pos_1121_; uint8_t v_badModifier_1122_; lean_object* v_error_x3f_1123_; uint8_t v_isModule_1124_; uint8_t v_isMeta_1125_; uint8_t v_isExported_1126_; uint8_t v_importAll_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1138_; 
v_imports_1120_ = lean_ctor_get(v_s_1119_, 0);
v_pos_1121_ = lean_ctor_get(v_s_1119_, 1);
v_badModifier_1122_ = lean_ctor_get_uint8(v_s_1119_, sizeof(void*)*3);
v_error_x3f_1123_ = lean_ctor_get(v_s_1119_, 2);
v_isModule_1124_ = lean_ctor_get_uint8(v_s_1119_, sizeof(void*)*3 + 1);
v_isMeta_1125_ = lean_ctor_get_uint8(v_s_1119_, sizeof(void*)*3 + 2);
v_isExported_1126_ = lean_ctor_get_uint8(v_s_1119_, sizeof(void*)*3 + 3);
v_importAll_1127_ = lean_ctor_get_uint8(v_s_1119_, sizeof(void*)*3 + 4);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_s_1119_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1129_ = v_s_1119_;
v_isShared_1130_ = v_isSharedCheck_1138_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_error_x3f_1123_);
lean_inc(v_pos_1121_);
lean_inc(v_imports_1120_);
lean_dec(v_s_1119_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1138_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = 1;
if (v_isModule_1124_ == 0)
{
lean_object* v___x_1133_; 
if (v_isShared_1130_ == 0)
{
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_imports_1120_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_pos_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_error_x3f_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3 + 1, v_isModule_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3 + 2, v_isMeta_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3 + 3, v_isExported_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3 + 4, v_importAll_1127_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*3, v___x_1131_);
return v___x_1133_;
}
}
else
{
lean_object* v___x_1136_; 
if (v_isShared_1130_ == 0)
{
v___x_1136_ = v___x_1129_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_imports_1120_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_pos_1121_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_error_x3f_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*3, v_badModifier_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*3 + 1, v_isModule_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*3 + 2, v_isMeta_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*3 + 3, v_isExported_1126_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 4, v___x_1131_);
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1139_, lean_object* v_s_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1142_, lean_object* v_s_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_ParseImports_setImportAll(v_x_1142_, v_s_1143_);
lean_dec_ref(v_x_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1148_, lean_object* v_input_1149_, lean_object* v_s_1150_, lean_object* v_i_1151_, lean_object* v_j_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_string_utf8_at_end(v_k_1148_, v_i_1151_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; lean_object* v_s_1156_; uint8_t v___x_1162_; 
v___x_1154_ = 1;
v___x_1162_ = lean_string_utf8_at_end(v_input_1149_, v_j_1152_);
if (v___x_1162_ == 0)
{
uint32_t v_curr_u2081_1163_; uint32_t v_curr_u2082_1164_; uint8_t v___x_1165_; 
v_curr_u2081_1163_ = lean_string_utf8_get_fast(v_k_1148_, v_i_1151_);
v_curr_u2082_1164_ = lean_string_utf8_get_fast(v_input_1149_, v_j_1152_);
v___x_1165_ = lean_uint32_dec_eq(v_curr_u2081_1163_, v_curr_u2082_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v_j_1152_);
lean_dec(v_i_1151_);
v_s_1156_ = v_s_1150_;
goto v___jp_1155_;
}
else
{
if (v___x_1162_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_string_utf8_next_fast(v_k_1148_, v_i_1151_);
lean_dec(v_i_1151_);
v___x_1167_ = lean_string_utf8_next_fast(v_input_1149_, v_j_1152_);
lean_dec(v_j_1152_);
v_i_1151_ = v___x_1166_;
v_j_1152_ = v___x_1167_;
goto _start;
}
else
{
lean_dec(v_j_1152_);
lean_dec(v_i_1151_);
v_s_1156_ = v_s_1150_;
goto v___jp_1155_;
}
}
}
else
{
lean_dec(v_j_1152_);
lean_dec(v_i_1151_);
v_s_1156_ = v_s_1150_;
goto v___jp_1155_;
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1157_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1158_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1, v___x_1153_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1 + 1, v___x_1154_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1 + 2, v___x_1154_);
v___x_1159_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1, v___x_1153_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1 + 1, v___x_1154_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1 + 2, v___x_1153_);
v___x_1160_ = l_Lean_ParseImports_State_pushImport(v___x_1159_, v_s_1156_);
v___x_1161_ = l_Lean_ParseImports_State_pushImport(v___x_1158_, v___x_1160_);
return v___x_1161_;
}
}
else
{
lean_object* v_imports_1169_; uint8_t v_badModifier_1170_; lean_object* v_error_x3f_1171_; uint8_t v_isModule_1172_; uint8_t v_isMeta_1173_; uint8_t v_isExported_1174_; uint8_t v_importAll_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_i_1151_);
v_imports_1169_ = lean_ctor_get(v_s_1150_, 0);
v_badModifier_1170_ = lean_ctor_get_uint8(v_s_1150_, sizeof(void*)*3);
v_error_x3f_1171_ = lean_ctor_get(v_s_1150_, 2);
v_isModule_1172_ = lean_ctor_get_uint8(v_s_1150_, sizeof(void*)*3 + 1);
v_isMeta_1173_ = lean_ctor_get_uint8(v_s_1150_, sizeof(void*)*3 + 2);
v_isExported_1174_ = lean_ctor_get_uint8(v_s_1150_, sizeof(void*)*3 + 3);
v_importAll_1175_ = lean_ctor_get_uint8(v_s_1150_, sizeof(void*)*3 + 4);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_s_1150_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_s_1150_, 1);
lean_dec(v_unused_1184_);
v___x_1177_ = v_s_1150_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_error_x3f_1171_);
lean_inc(v_imports_1169_);
lean_dec(v_s_1150_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_j_1152_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_imports_1169_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_j_1152_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_error_x3f_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3, v_badModifier_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3 + 1, v_isModule_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3 + 2, v_isMeta_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3 + 3, v_isExported_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3 + 4, v_importAll_1175_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_ParseImports_whitespace(v_input_1149_, v___x_1180_);
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1185_, lean_object* v_input_1186_, lean_object* v_s_1187_, lean_object* v_i_1188_, lean_object* v_j_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1185_, v_input_1186_, v_s_1187_, v_i_1188_, v_j_1189_);
lean_dec_ref(v_input_1186_);
lean_dec_ref(v_k_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1194_, lean_object* v_input_1195_, lean_object* v_s_1196_, lean_object* v_i_1197_, lean_object* v_j_1198_){
_start:
{
lean_object* v_s_1200_; uint8_t v___x_1217_; 
v___x_1217_ = lean_string_utf8_at_end(v_k_1194_, v_i_1197_);
if (v___x_1217_ == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_string_utf8_at_end(v_input_1195_, v_j_1198_);
if (v___x_1218_ == 0)
{
uint32_t v_curr_u2081_1219_; uint32_t v_curr_u2082_1220_; uint8_t v___x_1221_; 
v_curr_u2081_1219_ = lean_string_utf8_get_fast(v_k_1194_, v_i_1197_);
v_curr_u2082_1220_ = lean_string_utf8_get_fast(v_input_1195_, v_j_1198_);
v___x_1221_ = lean_uint32_dec_eq(v_curr_u2081_1219_, v_curr_u2082_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v_j_1198_);
lean_dec(v_i_1197_);
v_s_1200_ = v_s_1196_;
goto v___jp_1199_;
}
else
{
if (v___x_1218_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_string_utf8_next_fast(v_k_1194_, v_i_1197_);
lean_dec(v_i_1197_);
v___x_1223_ = lean_string_utf8_next_fast(v_input_1195_, v_j_1198_);
lean_dec(v_j_1198_);
v_i_1197_ = v___x_1222_;
v_j_1198_ = v___x_1223_;
goto _start;
}
else
{
lean_dec(v_j_1198_);
lean_dec(v_i_1197_);
v_s_1200_ = v_s_1196_;
goto v___jp_1199_;
}
}
}
else
{
lean_dec(v_j_1198_);
lean_dec(v_i_1197_);
v_s_1200_ = v_s_1196_;
goto v___jp_1199_;
}
}
else
{
lean_object* v_imports_1225_; uint8_t v_badModifier_1226_; lean_object* v_error_x3f_1227_; uint8_t v_isModule_1228_; uint8_t v_isMeta_1229_; uint8_t v_isExported_1230_; uint8_t v_importAll_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_i_1197_);
v_imports_1225_ = lean_ctor_get(v_s_1196_, 0);
v_badModifier_1226_ = lean_ctor_get_uint8(v_s_1196_, sizeof(void*)*3);
v_error_x3f_1227_ = lean_ctor_get(v_s_1196_, 2);
v_isModule_1228_ = lean_ctor_get_uint8(v_s_1196_, sizeof(void*)*3 + 1);
v_isMeta_1229_ = lean_ctor_get_uint8(v_s_1196_, sizeof(void*)*3 + 2);
v_isExported_1230_ = lean_ctor_get_uint8(v_s_1196_, sizeof(void*)*3 + 3);
v_importAll_1231_ = lean_ctor_get_uint8(v_s_1196_, sizeof(void*)*3 + 4);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_s_1196_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_s_1196_, 1);
lean_dec(v_unused_1240_);
v___x_1233_ = v_s_1196_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_error_x3f_1227_);
lean_inc(v_imports_1225_);
lean_dec(v_s_1196_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_j_1198_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_imports_1225_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_j_1198_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_error_x3f_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3, v_badModifier_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 1, v_isModule_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 2, v_isMeta_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 3, v_isExported_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 4, v_importAll_1231_);
v___x_1236_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_ParseImports_whitespace(v_input_1195_, v___x_1236_);
return v___x_1237_;
}
}
}
v___jp_1199_:
{
lean_object* v_imports_1201_; lean_object* v_pos_1202_; uint8_t v_badModifier_1203_; uint8_t v_isModule_1204_; uint8_t v_isMeta_1205_; uint8_t v_isExported_1206_; uint8_t v_importAll_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_imports_1201_ = lean_ctor_get(v_s_1200_, 0);
v_pos_1202_ = lean_ctor_get(v_s_1200_, 1);
v_badModifier_1203_ = lean_ctor_get_uint8(v_s_1200_, sizeof(void*)*3);
v_isModule_1204_ = lean_ctor_get_uint8(v_s_1200_, sizeof(void*)*3 + 1);
v_isMeta_1205_ = lean_ctor_get_uint8(v_s_1200_, sizeof(void*)*3 + 2);
v_isExported_1206_ = lean_ctor_get_uint8(v_s_1200_, sizeof(void*)*3 + 3);
v_importAll_1207_ = lean_ctor_get_uint8(v_s_1200_, sizeof(void*)*3 + 4);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_s_1200_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_s_1200_, 2);
lean_dec(v_unused_1216_);
v___x_1209_ = v_s_1200_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_pos_1202_);
lean_inc(v_imports_1201_);
lean_dec(v_s_1200_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 2, v___x_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_imports_1201_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_pos_1202_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___x_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3, v_badModifier_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 1, v_isModule_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 2, v_isMeta_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 3, v_isExported_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 4, v_importAll_1207_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1241_, lean_object* v_input_1242_, lean_object* v_s_1243_, lean_object* v_i_1244_, lean_object* v_j_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1241_, v_input_1242_, v_s_1243_, v_i_1244_, v_j_1245_);
lean_dec_ref(v_input_1242_);
lean_dec_ref(v_k_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1247_, lean_object* v_input_1248_, lean_object* v_s_1249_, lean_object* v_i_1250_, lean_object* v_j_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_string_utf8_at_end(v_k_1247_, v_i_1250_);
if (v___x_1252_ == 0)
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_string_utf8_at_end(v_input_1248_, v_j_1251_);
if (v___x_1253_ == 0)
{
uint32_t v_curr_u2081_1254_; uint32_t v_curr_u2082_1255_; uint8_t v___x_1256_; 
v_curr_u2081_1254_ = lean_string_utf8_get_fast(v_k_1247_, v_i_1250_);
v_curr_u2082_1255_ = lean_string_utf8_get_fast(v_input_1248_, v_j_1251_);
v___x_1256_ = lean_uint32_dec_eq(v_curr_u2081_1254_, v_curr_u2082_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_j_1251_);
lean_dec(v_i_1250_);
return v_s_1249_;
}
else
{
if (v___x_1253_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_string_utf8_next_fast(v_k_1247_, v_i_1250_);
lean_dec(v_i_1250_);
v___x_1258_ = lean_string_utf8_next_fast(v_input_1248_, v_j_1251_);
lean_dec(v_j_1251_);
v_i_1250_ = v___x_1257_;
v_j_1251_ = v___x_1258_;
goto _start;
}
else
{
lean_dec(v_j_1251_);
lean_dec(v_i_1250_);
return v_s_1249_;
}
}
}
else
{
lean_dec(v_j_1251_);
lean_dec(v_i_1250_);
return v_s_1249_;
}
}
else
{
lean_object* v_imports_1260_; uint8_t v_badModifier_1261_; lean_object* v_error_x3f_1262_; uint8_t v_isModule_1263_; uint8_t v_isMeta_1264_; uint8_t v_isExported_1265_; uint8_t v_importAll_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_i_1250_);
v_imports_1260_ = lean_ctor_get(v_s_1249_, 0);
v_badModifier_1261_ = lean_ctor_get_uint8(v_s_1249_, sizeof(void*)*3);
v_error_x3f_1262_ = lean_ctor_get(v_s_1249_, 2);
v_isModule_1263_ = lean_ctor_get_uint8(v_s_1249_, sizeof(void*)*3 + 1);
v_isMeta_1264_ = lean_ctor_get_uint8(v_s_1249_, sizeof(void*)*3 + 2);
v_isExported_1265_ = lean_ctor_get_uint8(v_s_1249_, sizeof(void*)*3 + 3);
v_importAll_1266_ = lean_ctor_get_uint8(v_s_1249_, sizeof(void*)*3 + 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_s_1249_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_s_1249_, 1);
lean_dec(v_unused_1276_);
v___x_1268_ = v_s_1249_;
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_error_x3f_1262_);
lean_inc(v_imports_1260_);
lean_dec(v_s_1249_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_j_1251_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_imports_1260_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_j_1251_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_error_x3f_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3, v_badModifier_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 1, v_isModule_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 2, v_isMeta_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 3, v_isExported_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 4, v_importAll_1266_);
v___x_1271_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_Lean_ParseImports_whitespace(v_input_1248_, v___x_1271_);
v___x_1273_ = l_Lean_ParseImports_setImportAll___redArg(v___x_1272_);
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* v_k_1277_, lean_object* v_input_1278_, lean_object* v_s_1279_, lean_object* v_i_1280_, lean_object* v_j_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_1277_, v_input_1278_, v_s_1279_, v_i_1280_, v_j_1281_);
lean_dec_ref(v_input_1278_);
lean_dec_ref(v_k_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* v_k_1283_, lean_object* v_input_1284_, lean_object* v_s_1285_, lean_object* v_i_1286_, lean_object* v_j_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_string_utf8_at_end(v_k_1283_, v_i_1286_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_string_utf8_at_end(v_input_1284_, v_j_1287_);
if (v___x_1289_ == 0)
{
uint32_t v_curr_u2081_1290_; uint32_t v_curr_u2082_1291_; uint8_t v___x_1292_; 
v_curr_u2081_1290_ = lean_string_utf8_get_fast(v_k_1283_, v_i_1286_);
v_curr_u2082_1291_ = lean_string_utf8_get_fast(v_input_1284_, v_j_1287_);
v___x_1292_ = lean_uint32_dec_eq(v_curr_u2081_1290_, v_curr_u2082_1291_);
if (v___x_1292_ == 0)
{
lean_dec(v_j_1287_);
lean_dec(v_i_1286_);
return v_s_1285_;
}
else
{
if (v___x_1289_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_string_utf8_next_fast(v_k_1283_, v_i_1286_);
lean_dec(v_i_1286_);
v___x_1294_ = lean_string_utf8_next_fast(v_input_1284_, v_j_1287_);
lean_dec(v_j_1287_);
v_i_1286_ = v___x_1293_;
v_j_1287_ = v___x_1294_;
goto _start;
}
else
{
lean_dec(v_j_1287_);
lean_dec(v_i_1286_);
return v_s_1285_;
}
}
}
else
{
lean_dec(v_j_1287_);
lean_dec(v_i_1286_);
return v_s_1285_;
}
}
else
{
lean_object* v_imports_1296_; uint8_t v_badModifier_1297_; lean_object* v_error_x3f_1298_; uint8_t v_isModule_1299_; uint8_t v_isMeta_1300_; uint8_t v_isExported_1301_; uint8_t v_importAll_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_i_1286_);
v_imports_1296_ = lean_ctor_get(v_s_1285_, 0);
v_badModifier_1297_ = lean_ctor_get_uint8(v_s_1285_, sizeof(void*)*3);
v_error_x3f_1298_ = lean_ctor_get(v_s_1285_, 2);
v_isModule_1299_ = lean_ctor_get_uint8(v_s_1285_, sizeof(void*)*3 + 1);
v_isMeta_1300_ = lean_ctor_get_uint8(v_s_1285_, sizeof(void*)*3 + 2);
v_isExported_1301_ = lean_ctor_get_uint8(v_s_1285_, sizeof(void*)*3 + 3);
v_importAll_1302_ = lean_ctor_get_uint8(v_s_1285_, sizeof(void*)*3 + 4);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_s_1285_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_s_1285_, 1);
lean_dec(v_unused_1312_);
v___x_1304_ = v_s_1285_;
v_isShared_1305_ = v_isSharedCheck_1311_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_error_x3f_1298_);
lean_inc(v_imports_1296_);
lean_dec(v_s_1285_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1311_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v_j_1287_);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_imports_1296_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_j_1287_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_error_x3f_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*3, v_badModifier_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*3 + 1, v_isModule_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*3 + 2, v_isMeta_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*3 + 3, v_isExported_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1310_, sizeof(void*)*3 + 4, v_importAll_1302_);
v___x_1307_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l_Lean_ParseImports_whitespace(v_input_1284_, v___x_1307_);
v___x_1309_ = l_Lean_ParseImports_setExported___redArg(v___x_1308_);
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1313_, lean_object* v_input_1314_, lean_object* v_s_1315_, lean_object* v_i_1316_, lean_object* v_j_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1313_, v_input_1314_, v_s_1315_, v_i_1316_, v_j_1317_);
lean_dec_ref(v_input_1314_);
lean_dec_ref(v_k_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1319_, lean_object* v_input_1320_, lean_object* v_s_1321_, lean_object* v_i_1322_, lean_object* v_j_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_string_utf8_at_end(v_k_1319_, v_i_1322_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_string_utf8_at_end(v_input_1320_, v_j_1323_);
if (v___x_1325_ == 0)
{
uint32_t v_curr_u2081_1326_; uint32_t v_curr_u2082_1327_; uint8_t v___x_1328_; 
v_curr_u2081_1326_ = lean_string_utf8_get_fast(v_k_1319_, v_i_1322_);
v_curr_u2082_1327_ = lean_string_utf8_get_fast(v_input_1320_, v_j_1323_);
v___x_1328_ = lean_uint32_dec_eq(v_curr_u2081_1326_, v_curr_u2082_1327_);
if (v___x_1328_ == 0)
{
lean_dec(v_j_1323_);
lean_dec(v_i_1322_);
return v_s_1321_;
}
else
{
if (v___x_1325_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_string_utf8_next_fast(v_k_1319_, v_i_1322_);
lean_dec(v_i_1322_);
v___x_1330_ = lean_string_utf8_next_fast(v_input_1320_, v_j_1323_);
lean_dec(v_j_1323_);
v_i_1322_ = v___x_1329_;
v_j_1323_ = v___x_1330_;
goto _start;
}
else
{
lean_dec(v_j_1323_);
lean_dec(v_i_1322_);
return v_s_1321_;
}
}
}
else
{
lean_dec(v_j_1323_);
lean_dec(v_i_1322_);
return v_s_1321_;
}
}
else
{
lean_object* v_imports_1332_; uint8_t v_badModifier_1333_; lean_object* v_error_x3f_1334_; uint8_t v_isModule_1335_; uint8_t v_isMeta_1336_; uint8_t v_isExported_1337_; uint8_t v_importAll_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v_i_1322_);
v_imports_1332_ = lean_ctor_get(v_s_1321_, 0);
v_badModifier_1333_ = lean_ctor_get_uint8(v_s_1321_, sizeof(void*)*3);
v_error_x3f_1334_ = lean_ctor_get(v_s_1321_, 2);
v_isModule_1335_ = lean_ctor_get_uint8(v_s_1321_, sizeof(void*)*3 + 1);
v_isMeta_1336_ = lean_ctor_get_uint8(v_s_1321_, sizeof(void*)*3 + 2);
v_isExported_1337_ = lean_ctor_get_uint8(v_s_1321_, sizeof(void*)*3 + 3);
v_importAll_1338_ = lean_ctor_get_uint8(v_s_1321_, sizeof(void*)*3 + 4);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_s_1321_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_s_1321_, 1);
lean_dec(v_unused_1348_);
v___x_1340_ = v_s_1321_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_error_x3f_1334_);
lean_inc(v_imports_1332_);
lean_dec(v_s_1321_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v_j_1323_);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_imports_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_j_1323_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_error_x3f_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3, v_badModifier_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 1, v_isModule_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 2, v_isMeta_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 3, v_isExported_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 4, v_importAll_1338_);
v___x_1343_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_ParseImports_whitespace(v_input_1320_, v___x_1343_);
v___x_1345_ = l_Lean_ParseImports_setMeta___redArg(v___x_1344_);
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1349_, lean_object* v_input_1350_, lean_object* v_s_1351_, lean_object* v_i_1352_, lean_object* v_j_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1349_, v_input_1350_, v_s_1351_, v_i_1352_, v_j_1353_);
lean_dec_ref(v_input_1350_);
lean_dec_ref(v_k_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1359_, lean_object* v_s_1360_){
_start:
{
lean_object* v_pos_1361_; lean_object* v___y_1363_; lean_object* v_imports_1364_; lean_object* v_pos_1365_; uint8_t v_isModule_1366_; uint8_t v_isMeta_1367_; uint8_t v_isExported_1368_; uint8_t v_importAll_1369_; lean_object* v___y_1375_; lean_object* v___y_1402_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_error_x3f_1434_; 
v_pos_1361_ = lean_ctor_get(v_s_1360_, 1);
lean_inc_n(v_pos_1361_, 2);
v___x_1431_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1431_, v_input_1359_, v_s_1360_, v___x_1432_, v_pos_1361_);
v_error_x3f_1434_ = lean_ctor_get(v___x_1433_, 2);
if (lean_obj_tag(v_error_x3f_1434_) == 1)
{
v___y_1402_ = v___x_1433_;
goto v___jp_1401_;
}
else
{
lean_object* v_pos_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_error_x3f_1438_; 
v_pos_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_pos_1435_);
v___x_1436_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1437_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1436_, v_input_1359_, v___x_1433_, v___x_1432_, v_pos_1435_);
v_error_x3f_1438_ = lean_ctor_get(v___x_1437_, 2);
if (lean_obj_tag(v_error_x3f_1438_) == 1)
{
v___y_1402_ = v___x_1437_;
goto v___jp_1401_;
}
else
{
lean_object* v_pos_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_pos_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_pos_1439_);
v___x_1440_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1441_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1440_, v_input_1359_, v___x_1437_, v___x_1432_, v_pos_1439_);
v___y_1402_ = v___x_1441_;
goto v___jp_1401_;
}
}
v___jp_1362_:
{
uint8_t v_decide_1370_; 
v_decide_1370_ = lean_nat_dec_eq(v_pos_1365_, v_pos_1361_);
lean_dec(v_pos_1361_);
if (v_decide_1370_ == 0)
{
lean_dec(v_pos_1365_);
lean_dec_ref(v_imports_1364_);
return v___y_1363_;
}
else
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v___y_1363_);
v___x_1371_ = 0;
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1373_, 0, v_imports_1364_);
lean_ctor_set(v___x_1373_, 1, v_pos_1365_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 1, v_isModule_1366_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 2, v_isMeta_1367_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 3, v_isExported_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 4, v_importAll_1369_);
return v___x_1373_;
}
}
v___jp_1374_:
{
lean_object* v_error_x3f_1376_; 
v_error_x3f_1376_ = lean_ctor_get(v___y_1375_, 2);
if (lean_obj_tag(v_error_x3f_1376_) == 1)
{
lean_object* v_imports_1377_; lean_object* v_pos_1378_; uint8_t v_isModule_1379_; uint8_t v_isMeta_1380_; uint8_t v_isExported_1381_; uint8_t v_importAll_1382_; 
lean_dec_ref(v_input_1359_);
v_imports_1377_ = lean_ctor_get(v___y_1375_, 0);
lean_inc_ref(v_imports_1377_);
v_pos_1378_ = lean_ctor_get(v___y_1375_, 1);
lean_inc(v_pos_1378_);
v_isModule_1379_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 1);
v_isMeta_1380_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 2);
v_isExported_1381_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 3);
v_importAll_1382_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 4);
v___y_1363_ = v___y_1375_;
v_imports_1364_ = v_imports_1377_;
v_pos_1365_ = v_pos_1378_;
v_isModule_1366_ = v_isModule_1379_;
v_isMeta_1367_ = v_isMeta_1380_;
v_isExported_1368_ = v_isExported_1381_;
v_importAll_1369_ = v_importAll_1382_;
goto v___jp_1362_;
}
else
{
uint8_t v_badModifier_1383_; 
v_badModifier_1383_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3);
if (v_badModifier_1383_ == 0)
{
lean_dec(v_pos_1361_);
v_s_1360_ = v___y_1375_;
goto _start;
}
else
{
lean_object* v_imports_1385_; uint8_t v_isModule_1386_; uint8_t v_isMeta_1387_; uint8_t v_isExported_1388_; uint8_t v_importAll_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v_input_1359_);
v_imports_1385_ = lean_ctor_get(v___y_1375_, 0);
v_isModule_1386_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 1);
v_isMeta_1387_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 2);
v_isExported_1388_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 3);
v_importAll_1389_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*3 + 4);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___y_1375_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v___y_1375_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v___y_1375_, 1);
lean_dec(v_unused_1400_);
v___x_1391_ = v___y_1375_;
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_imports_1385_);
lean_dec(v___y_1375_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = 0;
v___x_1394_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 2, v___x_1394_);
lean_ctor_set(v___x_1391_, 1, v_pos_1361_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_imports_1385_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_pos_1361_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v___x_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*3 + 1, v_isModule_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*3 + 2, v_isMeta_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*3 + 3, v_isExported_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*3 + 4, v_importAll_1389_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3, v___x_1393_);
return v___x_1396_;
}
}
}
}
}
v___jp_1401_:
{
lean_object* v_error_x3f_1403_; 
v_error_x3f_1403_ = lean_ctor_get(v___y_1402_, 2);
if (lean_obj_tag(v_error_x3f_1403_) == 1)
{
lean_object* v_imports_1404_; uint8_t v_badModifier_1405_; uint8_t v_isModule_1406_; uint8_t v_isMeta_1407_; uint8_t v_isExported_1408_; uint8_t v_importAll_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_inc_ref(v_error_x3f_1403_);
lean_dec_ref(v_input_1359_);
v_imports_1404_ = lean_ctor_get(v___y_1402_, 0);
v_badModifier_1405_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3);
v_isModule_1406_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 1);
v_isMeta_1407_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 2);
v_isExported_1408_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 3);
v_importAll_1409_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 4);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___y_1402_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1417_ = lean_ctor_get(v___y_1402_, 2);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v___y_1402_, 1);
lean_dec(v_unused_1418_);
v___x_1411_ = v___y_1402_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_imports_1404_);
lean_dec(v___y_1402_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
lean_inc(v_pos_1361_);
lean_inc_ref(v_imports_1404_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v_pos_1361_);
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_imports_1404_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_pos_1361_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_error_x3f_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3, v_badModifier_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3 + 1, v_isModule_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3 + 2, v_isMeta_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3 + 3, v_isExported_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*3 + 4, v_importAll_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_inc(v_pos_1361_);
v___y_1363_ = v___x_1414_;
v_imports_1364_ = v_imports_1404_;
v_pos_1365_ = v_pos_1361_;
v_isModule_1366_ = v_isModule_1406_;
v_isMeta_1367_ = v_isMeta_1407_;
v_isExported_1368_ = v_isExported_1408_;
v_importAll_1369_ = v_importAll_1409_;
goto v___jp_1362_;
}
}
}
else
{
if (lean_obj_tag(v_error_x3f_1403_) == 1)
{
lean_object* v_imports_1419_; lean_object* v_pos_1420_; uint8_t v_isModule_1421_; uint8_t v_isMeta_1422_; uint8_t v_isExported_1423_; uint8_t v_importAll_1424_; 
lean_dec_ref(v_input_1359_);
v_imports_1419_ = lean_ctor_get(v___y_1402_, 0);
lean_inc_ref(v_imports_1419_);
v_pos_1420_ = lean_ctor_get(v___y_1402_, 1);
lean_inc(v_pos_1420_);
v_isModule_1421_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 1);
v_isMeta_1422_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 2);
v_isExported_1423_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 3);
v_importAll_1424_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*3 + 4);
v___y_1363_ = v___y_1402_;
v_imports_1364_ = v_imports_1419_;
v_pos_1365_ = v_pos_1420_;
v_isModule_1366_ = v_isModule_1421_;
v_isMeta_1367_ = v_isMeta_1422_;
v_isExported_1368_ = v_isExported_1423_;
v_importAll_1369_ = v_importAll_1424_;
goto v___jp_1362_;
}
else
{
lean_object* v_pos_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_error_x3f_1429_; 
v_pos_1425_ = lean_ctor_get(v___y_1402_, 1);
lean_inc(v_pos_1425_);
v___x_1426_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1426_, v_input_1359_, v___y_1402_, v___x_1427_, v_pos_1425_);
v_error_x3f_1429_ = lean_ctor_get(v___x_1428_, 2);
if (lean_obj_tag(v_error_x3f_1429_) == 1)
{
v___y_1375_ = v___x_1428_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1430_; 
lean_inc_ref(v_input_1359_);
v___x_1430_ = l_Lean_ParseImports_moduleIdent(v_input_1359_, v___x_1428_);
v___y_1375_ = v___x_1430_;
goto v___jp_1374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1442_, lean_object* v_input_1443_, lean_object* v_s_1444_, lean_object* v_i_1445_, lean_object* v_j_1446_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_string_utf8_at_end(v_k_1442_, v_i_1445_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_string_utf8_at_end(v_input_1443_, v_j_1446_);
if (v___x_1448_ == 0)
{
uint32_t v_curr_u2081_1449_; uint32_t v_curr_u2082_1450_; uint8_t v___x_1451_; 
v_curr_u2081_1449_ = lean_string_utf8_get_fast(v_k_1442_, v_i_1445_);
v_curr_u2082_1450_ = lean_string_utf8_get_fast(v_input_1443_, v_j_1446_);
v___x_1451_ = lean_uint32_dec_eq(v_curr_u2081_1449_, v_curr_u2082_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_j_1446_);
lean_dec(v_i_1445_);
v___x_1452_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1447_, v_s_1444_);
return v___x_1452_;
}
else
{
if (v___x_1448_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_string_utf8_next_fast(v_k_1442_, v_i_1445_);
lean_dec(v_i_1445_);
v___x_1454_ = lean_string_utf8_next_fast(v_input_1443_, v_j_1446_);
lean_dec(v_j_1446_);
v_i_1445_ = v___x_1453_;
v_j_1446_ = v___x_1454_;
goto _start;
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_j_1446_);
lean_dec(v_i_1445_);
v___x_1456_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1447_, v_s_1444_);
return v___x_1456_;
}
}
}
else
{
lean_object* v___x_1457_; 
lean_dec(v_j_1446_);
lean_dec(v_i_1445_);
v___x_1457_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1447_, v_s_1444_);
return v___x_1457_;
}
}
else
{
lean_object* v_imports_1458_; uint8_t v_badModifier_1459_; lean_object* v_error_x3f_1460_; uint8_t v_isModule_1461_; uint8_t v_isMeta_1462_; uint8_t v_isExported_1463_; uint8_t v_importAll_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_i_1445_);
v_imports_1458_ = lean_ctor_get(v_s_1444_, 0);
v_badModifier_1459_ = lean_ctor_get_uint8(v_s_1444_, sizeof(void*)*3);
v_error_x3f_1460_ = lean_ctor_get(v_s_1444_, 2);
v_isModule_1461_ = lean_ctor_get_uint8(v_s_1444_, sizeof(void*)*3 + 1);
v_isMeta_1462_ = lean_ctor_get_uint8(v_s_1444_, sizeof(void*)*3 + 2);
v_isExported_1463_ = lean_ctor_get_uint8(v_s_1444_, sizeof(void*)*3 + 3);
v_importAll_1464_ = lean_ctor_get_uint8(v_s_1444_, sizeof(void*)*3 + 4);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_s_1444_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v_s_1444_, 1);
lean_dec(v_unused_1474_);
v___x_1466_ = v_s_1444_;
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_error_x3f_1460_);
lean_inc(v_imports_1458_);
lean_dec(v_s_1444_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v_j_1446_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_imports_1458_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_j_1446_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_error_x3f_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*3, v_badModifier_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*3 + 1, v_isModule_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*3 + 2, v_isMeta_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*3 + 3, v_isExported_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*3 + 4, v_importAll_1464_);
v___x_1469_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = l_Lean_ParseImports_whitespace(v_input_1443_, v___x_1469_);
v___x_1471_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1447_, v___x_1470_);
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1475_, lean_object* v_input_1476_, lean_object* v_s_1477_, lean_object* v_i_1478_, lean_object* v_j_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1475_, v_input_1476_, v_s_1477_, v_i_1478_, v_j_1479_);
lean_dec_ref(v_input_1476_);
lean_dec_ref(v_k_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_pos_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_s_1488_; lean_object* v_error_x3f_1489_; 
v_pos_1485_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_pos_1485_);
v___x_1486_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1487_ = lean_unsigned_to_nat(0u);
v_s_1488_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1486_, v_a_1483_, v_a_1484_, v___x_1487_, v_pos_1485_);
v_error_x3f_1489_ = lean_ctor_get(v_s_1488_, 2);
if (lean_obj_tag(v_error_x3f_1489_) == 1)
{
lean_dec_ref(v_a_1483_);
return v_s_1488_;
}
else
{
lean_object* v_pos_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v_error_x3f_1493_; 
v_pos_1490_ = lean_ctor_get(v_s_1488_, 1);
lean_inc(v_pos_1490_);
v___x_1491_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1492_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1491_, v_a_1483_, v_s_1488_, v___x_1487_, v_pos_1490_);
v_error_x3f_1493_ = lean_ctor_get(v___x_1492_, 2);
if (lean_obj_tag(v_error_x3f_1493_) == 1)
{
lean_dec_ref(v_a_1483_);
return v___x_1492_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1483_, v___x_1492_);
return v___x_1494_;
}
}
}
}
lean_object* l_Lean_parseImports_x27(lean_object* v_input_1497_, lean_object* v_fileName_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_s_1502_; lean_object* v_error_x3f_1503_; 
v___x_1500_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1501_ = l_Lean_ParseImports_whitespace(v_input_1497_, v___x_1500_);
lean_inc_ref(v_input_1497_);
v_s_1502_ = l_Lean_ParseImports_main(v_input_1497_, v___x_1501_);
v_error_x3f_1503_ = lean_ctor_get(v_s_1502_, 2);
lean_inc(v_error_x3f_1503_);
if (lean_obj_tag(v_error_x3f_1503_) == 1)
{
lean_object* v_pos_1504_; lean_object* v_val_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1527_; 
v_pos_1504_ = lean_ctor_get(v_s_1502_, 1);
lean_inc(v_pos_1504_);
lean_dec_ref(v_s_1502_);
v_val_1505_ = lean_ctor_get(v_error_x3f_1503_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_error_x3f_1503_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1507_ = v_error_x3f_1503_;
v_isShared_1508_ = v_isSharedCheck_1527_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_val_1505_);
lean_dec(v_error_x3f_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1527_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_fileMap_1509_; lean_object* v_pos_1510_; lean_object* v_line_1511_; lean_object* v_column_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v_fileMap_1509_ = l_Lean_String_toFileMap(v_input_1497_);
v_pos_1510_ = l_Lean_FileMap_toPosition(v_fileMap_1509_, v_pos_1504_);
lean_dec(v_pos_1504_);
v_line_1511_ = lean_ctor_get(v_pos_1510_, 0);
lean_inc(v_line_1511_);
v_column_1512_ = lean_ctor_get(v_pos_1510_, 1);
lean_inc(v_column_1512_);
lean_dec_ref(v_pos_1510_);
v___x_1513_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1514_ = lean_string_append(v_fileName_1498_, v___x_1513_);
v___x_1515_ = l_Nat_reprFast(v_line_1511_);
v___x_1516_ = lean_string_append(v___x_1514_, v___x_1515_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = lean_string_append(v___x_1516_, v___x_1513_);
v___x_1518_ = l_Nat_reprFast(v_column_1512_);
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
v___x_1522_ = lean_string_append(v___x_1521_, v_val_1505_);
lean_dec(v_val_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set_tag(v___x_1507_, 18);
lean_ctor_set(v___x_1507_, 0, v___x_1522_);
v___x_1524_ = v___x_1507_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
}
else
{
lean_object* v_imports_1528_; uint8_t v_isModule_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_error_x3f_1503_);
lean_dec_ref(v_fileName_1498_);
lean_dec_ref(v_input_1497_);
v_imports_1528_ = lean_ctor_get(v_s_1502_, 0);
lean_inc_ref(v_imports_1528_);
v_isModule_1529_ = lean_ctor_get_uint8(v_s_1502_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1502_);
v___x_1530_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1530_, 0, v_imports_1528_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*1, v_isModule_1529_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
}
LEAN_EXPORT void l_Lean_parseImports_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1497_ = stack[0].m_obj;
lean_object* v_fileName_1498_ = stack[1].m_obj;
lean_object* v_res_1532_;
v_res_1532_ = l_Lean_parseImports_x27(v_input_1497_, v_fileName_1498_);
stack->m_obj
 = v_res_1532_;
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1533_, lean_object* v_fileName_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_parseImports_x27(v_input_1533_, v_fileName_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1537_, lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref(v_k_1537_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_val_1540_ = lean_ctor_get(v_x_1538_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v_x_1538_, 1);
v___x_1541_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1540_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_k_1537_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
if (lean_obj_tag(v_a_1545_) == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_array_to_list(v_a_1546_);
return v___x_1547_;
}
else
{
lean_object* v_head_1548_; lean_object* v_tail_1549_; lean_object* v___x_1550_; 
v_head_1548_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_head_1548_);
v_tail_1549_ = lean_ctor_get(v_a_1545_, 1);
lean_inc(v_tail_1549_);
lean_dec_ref_known(v_a_1545_, 2);
v___x_1550_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1546_, v_head_1548_);
v_a_1545_ = v_tail_1549_;
v_a_1546_ = v___x_1550_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_bs_1554_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1555_ == 0)
{
return v_bs_1554_;
}
else
{
lean_object* v_v_1556_; lean_object* v___x_1557_; lean_object* v_bs_x27_1558_; lean_object* v___x_1559_; size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v_v_1556_ = lean_array_uget(v_bs_1554_, v_i_1553_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v_bs_x27_1558_ = lean_array_uset(v_bs_1554_, v_i_1553_, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_v_1556_);
v___x_1560_ = ((size_t)1ULL);
v___x_1561_ = lean_usize_add(v_i_1553_, v___x_1560_);
v___x_1562_ = lean_array_uset(v_bs_x27_1558_, v_i_1553_, v___x_1559_);
v_i_1553_ = v___x_1561_;
v_bs_1554_ = v___x_1562_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1552_ = stack[0].m_num;
size_t v_i_1553_ = stack[1].m_num;
lean_object* v_bs_1554_ = stack[2].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1552_, v_i_1553_, v_bs_1554_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_bs_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1571_){
_start:
{
size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_sz_1572_ = lean_array_size(v_a_1571_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1572_, v___x_1573_, v_a_1571_);
v___x_1575_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1580_){
_start:
{
lean_object* v_result_x3f_1581_; lean_object* v_errors_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1600_; 
v_result_x3f_1581_ = lean_ctor_get(v_x_1580_, 0);
v_errors_1582_ = lean_ctor_get(v_x_1580_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1580_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1584_ = v_x_1580_;
v_isShared_1585_ = v_isSharedCheck_1600_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_errors_1582_);
lean_inc(v_result_x3f_1581_);
lean_dec(v_x_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1600_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1586_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1587_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1586_, v_result_x3f_1581_);
v___x_1588_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1589_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v___x_1589_);
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1591_ = v___x_1584_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1592_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1587_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1597_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1595_, v___x_1596_);
v___x_1598_ = l_Lean_Json_mkObj(v___x_1597_);
lean_dec(v___x_1597_);
return v___x_1598_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1603_, size_t v_i_1604_, lean_object* v_bs_1605_){
_start:
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_usize_dec_lt(v_i_1604_, v_sz_1603_);
if (v___x_1606_ == 0)
{
return v_bs_1605_;
}
else
{
lean_object* v_v_1607_; lean_object* v___x_1608_; lean_object* v_bs_x27_1609_; lean_object* v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v_v_1607_ = lean_array_uget(v_bs_1605_, v_i_1604_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v_bs_x27_1609_ = lean_array_uset(v_bs_1605_, v_i_1604_, v___x_1608_);
v___x_1610_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1607_);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1604_, v___x_1611_);
v___x_1613_ = lean_array_uset(v_bs_x27_1609_, v_i_1604_, v___x_1610_);
v_i_1604_ = v___x_1612_;
v_bs_1605_ = v___x_1613_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1603_ = stack[0].m_num;
size_t v_i_1604_ = stack[1].m_num;
lean_object* v_bs_1605_ = stack[2].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1603_, v_i_1604_, v_bs_1605_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1616_, lean_object* v_i_1617_, lean_object* v_bs_1618_){
_start:
{
size_t v_sz_boxed_1619_; size_t v_i_boxed_1620_; lean_object* v_res_1621_; 
v_sz_boxed_1619_ = lean_unbox_usize(v_sz_1616_);
lean_dec(v_sz_1616_);
v_i_boxed_1620_ = lean_unbox_usize(v_i_1617_);
lean_dec(v_i_1617_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_1619_, v_i_boxed_1620_, v_bs_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* v_a_1622_){
_start:
{
size_t v_sz_1623_; size_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_sz_1623_ = lean_array_size(v_a_1622_);
v___x_1624_ = ((size_t)0ULL);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1623_, v___x_1624_, v_a_1622_);
v___x_1626_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1629_ = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
v___x_1630_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_1628_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v___x_1632_);
v___x_1635_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1636_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1634_, v___x_1635_);
v___x_1637_ = l_Lean_Json_mkObj(v___x_1636_);
lean_dec(v___x_1636_);
return v___x_1637_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1642_, size_t v_i_1643_, lean_object* v_bs_1644_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1643_, v_sz_1642_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_bs_1644_);
return v___x_1647_;
}
else
{
lean_object* v_v_1648_; lean_object* v___x_1649_; lean_object* v_bs_x27_1650_; lean_object* v_a_1652_; lean_object* v_a_1658_; lean_object* v___x_1665_; 
v_v_1648_ = lean_array_uget(v_bs_1644_, v_i_1643_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v_bs_x27_1650_ = lean_array_uset(v_bs_1644_, v_i_1643_, v___x_1649_);
v___x_1665_ = l_IO_FS_readFile(v_v_1648_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_parseImports_x27(v_a_1666_, v_v_1648_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1677_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 1);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v_a_1652_ = v___x_1675_;
goto v___jp_1651_;
}
}
}
else
{
lean_object* v_a_1678_; 
v_a_1678_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1667_, 1);
v_a_1658_ = v_a_1678_;
goto v___jp_1657_;
}
}
else
{
lean_object* v_a_1679_; 
lean_dec(v_v_1648_);
v_a_1679_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1665_, 1);
v_a_1658_ = v_a_1679_;
goto v___jp_1657_;
}
v___jp_1651_:
{
size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1643_, v___x_1653_);
v___x_1655_ = lean_array_uset(v_bs_x27_1650_, v_i_1643_, v_a_1652_);
v_i_1643_ = v___x_1654_;
v_bs_1644_ = v___x_1655_;
goto _start;
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_io_error_to_string(v_a_1658_);
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_mk_empty_array_with_capacity(v___x_1661_);
v___x_1663_ = lean_array_push(v___x_1662_, v___x_1660_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1659_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v_a_1652_ = v___x_1664_;
goto v___jp_1651_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1642_ = stack[0].m_num;
size_t v_i_1643_ = stack[1].m_num;
lean_object* v_bs_1644_ = stack[2].m_obj;
lean_object* v_res_1680_;
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1642_, v_i_1643_, v_bs_1644_);
stack->m_obj
 = v_res_1680_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1683_);
return v_res_1687_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v_putStr_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_get_stdout();
v_putStr_1691_ = lean_ctor_get(v___x_1690_, 4);
lean_inc_ref(v_putStr_1691_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = lean_apply_2(v_putStr_1691_, v_s_1688_, lean_box(0));
return v___x_1692_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1688_ = stack[0].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1688_);
stack->m_obj
 = v_res_1693_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1694_);
return v_res_1696_;
}
}
lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1697_){
_start:
{
uint32_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = 10;
v___x_1700_ = lean_string_push(v_s_1697_, v___x_1699_);
v___x_1701_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT void l_IO_println___at___00Lean_printImportsJson_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1697_ = stack[0].m_obj;
lean_object* v_res_1702_;
v_res_1702_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1697_);
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1703_);
return v_res_1705_;
}
}
lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1706_){
_start:
{
size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_sz_1708_ = lean_array_size(v_fileNames_1706_);
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1708_, v___x_1709_, v_fileNames_1706_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1711_);
v___x_1713_ = l_Lean_Json_compress(v___x_1712_);
v___x_1714_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1710_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1710_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_printImportsJson_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileNames_1706_ = stack[0].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l_Lean_printImportsJson(v_fileNames_1706_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_printImportsJson(v_fileNames_1724_);
return v_res_1726_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ParseImportsFast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ParseImportsFast(builtin);
}
#ifdef __cplusplus
}
#endif
