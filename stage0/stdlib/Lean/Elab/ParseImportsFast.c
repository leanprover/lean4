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
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_String_toFileMap(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object* v_p_298_, uint32_t v_c_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; uint8_t v___x_303_; 
v___x_300_ = lean_box_uint32(v_c_299_);
v___x_301_ = lean_apply_1(v_p_298_, v___x_300_);
v___x_302_ = lean_unbox(v___x_301_);
v___x_303_ = lean_bool_not(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object* v_p_304_, lean_object* v_c_305_){
_start:
{
uint32_t v_c_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_c_boxed_306_ = lean_unbox_uint32(v_c_305_);
lean_dec(v_c_305_);
v_res_307_ = l_Lean_ParseImports_takeWhile___lam__0(v_p_304_, v_c_boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* v_p_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___f_312_; lean_object* v___x_313_; 
v___f_312_ = lean_alloc_closure((void*)(l_Lean_ParseImports_takeWhile___lam__0___boxed), 2, 1);
lean_closure_set(v___f_312_, 0, v_p_309_);
v___x_313_ = l_Lean_ParseImports_takeUntil(v___f_312_, v_a_310_, v_a_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* v_p_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_ParseImports_takeWhile(v_p_314_, v_a_315_, v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* v_p_318_, lean_object* v_q_319_, lean_object* v_input_320_, lean_object* v_s_321_){
_start:
{
lean_object* v_s_322_; lean_object* v_error_x3f_323_; 
lean_inc_ref(v_input_320_);
v_s_322_ = lean_apply_2(v_p_318_, v_input_320_, v_s_321_);
v_error_x3f_323_ = lean_ctor_get(v_s_322_, 2);
lean_inc(v_error_x3f_323_);
if (lean_obj_tag(v_error_x3f_323_) == 1)
{
lean_dec_ref_known(v_error_x3f_323_, 1);
lean_dec_ref(v_input_320_);
lean_dec_ref(v_q_319_);
return v_s_322_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_error_x3f_323_);
v___x_324_ = lean_apply_2(v_q_319_, v_input_320_, v_s_322_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object* v_p_325_, lean_object* v_q_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_s_329_; lean_object* v_error_x3f_330_; 
lean_inc_ref(v___y_327_);
v_s_329_ = lean_apply_2(v_p_325_, v___y_327_, v___y_328_);
v_error_x3f_330_ = lean_ctor_get(v_s_329_, 2);
lean_inc(v_error_x3f_330_);
if (lean_obj_tag(v_error_x3f_330_) == 1)
{
lean_dec_ref_known(v_error_x3f_330_, 1);
lean_dec_ref(v___y_327_);
lean_dec_ref(v_q_326_);
return v_s_329_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_error_x3f_330_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_apply_3(v_q_326_, v___x_331_, v___y_327_, v_s_329_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(lean_object* v_input_335_, lean_object* v_s_336_){
_start:
{
lean_object* v_imports_337_; lean_object* v_pos_338_; uint8_t v_badModifier_339_; lean_object* v_error_x3f_340_; uint8_t v_isModule_341_; uint8_t v_isMeta_342_; uint8_t v_isExported_343_; uint8_t v_importAll_344_; uint8_t v___x_345_; 
v_imports_337_ = lean_ctor_get(v_s_336_, 0);
v_pos_338_ = lean_ctor_get(v_s_336_, 1);
v_badModifier_339_ = lean_ctor_get_uint8(v_s_336_, sizeof(void*)*3);
v_error_x3f_340_ = lean_ctor_get(v_s_336_, 2);
v_isModule_341_ = lean_ctor_get_uint8(v_s_336_, sizeof(void*)*3 + 1);
v_isMeta_342_ = lean_ctor_get_uint8(v_s_336_, sizeof(void*)*3 + 2);
v_isExported_343_ = lean_ctor_get_uint8(v_s_336_, sizeof(void*)*3 + 3);
v_importAll_344_ = lean_ctor_get_uint8(v_s_336_, sizeof(void*)*3 + 4);
v___x_345_ = lean_string_utf8_at_end(v_input_335_, v_pos_338_);
if (v___x_345_ == 0)
{
uint32_t v___x_346_; uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_string_utf8_get_fast(v_input_335_, v_pos_338_);
v___x_347_ = 10;
v___x_348_ = lean_uint32_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_357_; 
lean_inc(v_error_x3f_340_);
lean_inc(v_pos_338_);
lean_inc_ref(v_imports_337_);
v_isSharedCheck_357_ = !lean_is_exclusive(v_s_336_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_358_ = lean_ctor_get(v_s_336_, 2);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_s_336_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_s_336_, 0);
lean_dec(v_unused_360_);
v___x_350_ = v_s_336_;
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
else
{
lean_dec(v_s_336_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_string_utf8_next_fast(v_input_335_, v_pos_338_);
lean_dec(v_pos_338_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_imports_337_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_error_x3f_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*3, v_badModifier_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*3 + 1, v_isModule_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*3 + 2, v_isMeta_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*3 + 3, v_isExported_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_356_, sizeof(void*)*3 + 4, v_importAll_344_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_s_336_ = v___x_354_;
goto _start;
}
}
}
else
{
return v_s_336_;
}
}
else
{
return v_s_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(lean_object* v_input_361_, lean_object* v_s_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_361_, v_s_362_);
lean_dec_ref(v_input_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* v_input_367_, lean_object* v_s_368_){
_start:
{
lean_object* v_imports_369_; lean_object* v_pos_370_; uint8_t v_badModifier_371_; lean_object* v_error_x3f_372_; uint8_t v_isModule_373_; uint8_t v_isMeta_374_; uint8_t v_isExported_375_; uint8_t v_importAll_376_; uint8_t v___x_381_; 
v_imports_369_ = lean_ctor_get(v_s_368_, 0);
v_pos_370_ = lean_ctor_get(v_s_368_, 1);
v_badModifier_371_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3);
v_error_x3f_372_ = lean_ctor_get(v_s_368_, 2);
v_isModule_373_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3 + 1);
v_isMeta_374_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3 + 2);
v_isExported_375_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3 + 3);
v_importAll_376_ = lean_ctor_get_uint8(v_s_368_, sizeof(void*)*3 + 4);
v___x_381_ = lean_string_utf8_at_end(v_input_367_, v_pos_370_);
if (v___x_381_ == 0)
{
uint32_t v_curr_382_; uint8_t v___y_384_; uint8_t v___y_430_; uint32_t v___x_435_; uint8_t v___x_436_; 
v_curr_382_ = lean_string_utf8_get_fast(v_input_367_, v_pos_370_);
v___x_435_ = 9;
v___x_436_ = lean_uint32_dec_eq(v_curr_382_, v___x_435_);
if (v___x_436_ == 0)
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 32;
v___x_438_ = lean_uint32_dec_eq(v_curr_382_, v___x_437_);
if (v___x_438_ == 0)
{
v___y_430_ = v___x_436_;
goto v___jp_429_;
}
else
{
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
lean_inc(v_pos_370_);
lean_inc_ref(v_imports_369_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_447_ = lean_ctor_get(v_s_368_, 2);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_s_368_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_s_368_, 0);
lean_dec(v_unused_449_);
v___x_440_ = v_s_368_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_s_368_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_ParseImports_whitespace___closed__1));
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 2, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_imports_369_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_pos_370_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___x_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3, v_badModifier_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 1, v_isModule_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 2, v_isMeta_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 3, v_isExported_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 4, v_importAll_376_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 45;
v___x_386_ = lean_uint32_dec_eq(v_curr_382_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 47;
v___x_388_ = lean_uint32_dec_eq(v_curr_382_, v___x_387_);
if (v___x_388_ == 0)
{
return v_s_368_;
}
else
{
lean_object* v_i_389_; uint32_t v_curr_390_; uint8_t v___x_391_; 
v_i_389_ = lean_string_utf8_next_fast(v_input_367_, v_pos_370_);
v_curr_390_ = lean_string_utf8_get(v_input_367_, v_i_389_);
v___x_391_ = lean_uint32_dec_eq(v_curr_390_, v___x_385_);
if (v___x_391_ == 0)
{
return v_s_368_;
}
else
{
lean_object* v_i_392_; uint32_t v_curr_393_; uint8_t v___x_394_; 
v_i_392_ = lean_string_utf8_next(v_input_367_, v_i_389_);
v_curr_393_ = lean_string_utf8_get(v_input_367_, v_i_392_);
v___x_394_ = lean_uint32_dec_eq(v_curr_393_, v___x_385_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 33;
v___x_396_ = lean_uint32_dec_eq(v_curr_393_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_408_; 
lean_inc(v_error_x3f_372_);
lean_inc_ref(v_imports_369_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_409_ = lean_ctor_get(v_s_368_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_s_368_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_s_368_, 0);
lean_dec(v_unused_411_);
v___x_398_ = v_s_368_;
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
else
{
lean_dec(v_s_368_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_408_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_string_utf8_next(v_input_367_, v_i_392_);
lean_dec(v_i_392_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_imports_369_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_error_x3f_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3, v_badModifier_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3 + 1, v_isModule_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3 + 2, v_isMeta_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3 + 3, v_isExported_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3 + 4, v_importAll_376_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v_s_404_; lean_object* v_error_x3f_405_; 
v_s_404_ = l_Lean_ParseImports_finishCommentBlock(v___x_400_, v_input_367_, v___x_403_);
v_error_x3f_405_ = lean_ctor_get(v_s_404_, 2);
lean_inc(v_error_x3f_405_);
if (lean_obj_tag(v_error_x3f_405_) == 1)
{
lean_dec_ref_known(v_error_x3f_405_, 1);
return v_s_404_;
}
else
{
lean_dec(v_error_x3f_405_);
v_s_368_ = v_s_404_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_392_);
return v_s_368_;
}
}
else
{
lean_dec(v_i_392_);
return v_s_368_;
}
}
}
}
else
{
lean_object* v_i_412_; uint32_t v_curr_413_; uint8_t v___x_414_; 
v_i_412_ = lean_string_utf8_next_fast(v_input_367_, v_pos_370_);
v_curr_413_ = lean_string_utf8_get(v_input_367_, v_i_412_);
v___x_414_ = lean_uint32_dec_eq(v_curr_413_, v___x_385_);
if (v___x_414_ == 0)
{
return v_s_368_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
lean_inc(v_error_x3f_372_);
lean_inc_ref(v_imports_369_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_s_368_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_426_ = lean_ctor_get(v_s_368_, 2);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_s_368_, 1);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_s_368_, 0);
lean_dec(v_unused_428_);
v___x_416_ = v_s_368_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_s_368_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_string_utf8_next(v_input_367_, v_i_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_imports_369_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_error_x3f_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3, v_badModifier_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3 + 1, v_isModule_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3 + 2, v_isMeta_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3 + 3, v_isExported_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3 + 4, v_importAll_376_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v_s_421_; lean_object* v_error_x3f_422_; 
v_s_421_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_367_, v___x_420_);
v_error_x3f_422_ = lean_ctor_get(v_s_421_, 2);
lean_inc(v_error_x3f_422_);
if (lean_obj_tag(v_error_x3f_422_) == 1)
{
lean_dec_ref_known(v_error_x3f_422_, 1);
return v_s_421_;
}
else
{
lean_dec(v_error_x3f_422_);
v_s_368_ = v_s_421_;
goto _start;
}
}
}
}
}
}
else
{
lean_inc(v_error_x3f_372_);
lean_inc(v_pos_370_);
lean_inc_ref(v_imports_369_);
lean_dec_ref(v_s_368_);
goto v___jp_377_;
}
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 13;
v___x_432_ = lean_uint32_dec_eq(v_curr_382_, v___x_431_);
if (v___x_432_ == 0)
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 10;
v___x_434_ = lean_uint32_dec_eq(v_curr_382_, v___x_433_);
v___y_384_ = v___x_434_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___x_432_;
goto v___jp_383_;
}
}
else
{
lean_inc(v_error_x3f_372_);
lean_inc(v_pos_370_);
lean_inc_ref(v_imports_369_);
lean_dec_ref(v_s_368_);
goto v___jp_377_;
}
}
}
else
{
return v_s_368_;
}
v___jp_377_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_string_utf8_next(v_input_367_, v_pos_370_);
lean_dec(v_pos_370_);
v___x_379_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_379_, 0, v_imports_369_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_ctor_set(v___x_379_, 2, v_error_x3f_372_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3, v_badModifier_371_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 1, v_isModule_373_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 2, v_isMeta_374_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 3, v_isExported_375_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 4, v_importAll_376_);
v_s_368_ = v___x_379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* v_input_450_, lean_object* v_s_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_ParseImports_whitespace(v_input_450_, v_s_451_);
lean_dec_ref(v_input_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object* v_k_453_, lean_object* v_failure_454_, lean_object* v_success_455_, lean_object* v_input_456_, lean_object* v_s_457_, lean_object* v_i_458_, lean_object* v_j_459_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_string_utf8_at_end(v_k_453_, v_i_458_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = lean_string_utf8_at_end(v_input_456_, v_j_459_);
if (v___x_461_ == 0)
{
uint32_t v_curr_u2081_462_; uint32_t v_curr_u2082_463_; uint8_t v___x_464_; uint8_t v___x_465_; 
v_curr_u2081_462_ = lean_string_utf8_get_fast(v_k_453_, v_i_458_);
v_curr_u2082_463_ = lean_string_utf8_get_fast(v_input_456_, v_j_459_);
v___x_464_ = lean_uint32_dec_eq(v_curr_u2081_462_, v_curr_u2082_463_);
v___x_465_ = lean_bool_not(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_string_utf8_next_fast(v_k_453_, v_i_458_);
lean_dec(v_i_458_);
v___x_467_ = lean_string_utf8_next_fast(v_input_456_, v_j_459_);
lean_dec(v_j_459_);
v_i_458_ = v___x_466_;
v_j_459_ = v___x_467_;
goto _start;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_j_459_);
lean_dec(v_i_458_);
lean_dec_ref(v_success_455_);
v___x_469_ = lean_apply_2(v_failure_454_, v_input_456_, v_s_457_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_j_459_);
lean_dec(v_i_458_);
lean_dec_ref(v_success_455_);
v___x_470_ = lean_apply_2(v_failure_454_, v_input_456_, v_s_457_);
return v___x_470_;
}
}
else
{
lean_object* v_imports_471_; uint8_t v_badModifier_472_; lean_object* v_error_x3f_473_; uint8_t v_isModule_474_; uint8_t v_isMeta_475_; uint8_t v_isExported_476_; uint8_t v_importAll_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_i_458_);
lean_dec_ref(v_failure_454_);
v_imports_471_ = lean_ctor_get(v_s_457_, 0);
v_badModifier_472_ = lean_ctor_get_uint8(v_s_457_, sizeof(void*)*3);
v_error_x3f_473_ = lean_ctor_get(v_s_457_, 2);
v_isModule_474_ = lean_ctor_get_uint8(v_s_457_, sizeof(void*)*3 + 1);
v_isMeta_475_ = lean_ctor_get_uint8(v_s_457_, sizeof(void*)*3 + 2);
v_isExported_476_ = lean_ctor_get_uint8(v_s_457_, sizeof(void*)*3 + 3);
v_importAll_477_ = lean_ctor_get_uint8(v_s_457_, sizeof(void*)*3 + 4);
v_isSharedCheck_486_ = !lean_is_exclusive(v_s_457_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_s_457_, 1);
lean_dec(v_unused_487_);
v___x_479_ = v_s_457_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_error_x3f_473_);
lean_inc(v_imports_471_);
lean_dec(v_s_457_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_j_459_);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_imports_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_j_459_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_error_x3f_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3, v_badModifier_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3 + 1, v_isModule_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3 + 2, v_isMeta_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3 + 3, v_isExported_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3 + 4, v_importAll_477_);
v___x_482_ = v_reuseFailAlloc_485_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = l_Lean_ParseImports_whitespace(v_input_456_, v___x_482_);
v___x_484_ = lean_apply_2(v_success_455_, v_input_456_, v___x_483_);
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* v_k_488_, lean_object* v_failure_489_, lean_object* v_success_490_, lean_object* v_input_491_, lean_object* v_s_492_, lean_object* v_i_493_, lean_object* v_j_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_488_, v_failure_489_, v_success_490_, v_input_491_, v_s_492_, v_i_493_, v_j_494_);
lean_dec_ref(v_k_488_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* v_k_496_, lean_object* v_failure_497_, lean_object* v_success_498_, lean_object* v_input_499_, lean_object* v_s_500_){
_start:
{
lean_object* v_pos_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_pos_501_ = lean_ctor_get(v_s_500_, 1);
lean_inc(v_pos_501_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_496_, v_failure_497_, v_success_498_, v_input_499_, v_s_500_, v___x_502_, v_pos_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* v_k_504_, lean_object* v_failure_505_, lean_object* v_success_506_, lean_object* v_input_507_, lean_object* v_s_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_ParseImports_keywordCore(v_k_504_, v_failure_505_, v_success_506_, v_input_507_, v_s_508_);
lean_dec_ref(v_k_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* v_k_512_, lean_object* v_x_513_, lean_object* v_s_514_){
_start:
{
lean_object* v_imports_515_; lean_object* v_pos_516_; uint8_t v_badModifier_517_; uint8_t v_isModule_518_; uint8_t v_isMeta_519_; uint8_t v_isExported_520_; uint8_t v_importAll_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_imports_515_ = lean_ctor_get(v_s_514_, 0);
v_pos_516_ = lean_ctor_get(v_s_514_, 1);
v_badModifier_517_ = lean_ctor_get_uint8(v_s_514_, sizeof(void*)*3);
v_isModule_518_ = lean_ctor_get_uint8(v_s_514_, sizeof(void*)*3 + 1);
v_isMeta_519_ = lean_ctor_get_uint8(v_s_514_, sizeof(void*)*3 + 2);
v_isExported_520_ = lean_ctor_get_uint8(v_s_514_, sizeof(void*)*3 + 3);
v_importAll_521_ = lean_ctor_get_uint8(v_s_514_, sizeof(void*)*3 + 4);
v_isSharedCheck_533_ = !lean_is_exclusive(v_s_514_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_s_514_, 2);
lean_dec(v_unused_534_);
v___x_523_ = v_s_514_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_pos_516_);
lean_inc(v_imports_515_);
lean_dec(v_s_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_525_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
v___x_526_ = lean_string_append(v___x_525_, v_k_512_);
v___x_527_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 2, v___x_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_imports_515_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_pos_516_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v___x_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*3, v_badModifier_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*3 + 1, v_isModule_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*3 + 2, v_isMeta_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*3 + 3, v_isExported_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*3 + 4, v_importAll_521_);
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* v_k_535_, lean_object* v_x_536_, lean_object* v_s_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_ParseImports_keyword___lam__0(v_k_535_, v_x_536_, v_s_537_);
lean_dec_ref(v_x_536_);
lean_dec_ref(v_k_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* v_k_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_pos_542_; lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_pos_542_ = lean_ctor_get(v_a_541_, 1);
lean_inc(v_pos_542_);
lean_inc_ref(v_k_539_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(v___f_543_, 0, v_k_539_);
v___x_544_ = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_539_, v___f_543_, v___x_544_, v_a_540_, v_a_541_, v___x_545_, v_pos_542_);
lean_dec_ref(v_k_539_);
return v___x_546_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* v_input_547_, lean_object* v_s_548_){
_start:
{
lean_object* v_pos_549_; uint32_t v_curr_550_; uint32_t v___x_551_; uint8_t v___x_552_; 
v_pos_549_ = lean_ctor_get(v_s_548_, 1);
v_curr_550_ = lean_string_utf8_get(v_input_547_, v_pos_549_);
v___x_551_ = 46;
v___x_552_ = lean_uint32_dec_eq(v_curr_550_, v___x_551_);
if (v___x_552_ == 0)
{
return v___x_552_;
}
else
{
lean_object* v_i_553_; uint8_t v___x_554_; 
v_i_553_ = lean_string_utf8_next(v_input_547_, v_pos_549_);
v___x_554_ = lean_string_utf8_at_end(v_input_547_, v_i_553_);
if (v___x_554_ == 0)
{
uint32_t v_curr_555_; uint8_t v___y_557_; uint8_t v___y_561_; uint32_t v___x_570_; uint8_t v___x_571_; 
v_curr_555_ = lean_string_utf8_get_fast(v_input_547_, v_i_553_);
lean_dec(v_i_553_);
v___x_570_ = 65;
v___x_571_ = lean_uint32_dec_le(v___x_570_, v_curr_555_);
if (v___x_571_ == 0)
{
goto v___jp_565_;
}
else
{
uint32_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = 90;
v___x_573_ = lean_uint32_dec_le(v_curr_555_, v___x_572_);
if (v___x_573_ == 0)
{
goto v___jp_565_;
}
else
{
return v___x_552_;
}
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 171;
v___x_559_ = lean_uint32_dec_eq(v_curr_555_, v___x_558_);
return v___x_559_;
}
else
{
return v___x_552_;
}
}
v___jp_560_:
{
if (v___y_561_ == 0)
{
uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 95;
v___x_563_ = lean_uint32_dec_eq(v_curr_555_, v___x_562_);
if (v___x_563_ == 0)
{
uint8_t v___x_564_; 
v___x_564_ = l_Lean_isLetterLike(v_curr_555_);
v___y_557_ = v___x_564_;
goto v___jp_556_;
}
else
{
v___y_557_ = v___x_563_;
goto v___jp_556_;
}
}
else
{
return v___x_552_;
}
}
v___jp_565_:
{
uint32_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = 97;
v___x_567_ = lean_uint32_dec_le(v___x_566_, v_curr_555_);
if (v___x_567_ == 0)
{
v___y_561_ = v___x_567_;
goto v___jp_560_;
}
else
{
uint32_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 122;
v___x_569_ = lean_uint32_dec_le(v_curr_555_, v___x_568_);
v___y_561_ = v___x_569_;
goto v___jp_560_;
}
}
}
else
{
uint8_t v___x_574_; 
lean_dec(v_i_553_);
v___x_574_ = 0;
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_575_, lean_object* v_s_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_Lean_ParseImports_isIdCont(v_input_575_, v_s_576_);
lean_dec_ref(v_s_576_);
lean_dec_ref(v_input_575_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_579_, lean_object* v_s_580_){
_start:
{
lean_object* v_imports_581_; lean_object* v_pos_582_; uint8_t v_badModifier_583_; lean_object* v_error_x3f_584_; uint8_t v_isModule_585_; uint8_t v_isMeta_586_; uint8_t v_isExported_587_; uint8_t v_importAll_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_imports_581_ = lean_ctor_get(v_s_580_, 0);
v_pos_582_ = lean_ctor_get(v_s_580_, 1);
v_badModifier_583_ = lean_ctor_get_uint8(v_s_580_, sizeof(void*)*3);
v_error_x3f_584_ = lean_ctor_get(v_s_580_, 2);
v_isModule_585_ = lean_ctor_get_uint8(v_s_580_, sizeof(void*)*3 + 1);
v_isMeta_586_ = lean_ctor_get_uint8(v_s_580_, sizeof(void*)*3 + 2);
v_isExported_587_ = lean_ctor_get_uint8(v_s_580_, sizeof(void*)*3 + 3);
v_importAll_588_ = lean_ctor_get_uint8(v_s_580_, sizeof(void*)*3 + 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v_s_580_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v_s_580_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_error_x3f_584_);
lean_inc(v_pos_582_);
lean_inc(v_imports_581_);
lean_dec(v_s_580_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_array_push(v_imports_581_, v_i_579_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_pos_582_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_error_x3f_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*3, v_badModifier_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*3 + 1, v_isModule_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*3 + 2, v_isMeta_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*3 + 3, v_isExported_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*3 + 4, v_importAll_588_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_597_){
_start:
{
uint8_t v___y_599_; uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 95;
v___x_607_ = lean_uint32_dec_eq(v_c_597_, v___x_606_);
if (v___x_607_ == 0)
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 39;
v___x_609_ = lean_uint32_dec_eq(v_c_597_, v___x_608_);
v___y_599_ = v___x_609_;
goto v___jp_598_;
}
else
{
v___y_599_ = v___x_607_;
goto v___jp_598_;
}
v___jp_598_:
{
if (v___y_599_ == 0)
{
uint32_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 33;
v___x_601_ = lean_uint32_dec_eq(v_c_597_, v___x_600_);
if (v___x_601_ == 0)
{
uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 63;
v___x_603_ = lean_uint32_dec_eq(v_c_597_, v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = l_Lean_isLetterLike(v_c_597_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = l_Lean_isSubScriptAlnum(v_c_597_);
return v___x_605_;
}
else
{
return v___x_604_;
}
}
else
{
return v___x_603_;
}
}
else
{
return v___x_601_;
}
}
else
{
return v___y_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_610_){
_start:
{
uint32_t v_c_boxed_611_; uint8_t v_res_612_; lean_object* v_r_613_; 
v_c_boxed_611_ = lean_unbox_uint32(v_c_610_);
lean_dec(v_c_610_);
v_res_612_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_614_){
_start:
{
uint8_t v___y_616_; uint8_t v___y_624_; uint8_t v___y_633_; uint8_t v___y_641_; uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 65;
v___x_652_ = lean_uint32_dec_le(v___x_651_, v_c_614_);
if (v___x_652_ == 0)
{
goto v___jp_646_;
}
else
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 90;
v___x_654_ = lean_uint32_dec_le(v_c_614_, v___x_653_);
if (v___x_654_ == 0)
{
goto v___jp_646_;
}
else
{
return v___x_654_;
}
}
v___jp_615_:
{
if (v___y_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 33;
v___x_618_ = lean_uint32_dec_eq(v_c_614_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 63;
v___x_620_ = lean_uint32_dec_eq(v_c_614_, v___x_619_);
if (v___x_620_ == 0)
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_isLetterLike(v_c_614_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_isSubScriptAlnum(v_c_614_);
return v___x_622_;
}
else
{
return v___x_621_;
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
return v___y_616_;
}
}
v___jp_623_:
{
if (v___y_624_ == 0)
{
return v___y_624_;
}
else
{
uint32_t v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_625_ = 32;
v___x_626_ = lean_uint32_dec_eq(v_c_614_, v___x_625_);
v___x_627_ = lean_bool_not(v___x_626_);
if (v___x_627_ == 0)
{
return v___x_627_;
}
else
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 95;
v___x_629_ = lean_uint32_dec_eq(v_c_614_, v___x_628_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 39;
v___x_631_ = lean_uint32_dec_eq(v_c_614_, v___x_630_);
v___y_616_ = v___x_631_;
goto v___jp_615_;
}
else
{
v___y_616_ = v___x_629_;
goto v___jp_615_;
}
}
}
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
uint32_t v___x_634_; uint8_t v___x_635_; uint8_t v___x_636_; 
v___x_634_ = 46;
v___x_635_ = lean_uint32_dec_eq(v_c_614_, v___x_634_);
v___x_636_ = lean_bool_not(v___x_635_);
if (v___x_636_ == 0)
{
v___y_624_ = v___x_636_;
goto v___jp_623_;
}
else
{
uint32_t v___x_637_; uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_637_ = 10;
v___x_638_ = lean_uint32_dec_eq(v_c_614_, v___x_637_);
v___x_639_ = lean_bool_not(v___x_638_);
v___y_624_ = v___x_639_;
goto v___jp_623_;
}
}
else
{
return v___y_633_;
}
}
v___jp_640_:
{
if (v___y_641_ == 0)
{
uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 48;
v___x_643_ = lean_uint32_dec_le(v___x_642_, v_c_614_);
if (v___x_643_ == 0)
{
v___y_633_ = v___x_643_;
goto v___jp_632_;
}
else
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 57;
v___x_645_ = lean_uint32_dec_le(v_c_614_, v___x_644_);
v___y_633_ = v___x_645_;
goto v___jp_632_;
}
}
else
{
return v___y_641_;
}
}
v___jp_646_:
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 97;
v___x_648_ = lean_uint32_dec_le(v___x_647_, v_c_614_);
if (v___x_648_ == 0)
{
v___y_641_ = v___x_648_;
goto v___jp_640_;
}
else
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 122;
v___x_650_ = lean_uint32_dec_le(v_c_614_, v___x_649_);
v___y_641_ = v___x_650_;
goto v___jp_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_655_){
_start:
{
uint32_t v_c_boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_c_boxed_656_ = lean_unbox_uint32(v_c_655_);
lean_dec(v_c_655_);
v_res_657_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_659_, lean_object* v_s_660_){
_start:
{
lean_object* v_imports_661_; lean_object* v_pos_662_; uint8_t v_badModifier_663_; lean_object* v_error_x3f_664_; uint8_t v_isModule_665_; uint8_t v_isMeta_666_; uint8_t v_isExported_667_; uint8_t v_importAll_668_; uint8_t v___x_669_; 
v_imports_661_ = lean_ctor_get(v_s_660_, 0);
v_pos_662_ = lean_ctor_get(v_s_660_, 1);
v_badModifier_663_ = lean_ctor_get_uint8(v_s_660_, sizeof(void*)*3);
v_error_x3f_664_ = lean_ctor_get(v_s_660_, 2);
v_isModule_665_ = lean_ctor_get_uint8(v_s_660_, sizeof(void*)*3 + 1);
v_isMeta_666_ = lean_ctor_get_uint8(v_s_660_, sizeof(void*)*3 + 2);
v_isExported_667_ = lean_ctor_get_uint8(v_s_660_, sizeof(void*)*3 + 3);
v_importAll_668_ = lean_ctor_get_uint8(v_s_660_, sizeof(void*)*3 + 4);
v___x_669_ = lean_string_utf8_at_end(v_input_659_, v_pos_662_);
if (v___x_669_ == 0)
{
uint32_t v___x_670_; uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_string_utf8_get_fast(v_input_659_, v_pos_662_);
v___x_671_ = 187;
v___x_672_ = lean_uint32_dec_eq(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
lean_inc(v_error_x3f_664_);
lean_inc(v_pos_662_);
lean_inc_ref(v_imports_661_);
v_isSharedCheck_681_ = !lean_is_exclusive(v_s_660_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_682_ = lean_ctor_get(v_s_660_, 2);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_s_660_, 1);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_s_660_, 0);
lean_dec(v_unused_684_);
v___x_674_ = v_s_660_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_dec(v_s_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_string_utf8_next_fast(v_input_659_, v_pos_662_);
lean_dec(v_pos_662_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_imports_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_error_x3f_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3, v_badModifier_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 1, v_isModule_665_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 2, v_isMeta_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 3, v_isExported_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 4, v_importAll_668_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v_s_660_ = v___x_678_;
goto _start;
}
}
}
else
{
return v_s_660_;
}
}
else
{
return v_s_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_685_, lean_object* v_s_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_685_, v_s_686_);
lean_dec_ref(v_input_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_688_, lean_object* v_input_689_, lean_object* v_s_690_){
_start:
{
lean_object* v_imports_691_; lean_object* v_pos_692_; uint8_t v_badModifier_693_; lean_object* v_error_x3f_694_; uint8_t v_isModule_695_; uint8_t v_isMeta_696_; uint8_t v_isExported_697_; uint8_t v_importAll_698_; uint8_t v___y_700_; uint8_t v___x_713_; 
v_imports_691_ = lean_ctor_get(v_s_690_, 0);
v_pos_692_ = lean_ctor_get(v_s_690_, 1);
v_badModifier_693_ = lean_ctor_get_uint8(v_s_690_, sizeof(void*)*3);
v_error_x3f_694_ = lean_ctor_get(v_s_690_, 2);
v_isModule_695_ = lean_ctor_get_uint8(v_s_690_, sizeof(void*)*3 + 1);
v_isMeta_696_ = lean_ctor_get_uint8(v_s_690_, sizeof(void*)*3 + 2);
v_isExported_697_ = lean_ctor_get_uint8(v_s_690_, sizeof(void*)*3 + 3);
v_importAll_698_ = lean_ctor_get_uint8(v_s_690_, sizeof(void*)*3 + 4);
v___x_713_ = lean_string_utf8_at_end(v_input_689_, v_pos_692_);
if (v___x_713_ == 0)
{
uint32_t v___x_714_; uint8_t v___y_716_; uint8_t v___y_729_; uint8_t v___y_740_; uint8_t v___y_749_; uint32_t v___x_760_; uint8_t v___x_761_; 
v___x_714_ = lean_string_utf8_get_fast(v_input_689_, v_pos_692_);
v___x_760_ = 65;
v___x_761_ = lean_uint32_dec_le(v___x_760_, v___x_714_);
if (v___x_761_ == 0)
{
goto v___jp_755_;
}
else
{
uint32_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 90;
v___x_763_ = lean_uint32_dec_le(v___x_714_, v___x_762_);
if (v___x_763_ == 0)
{
goto v___jp_755_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = lean_bool_not(v___y_688_);
v___y_700_ = v___x_764_;
goto v___jp_699_;
}
}
v___jp_715_:
{
if (v___y_716_ == 0)
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 33;
v___x_718_ = lean_uint32_dec_eq(v___x_714_, v___x_717_);
if (v___x_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 63;
v___x_720_ = lean_uint32_dec_eq(v___x_714_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_isLetterLike(v___x_714_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = l_Lean_isSubScriptAlnum(v___x_714_);
v___x_723_ = lean_bool_not(v___x_722_);
v___y_700_ = v___x_723_;
goto v___jp_699_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = lean_bool_not(v___x_721_);
v___y_700_ = v___x_724_;
goto v___jp_699_;
}
}
else
{
uint8_t v___x_725_; 
v___x_725_ = lean_bool_not(v___x_720_);
v___y_700_ = v___x_725_;
goto v___jp_699_;
}
}
else
{
uint8_t v___x_726_; 
v___x_726_ = lean_bool_not(v___x_718_);
v___y_700_ = v___x_726_;
goto v___jp_699_;
}
}
else
{
uint8_t v___x_727_; 
v___x_727_ = lean_bool_not(v___y_716_);
v___y_700_ = v___x_727_;
goto v___jp_699_;
}
}
v___jp_728_:
{
if (v___y_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = lean_bool_not(v___y_729_);
v___y_700_ = v___x_730_;
goto v___jp_699_;
}
else
{
uint32_t v___x_731_; uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = 32;
v___x_732_ = lean_uint32_dec_eq(v___x_714_, v___x_731_);
v___x_733_ = lean_bool_not(v___x_732_);
if (v___x_733_ == 0)
{
uint8_t v___x_734_; 
v___x_734_ = lean_bool_not(v___x_733_);
v___y_700_ = v___x_734_;
goto v___jp_699_;
}
else
{
uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 95;
v___x_736_ = lean_uint32_dec_eq(v___x_714_, v___x_735_);
if (v___x_736_ == 0)
{
uint32_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 39;
v___x_738_ = lean_uint32_dec_eq(v___x_714_, v___x_737_);
v___y_716_ = v___x_738_;
goto v___jp_715_;
}
else
{
v___y_716_ = v___x_736_;
goto v___jp_715_;
}
}
}
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
uint32_t v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; 
v___x_741_ = 46;
v___x_742_ = lean_uint32_dec_eq(v___x_714_, v___x_741_);
v___x_743_ = lean_bool_not(v___x_742_);
if (v___x_743_ == 0)
{
v___y_729_ = v___x_743_;
goto v___jp_728_;
}
else
{
uint32_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; 
v___x_744_ = 10;
v___x_745_ = lean_uint32_dec_eq(v___x_714_, v___x_744_);
v___x_746_ = lean_bool_not(v___x_745_);
v___y_729_ = v___x_746_;
goto v___jp_728_;
}
}
else
{
uint8_t v___x_747_; 
v___x_747_ = lean_bool_not(v___y_740_);
v___y_700_ = v___x_747_;
goto v___jp_699_;
}
}
v___jp_748_:
{
if (v___y_749_ == 0)
{
uint32_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 48;
v___x_751_ = lean_uint32_dec_le(v___x_750_, v___x_714_);
if (v___x_751_ == 0)
{
v___y_740_ = v___x_751_;
goto v___jp_739_;
}
else
{
uint32_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 57;
v___x_753_ = lean_uint32_dec_le(v___x_714_, v___x_752_);
v___y_740_ = v___x_753_;
goto v___jp_739_;
}
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_bool_not(v___y_749_);
v___y_700_ = v___x_754_;
goto v___jp_699_;
}
}
v___jp_755_:
{
uint32_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = 97;
v___x_757_ = lean_uint32_dec_le(v___x_756_, v___x_714_);
if (v___x_757_ == 0)
{
v___y_749_ = v___x_757_;
goto v___jp_748_;
}
else
{
uint32_t v___x_758_; uint8_t v___x_759_; 
v___x_758_ = 122;
v___x_759_ = lean_uint32_dec_le(v___x_714_, v___x_758_);
v___y_749_ = v___x_759_;
goto v___jp_748_;
}
}
}
else
{
return v_s_690_;
}
v___jp_699_:
{
if (v___y_700_ == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
lean_inc(v_error_x3f_694_);
lean_inc(v_pos_692_);
lean_inc_ref(v_imports_691_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_s_690_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_710_ = lean_ctor_get(v_s_690_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_s_690_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_s_690_, 0);
lean_dec(v_unused_712_);
v___x_702_ = v_s_690_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_s_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_string_utf8_next_fast(v_input_689_, v_pos_692_);
lean_dec(v_pos_692_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_imports_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_error_x3f_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3, v_badModifier_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 1, v_isModule_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 2, v_isMeta_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 3, v_isExported_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*3 + 4, v_importAll_698_);
v___x_706_ = v_reuseFailAlloc_708_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_s_690_ = v___x_706_;
goto _start;
}
}
}
else
{
return v_s_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_765_, lean_object* v_input_766_, lean_object* v_s_767_){
_start:
{
uint8_t v___y_2339__boxed_768_; lean_object* v_res_769_; 
v___y_2339__boxed_768_ = lean_unbox(v___y_765_);
v_res_769_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_2339__boxed_768_, v_input_766_, v_s_767_);
lean_dec_ref(v_input_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_776_, lean_object* v_finalize_777_, lean_object* v_module_778_, lean_object* v_s_779_){
_start:
{
lean_object* v___y_781_; lean_object* v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; uint8_t v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v_imports_796_; lean_object* v_pos_797_; uint8_t v_badModifier_798_; lean_object* v_error_x3f_799_; uint8_t v_isModule_800_; uint8_t v_isMeta_801_; uint8_t v_isExported_802_; uint8_t v_importAll_803_; uint8_t v___x_804_; 
v_imports_796_ = lean_ctor_get(v_s_779_, 0);
v_pos_797_ = lean_ctor_get(v_s_779_, 1);
v_badModifier_798_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*3);
v_error_x3f_799_ = lean_ctor_get(v_s_779_, 2);
v_isModule_800_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*3 + 1);
v_isMeta_801_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*3 + 2);
v_isExported_802_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*3 + 3);
v_importAll_803_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*3 + 4);
v___x_804_ = lean_string_utf8_at_end(v_input_776_, v_pos_797_);
if (v___x_804_ == 0)
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_960_; 
lean_inc(v_error_x3f_799_);
lean_inc(v_pos_797_);
lean_inc_ref(v_imports_796_);
v_isSharedCheck_960_ = !lean_is_exclusive(v_s_779_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_961_ = lean_ctor_get(v_s_779_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_s_779_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_s_779_, 0);
lean_dec(v_unused_963_);
v___x_806_ = v_s_779_;
v_isShared_807_ = v_isSharedCheck_960_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_s_779_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_960_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint32_t v_curr_808_; uint32_t v___x_809_; lean_object* v___y_811_; lean_object* v___y_812_; uint32_t v___y_813_; uint8_t v___y_814_; uint8_t v___y_815_; uint8_t v___y_816_; lean_object* v___y_817_; uint8_t v___y_818_; uint8_t v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; uint8_t v___y_823_; lean_object* v___y_826_; lean_object* v___y_827_; uint32_t v___y_828_; uint8_t v___y_829_; uint8_t v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; uint8_t v___y_833_; uint8_t v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; uint8_t v___y_837_; uint8_t v___y_838_; lean_object* v___y_843_; lean_object* v___y_844_; uint32_t v___y_845_; uint8_t v___y_846_; uint8_t v___y_847_; uint8_t v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; uint8_t v___y_851_; uint8_t v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v___x_859_; uint8_t v___y_861_; uint8_t v___y_888_; uint8_t v___y_892_; 
v_curr_808_ = lean_string_utf8_get_fast(v_input_776_, v_pos_797_);
v___x_809_ = 171;
v___x_859_ = lean_uint32_dec_eq(v_curr_808_, v___x_809_);
if (v___x_859_ == 0)
{
uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = 65;
v___x_902_ = lean_uint32_dec_le(v___x_901_, v_curr_808_);
if (v___x_902_ == 0)
{
goto v___jp_896_;
}
else
{
uint32_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = 90;
v___x_904_ = lean_uint32_dec_le(v_curr_808_, v___x_903_);
if (v___x_904_ == 0)
{
goto v___jp_896_;
}
else
{
v___y_861_ = v___x_904_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v_startPart_905_; lean_object* v___x_906_; lean_object* v_s_907_; lean_object* v_imports_908_; lean_object* v_pos_909_; uint8_t v_badModifier_910_; lean_object* v_error_x3f_911_; uint8_t v_isModule_912_; uint8_t v_isMeta_913_; uint8_t v_isExported_914_; uint8_t v_importAll_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_806_);
v_startPart_905_ = lean_string_utf8_next_fast(v_input_776_, v_pos_797_);
lean_dec(v_pos_797_);
v___x_906_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_906_, 0, v_imports_796_);
lean_ctor_set(v___x_906_, 1, v_startPart_905_);
lean_ctor_set(v___x_906_, 2, v_error_x3f_799_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3, v_badModifier_798_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3 + 1, v_isModule_800_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3 + 2, v_isMeta_801_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3 + 3, v_isExported_802_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3 + 4, v_importAll_803_);
v_s_907_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_776_, v___x_906_);
v_imports_908_ = lean_ctor_get(v_s_907_, 0);
v_pos_909_ = lean_ctor_get(v_s_907_, 1);
v_badModifier_910_ = lean_ctor_get_uint8(v_s_907_, sizeof(void*)*3);
v_error_x3f_911_ = lean_ctor_get(v_s_907_, 2);
v_isModule_912_ = lean_ctor_get_uint8(v_s_907_, sizeof(void*)*3 + 1);
v_isMeta_913_ = lean_ctor_get_uint8(v_s_907_, sizeof(void*)*3 + 2);
v_isExported_914_ = lean_ctor_get_uint8(v_s_907_, sizeof(void*)*3 + 3);
v_importAll_915_ = lean_ctor_get_uint8(v_s_907_, sizeof(void*)*3 + 4);
v_isSharedCheck_959_ = !lean_is_exclusive(v_s_907_);
if (v_isSharedCheck_959_ == 0)
{
v___x_917_ = v_s_907_;
v_isShared_918_ = v_isSharedCheck_959_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_error_x3f_911_);
lean_inc(v_pos_909_);
lean_inc(v_imports_908_);
lean_dec(v_s_907_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_959_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = lean_string_utf8_at_end(v_input_776_, v_pos_909_);
if (v___x_919_ == 0)
{
lean_object* v_i_920_; lean_object* v_s_922_; 
v_i_920_ = lean_string_utf8_next_fast(v_input_776_, v_pos_909_);
lean_inc(v_error_x3f_911_);
lean_inc_ref(v_imports_908_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_i_920_);
v_s_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_imports_908_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_i_920_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_error_x3f_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3, v_badModifier_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 1, v_isModule_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 2, v_isMeta_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 3, v_isExported_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 4, v_importAll_915_);
v_s_922_ = v_reuseFailAlloc_954_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v_module_924_; uint8_t v___y_926_; uint32_t v_curr_931_; uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_923_ = lean_string_utf8_extract(v_input_776_, v_startPart_905_, v_pos_909_);
lean_dec(v_pos_909_);
v_module_924_ = l_Lean_Name_str___override(v_module_778_, v___x_923_);
v_curr_931_ = lean_string_utf8_get(v_input_776_, v_i_920_);
v___x_932_ = 46;
v___x_933_ = lean_uint32_dec_eq(v_curr_931_, v___x_932_);
if (v___x_933_ == 0)
{
v___y_926_ = v___x_933_;
goto v___jp_925_;
}
else
{
lean_object* v_i_934_; uint8_t v___x_935_; 
v_i_934_ = lean_string_utf8_next(v_input_776_, v_i_920_);
v___x_935_ = lean_string_utf8_at_end(v_input_776_, v_i_934_);
if (v___x_935_ == 0)
{
uint32_t v_curr_936_; uint8_t v___y_938_; uint8_t v___y_941_; uint32_t v___x_950_; uint8_t v___x_951_; 
v_curr_936_ = lean_string_utf8_get_fast(v_input_776_, v_i_934_);
lean_dec(v_i_934_);
v___x_950_ = 65;
v___x_951_ = lean_uint32_dec_le(v___x_950_, v_curr_936_);
if (v___x_951_ == 0)
{
goto v___jp_945_;
}
else
{
uint32_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = 90;
v___x_953_ = lean_uint32_dec_le(v_curr_936_, v___x_952_);
if (v___x_953_ == 0)
{
goto v___jp_945_;
}
else
{
v___y_926_ = v___x_933_;
goto v___jp_925_;
}
}
v___jp_937_:
{
if (v___y_938_ == 0)
{
uint8_t v___x_939_; 
v___x_939_ = lean_uint32_dec_eq(v_curr_936_, v___x_809_);
v___y_926_ = v___x_939_;
goto v___jp_925_;
}
else
{
v___y_926_ = v___x_933_;
goto v___jp_925_;
}
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 95;
v___x_943_ = lean_uint32_dec_eq(v_curr_936_, v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_isLetterLike(v_curr_936_);
v___y_938_ = v___x_944_;
goto v___jp_937_;
}
else
{
v___y_938_ = v___x_943_;
goto v___jp_937_;
}
}
else
{
v___y_926_ = v___x_933_;
goto v___jp_925_;
}
}
v___jp_945_:
{
uint32_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = 97;
v___x_947_ = lean_uint32_dec_le(v___x_946_, v_curr_936_);
if (v___x_947_ == 0)
{
v___y_941_ = v___x_947_;
goto v___jp_940_;
}
else
{
uint32_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = 122;
v___x_949_ = lean_uint32_dec_le(v_curr_936_, v___x_948_);
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
}
}
else
{
lean_dec(v_i_934_);
v___y_926_ = v___x_919_;
goto v___jp_925_;
}
}
v___jp_925_:
{
if (v___y_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v_error_x3f_911_);
lean_dec_ref(v_imports_908_);
v___x_927_ = lean_apply_3(v_finalize_777_, v_module_924_, v_input_776_, v_s_922_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v_s_929_; 
lean_dec_ref(v_s_922_);
v___x_928_ = lean_string_utf8_next(v_input_776_, v_i_920_);
v_s_929_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_929_, 0, v_imports_908_);
lean_ctor_set(v_s_929_, 1, v___x_928_);
lean_ctor_set(v_s_929_, 2, v_error_x3f_911_);
lean_ctor_set_uint8(v_s_929_, sizeof(void*)*3, v_badModifier_910_);
lean_ctor_set_uint8(v_s_929_, sizeof(void*)*3 + 1, v_isModule_912_);
lean_ctor_set_uint8(v_s_929_, sizeof(void*)*3 + 2, v_isMeta_913_);
lean_ctor_set_uint8(v_s_929_, sizeof(void*)*3 + 3, v_isExported_914_);
lean_ctor_set_uint8(v_s_929_, sizeof(void*)*3 + 4, v_importAll_915_);
v_module_778_ = v_module_924_;
v_s_779_ = v_s_929_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_957_; 
lean_dec(v_error_x3f_911_);
lean_dec(v_module_778_);
lean_dec_ref(v_finalize_777_);
lean_dec_ref(v_input_776_);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 2, v___x_955_);
v___x_957_ = v___x_917_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_imports_908_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_pos_909_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v___x_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3, v_badModifier_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3 + 1, v_isModule_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3 + 2, v_isMeta_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3 + 3, v_isExported_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3 + 4, v_importAll_915_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
v___jp_810_:
{
if (v___y_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = lean_uint32_dec_eq(v___y_813_, v___x_809_);
v___y_781_ = v___y_812_;
v___y_782_ = v___y_811_;
v___y_783_ = v___y_816_;
v___y_784_ = v___y_815_;
v___y_785_ = v___y_814_;
v___y_786_ = v___y_817_;
v___y_787_ = v___y_818_;
v___y_788_ = v___y_819_;
v___y_789_ = v___y_822_;
v___y_790_ = v___y_821_;
v___y_791_ = v___x_824_;
goto v___jp_780_;
}
else
{
v___y_781_ = v___y_812_;
v___y_782_ = v___y_811_;
v___y_783_ = v___y_816_;
v___y_784_ = v___y_815_;
v___y_785_ = v___y_814_;
v___y_786_ = v___y_817_;
v___y_787_ = v___y_818_;
v___y_788_ = v___y_819_;
v___y_789_ = v___y_822_;
v___y_790_ = v___y_821_;
v___y_791_ = v___y_820_;
goto v___jp_780_;
}
}
v___jp_825_:
{
if (v___y_838_ == 0)
{
uint32_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 95;
v___x_840_ = lean_uint32_dec_eq(v___y_828_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_isLetterLike(v___y_828_);
v___y_811_ = v___y_827_;
v___y_812_ = v___y_826_;
v___y_813_ = v___y_828_;
v___y_814_ = v___y_831_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_829_;
v___y_817_ = v___y_832_;
v___y_818_ = v___y_833_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_836_;
v___y_822_ = v___y_835_;
v___y_823_ = v___x_841_;
goto v___jp_810_;
}
else
{
v___y_811_ = v___y_827_;
v___y_812_ = v___y_826_;
v___y_813_ = v___y_828_;
v___y_814_ = v___y_831_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_829_;
v___y_817_ = v___y_832_;
v___y_818_ = v___y_833_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_836_;
v___y_822_ = v___y_835_;
v___y_823_ = v___x_840_;
goto v___jp_810_;
}
}
else
{
v___y_781_ = v___y_826_;
v___y_782_ = v___y_827_;
v___y_783_ = v___y_829_;
v___y_784_ = v___y_830_;
v___y_785_ = v___y_831_;
v___y_786_ = v___y_832_;
v___y_787_ = v___y_833_;
v___y_788_ = v___y_834_;
v___y_789_ = v___y_835_;
v___y_790_ = v___y_836_;
v___y_791_ = v___y_837_;
goto v___jp_780_;
}
}
v___jp_842_:
{
uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = 97;
v___x_856_ = lean_uint32_dec_le(v___x_855_, v___y_845_);
if (v___x_856_ == 0)
{
v___y_826_ = v___y_844_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_845_;
v___y_829_ = v___y_848_;
v___y_830_ = v___y_847_;
v___y_831_ = v___y_846_;
v___y_832_ = v___y_849_;
v___y_833_ = v___y_850_;
v___y_834_ = v___y_851_;
v___y_835_ = v___y_854_;
v___y_836_ = v___y_853_;
v___y_837_ = v___y_852_;
v___y_838_ = v___x_856_;
goto v___jp_825_;
}
else
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 122;
v___x_858_ = lean_uint32_dec_le(v___y_845_, v___x_857_);
v___y_826_ = v___y_844_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_845_;
v___y_829_ = v___y_848_;
v___y_830_ = v___y_847_;
v___y_831_ = v___y_846_;
v___y_832_ = v___y_849_;
v___y_833_ = v___y_850_;
v___y_834_ = v___y_851_;
v___y_835_ = v___y_854_;
v___y_836_ = v___y_853_;
v___y_837_ = v___y_852_;
v___y_838_ = v___x_858_;
goto v___jp_825_;
}
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_string_utf8_next_fast(v_input_776_, v_pos_797_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_862_);
v___x_864_ = v___x_806_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_imports_796_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_error_x3f_799_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*3, v_badModifier_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*3 + 1, v_isModule_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*3 + 2, v_isMeta_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*3 + 3, v_isExported_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*3 + 4, v_importAll_803_);
v___x_864_ = v_reuseFailAlloc_886_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v_s_865_; lean_object* v_imports_866_; lean_object* v_pos_867_; uint8_t v_badModifier_868_; lean_object* v_error_x3f_869_; uint8_t v_isModule_870_; uint8_t v_isMeta_871_; uint8_t v_isExported_872_; uint8_t v_importAll_873_; lean_object* v___x_874_; lean_object* v_module_875_; uint32_t v_curr_876_; uint32_t v___x_877_; uint8_t v___x_878_; 
v_s_865_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_861_, v_input_776_, v___x_864_);
v_imports_866_ = lean_ctor_get(v_s_865_, 0);
lean_inc_ref(v_imports_866_);
v_pos_867_ = lean_ctor_get(v_s_865_, 1);
lean_inc(v_pos_867_);
v_badModifier_868_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*3);
v_error_x3f_869_ = lean_ctor_get(v_s_865_, 2);
lean_inc(v_error_x3f_869_);
v_isModule_870_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*3 + 1);
v_isMeta_871_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*3 + 2);
v_isExported_872_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*3 + 3);
v_importAll_873_ = lean_ctor_get_uint8(v_s_865_, sizeof(void*)*3 + 4);
v___x_874_ = lean_string_utf8_extract(v_input_776_, v_pos_797_, v_pos_867_);
lean_dec(v_pos_797_);
v_module_875_ = l_Lean_Name_str___override(v_module_778_, v___x_874_);
v_curr_876_ = lean_string_utf8_get(v_input_776_, v_pos_867_);
v___x_877_ = 46;
v___x_878_ = lean_uint32_dec_eq(v_curr_876_, v___x_877_);
if (v___x_878_ == 0)
{
v___y_781_ = v_imports_866_;
v___y_782_ = v_s_865_;
v___y_783_ = v_importAll_873_;
v___y_784_ = v_isMeta_871_;
v___y_785_ = v_isModule_870_;
v___y_786_ = v_error_x3f_869_;
v___y_787_ = v_isExported_872_;
v___y_788_ = v_badModifier_868_;
v___y_789_ = v_pos_867_;
v___y_790_ = v_module_875_;
v___y_791_ = v___x_878_;
goto v___jp_780_;
}
else
{
lean_object* v_i_879_; uint8_t v___x_880_; 
v_i_879_ = lean_string_utf8_next(v_input_776_, v_pos_867_);
v___x_880_ = lean_string_utf8_at_end(v_input_776_, v_i_879_);
if (v___x_880_ == 0)
{
uint32_t v_curr_881_; uint32_t v___x_882_; uint8_t v___x_883_; 
v_curr_881_ = lean_string_utf8_get_fast(v_input_776_, v_i_879_);
lean_dec(v_i_879_);
v___x_882_ = 65;
v___x_883_ = lean_uint32_dec_le(v___x_882_, v_curr_881_);
if (v___x_883_ == 0)
{
v___y_843_ = v_s_865_;
v___y_844_ = v_imports_866_;
v___y_845_ = v_curr_881_;
v___y_846_ = v_isModule_870_;
v___y_847_ = v_isMeta_871_;
v___y_848_ = v_importAll_873_;
v___y_849_ = v_error_x3f_869_;
v___y_850_ = v_isExported_872_;
v___y_851_ = v_badModifier_868_;
v___y_852_ = v___x_878_;
v___y_853_ = v_module_875_;
v___y_854_ = v_pos_867_;
goto v___jp_842_;
}
else
{
uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = 90;
v___x_885_ = lean_uint32_dec_le(v_curr_881_, v___x_884_);
if (v___x_885_ == 0)
{
v___y_843_ = v_s_865_;
v___y_844_ = v_imports_866_;
v___y_845_ = v_curr_881_;
v___y_846_ = v_isModule_870_;
v___y_847_ = v_isMeta_871_;
v___y_848_ = v_importAll_873_;
v___y_849_ = v_error_x3f_869_;
v___y_850_ = v_isExported_872_;
v___y_851_ = v_badModifier_868_;
v___y_852_ = v___x_878_;
v___y_853_ = v_module_875_;
v___y_854_ = v_pos_867_;
goto v___jp_842_;
}
else
{
v___y_781_ = v_imports_866_;
v___y_782_ = v_s_865_;
v___y_783_ = v_importAll_873_;
v___y_784_ = v_isMeta_871_;
v___y_785_ = v_isModule_870_;
v___y_786_ = v_error_x3f_869_;
v___y_787_ = v_isExported_872_;
v___y_788_ = v_badModifier_868_;
v___y_789_ = v_pos_867_;
v___y_790_ = v_module_875_;
v___y_791_ = v___x_878_;
goto v___jp_780_;
}
}
}
else
{
lean_dec(v_i_879_);
v___y_781_ = v_imports_866_;
v___y_782_ = v_s_865_;
v___y_783_ = v_importAll_873_;
v___y_784_ = v_isMeta_871_;
v___y_785_ = v_isModule_870_;
v___y_786_ = v_error_x3f_869_;
v___y_787_ = v_isExported_872_;
v___y_788_ = v_badModifier_868_;
v___y_789_ = v_pos_867_;
v___y_790_ = v_module_875_;
v___y_791_ = v___x_859_;
goto v___jp_780_;
}
}
}
}
v___jp_887_:
{
if (v___y_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_del_object(v___x_806_);
lean_dec(v_error_x3f_799_);
lean_dec(v_module_778_);
lean_dec_ref(v_finalize_777_);
lean_dec_ref(v_input_776_);
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_890_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_890_, 0, v_imports_796_);
lean_ctor_set(v___x_890_, 1, v_pos_797_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*3, v_badModifier_798_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*3 + 1, v_isModule_800_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*3 + 2, v_isMeta_801_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*3 + 3, v_isExported_802_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*3 + 4, v_importAll_803_);
return v___x_890_;
}
else
{
v___y_861_ = v___y_888_;
goto v___jp_860_;
}
}
v___jp_891_:
{
if (v___y_892_ == 0)
{
uint32_t v___x_893_; uint8_t v___x_894_; 
v___x_893_ = 95;
v___x_894_ = lean_uint32_dec_eq(v_curr_808_, v___x_893_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_isLetterLike(v_curr_808_);
v___y_888_ = v___x_895_;
goto v___jp_887_;
}
else
{
v___y_888_ = v___x_894_;
goto v___jp_887_;
}
}
else
{
v___y_861_ = v___y_892_;
goto v___jp_860_;
}
}
v___jp_896_:
{
uint32_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = 97;
v___x_898_ = lean_uint32_dec_le(v___x_897_, v_curr_808_);
if (v___x_898_ == 0)
{
v___y_892_ = v___x_898_;
goto v___jp_891_;
}
else
{
uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = 122;
v___x_900_ = lean_uint32_dec_le(v_curr_808_, v___x_899_);
v___y_892_ = v___x_900_;
goto v___jp_891_;
}
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_module_778_);
lean_dec_ref(v_finalize_777_);
lean_dec_ref(v_input_776_);
v___x_964_ = l_Lean_ParseImports_State_mkEOIError(v_s_779_);
return v___x_964_;
}
v___jp_780_:
{
if (v___y_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___y_789_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_781_);
v___x_792_ = lean_apply_3(v_finalize_777_, v___y_790_, v_input_776_, v___y_782_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v_s_794_; 
lean_dec_ref(v___y_782_);
v___x_793_ = lean_string_utf8_next(v_input_776_, v___y_789_);
lean_dec(v___y_789_);
v_s_794_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_794_, 0, v___y_781_);
lean_ctor_set(v_s_794_, 1, v___x_793_);
lean_ctor_set(v_s_794_, 2, v___y_786_);
lean_ctor_set_uint8(v_s_794_, sizeof(void*)*3, v___y_788_);
lean_ctor_set_uint8(v_s_794_, sizeof(void*)*3 + 1, v___y_785_);
lean_ctor_set_uint8(v_s_794_, sizeof(void*)*3 + 2, v___y_784_);
lean_ctor_set_uint8(v_s_794_, sizeof(void*)*3 + 3, v___y_787_);
lean_ctor_set_uint8(v_s_794_, sizeof(void*)*3 + 4, v___y_783_);
v_module_778_ = v___y_790_;
v_s_779_ = v_s_794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_965_, lean_object* v_input_966_, lean_object* v_s_967_){
_start:
{
uint8_t v_isMeta_968_; uint8_t v_isExported_969_; uint8_t v_importAll_970_; lean_object* v_imp_971_; lean_object* v___x_972_; lean_object* v_s_973_; lean_object* v_imports_974_; lean_object* v_pos_975_; uint8_t v_badModifier_976_; lean_object* v_error_x3f_977_; uint8_t v_isModule_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_987_; 
v_isMeta_968_ = lean_ctor_get_uint8(v_s_967_, sizeof(void*)*3 + 2);
v_isExported_969_ = lean_ctor_get_uint8(v_s_967_, sizeof(void*)*3 + 3);
v_importAll_970_ = lean_ctor_get_uint8(v_s_967_, sizeof(void*)*3 + 4);
v_imp_971_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_971_, 0, v_module_965_);
lean_ctor_set_uint8(v_imp_971_, sizeof(void*)*1, v_importAll_970_);
lean_ctor_set_uint8(v_imp_971_, sizeof(void*)*1 + 1, v_isExported_969_);
lean_ctor_set_uint8(v_imp_971_, sizeof(void*)*1 + 2, v_isMeta_968_);
v___x_972_ = l_Lean_ParseImports_State_pushImport(v_imp_971_, v_s_967_);
v_s_973_ = l_Lean_ParseImports_whitespace(v_input_966_, v___x_972_);
v_imports_974_ = lean_ctor_get(v_s_973_, 0);
v_pos_975_ = lean_ctor_get(v_s_973_, 1);
v_badModifier_976_ = lean_ctor_get_uint8(v_s_973_, sizeof(void*)*3);
v_error_x3f_977_ = lean_ctor_get(v_s_973_, 2);
v_isModule_978_ = lean_ctor_get_uint8(v_s_973_, sizeof(void*)*3 + 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_s_973_);
if (v_isSharedCheck_987_ == 0)
{
v___x_980_ = v_s_973_;
v_isShared_981_ = v_isSharedCheck_987_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_error_x3f_977_);
lean_inc(v_pos_975_);
lean_inc(v_imports_974_);
lean_dec(v_s_973_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_987_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
uint8_t v___x_982_; uint8_t v___x_983_; lean_object* v___x_985_; 
v___x_982_ = 0;
v___x_983_ = lean_bool_not(v_isModule_978_);
if (v_isShared_981_ == 0)
{
v___x_985_ = v___x_980_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_imports_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_pos_975_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_error_x3f_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*3, v_badModifier_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*3 + 1, v_isModule_978_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*3 + 2, v___x_982_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*3 + 3, v___x_983_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*3 + 4, v___x_982_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_988_, lean_object* v_input_989_, lean_object* v_s_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_988_, v_input_989_, v_s_990_);
lean_dec_ref(v_input_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_993_, lean_object* v_s_994_){
_start:
{
lean_object* v_finalize_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_finalize_995_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_996_ = lean_box(0);
v___x_997_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_993_, v_finalize_995_, v___x_996_, v_s_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_998_, lean_object* v_input_999_, lean_object* v_s_1000_){
_start:
{
lean_object* v_pos_1001_; lean_object* v_s_1002_; lean_object* v_error_x3f_1003_; 
v_pos_1001_ = lean_ctor_get(v_s_1000_, 1);
lean_inc(v_pos_1001_);
v_s_1002_ = lean_apply_2(v_p_998_, v_input_999_, v_s_1000_);
v_error_x3f_1003_ = lean_ctor_get(v_s_1002_, 2);
lean_inc(v_error_x3f_1003_);
if (lean_obj_tag(v_error_x3f_1003_) == 1)
{
lean_object* v_imports_1004_; uint8_t v_badModifier_1005_; uint8_t v_isModule_1006_; uint8_t v_isMeta_1007_; uint8_t v_isExported_1008_; uint8_t v_importAll_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_imports_1004_ = lean_ctor_get(v_s_1002_, 0);
v_badModifier_1005_ = lean_ctor_get_uint8(v_s_1002_, sizeof(void*)*3);
v_isModule_1006_ = lean_ctor_get_uint8(v_s_1002_, sizeof(void*)*3 + 1);
v_isMeta_1007_ = lean_ctor_get_uint8(v_s_1002_, sizeof(void*)*3 + 2);
v_isExported_1008_ = lean_ctor_get_uint8(v_s_1002_, sizeof(void*)*3 + 3);
v_importAll_1009_ = lean_ctor_get_uint8(v_s_1002_, sizeof(void*)*3 + 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_s_1002_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1017_ = lean_ctor_get(v_s_1002_, 2);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_s_1002_, 1);
lean_dec(v_unused_1018_);
v___x_1011_ = v_s_1002_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_imports_1004_);
lean_dec(v_s_1002_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v_pos_1001_);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_imports_1004_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_pos_1001_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_error_x3f_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3, v_badModifier_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3 + 1, v_isModule_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3 + 2, v_isMeta_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3 + 3, v_isExported_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3 + 4, v_importAll_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_dec(v_error_x3f_1003_);
lean_dec(v_pos_1001_);
return v_s_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_1022_, lean_object* v_input_1023_, lean_object* v_s_1024_){
_start:
{
lean_object* v_pos_1025_; lean_object* v_s_1026_; lean_object* v_error_x3f_1027_; 
v_pos_1025_ = lean_ctor_get(v_s_1024_, 1);
lean_inc(v_pos_1025_);
lean_inc_ref(v_p_1022_);
lean_inc_ref(v_input_1023_);
v_s_1026_ = lean_apply_2(v_p_1022_, v_input_1023_, v_s_1024_);
v_error_x3f_1027_ = lean_ctor_get(v_s_1026_, 2);
lean_inc(v_error_x3f_1027_);
if (lean_obj_tag(v_error_x3f_1027_) == 1)
{
lean_object* v_imports_1028_; lean_object* v_pos_1029_; uint8_t v_isModule_1030_; uint8_t v_isMeta_1031_; uint8_t v_isExported_1032_; uint8_t v_importAll_1033_; uint8_t v___x_1034_; 
lean_dec_ref_known(v_error_x3f_1027_, 1);
lean_dec_ref(v_input_1023_);
lean_dec_ref(v_p_1022_);
v_imports_1028_ = lean_ctor_get(v_s_1026_, 0);
lean_inc_ref(v_imports_1028_);
v_pos_1029_ = lean_ctor_get(v_s_1026_, 1);
lean_inc(v_pos_1029_);
v_isModule_1030_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 1);
v_isMeta_1031_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 2);
v_isExported_1032_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 3);
v_importAll_1033_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 4);
v___x_1034_ = lean_nat_dec_eq(v_pos_1029_, v_pos_1025_);
lean_dec(v_pos_1025_);
if (v___x_1034_ == 0)
{
lean_dec(v_pos_1029_);
lean_dec_ref(v_imports_1028_);
return v_s_1026_;
}
else
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v_s_1026_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; lean_object* v_unused_1046_; 
v_unused_1044_ = lean_ctor_get(v_s_1026_, 2);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_s_1026_, 1);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_s_1026_, 0);
lean_dec(v_unused_1046_);
v___x_1036_ = v_s_1026_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_s_1026_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = 0;
v___x_1039_ = lean_box(0);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 2, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_imports_1028_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_pos_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*3 + 1, v_isModule_1030_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*3 + 2, v_isMeta_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*3 + 3, v_isExported_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*3 + 4, v_importAll_1033_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*3, v___x_1038_);
return v___x_1041_;
}
}
}
}
else
{
uint8_t v_badModifier_1047_; 
lean_dec(v_error_x3f_1027_);
v_badModifier_1047_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3);
if (v_badModifier_1047_ == 0)
{
lean_dec(v_pos_1025_);
v_s_1024_ = v_s_1026_;
goto _start;
}
else
{
lean_object* v_imports_1049_; uint8_t v_isModule_1050_; uint8_t v_isMeta_1051_; uint8_t v_isExported_1052_; uint8_t v_importAll_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_input_1023_);
lean_dec_ref(v_p_1022_);
v_imports_1049_ = lean_ctor_get(v_s_1026_, 0);
v_isModule_1050_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 1);
v_isMeta_1051_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 2);
v_isExported_1052_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 3);
v_importAll_1053_ = lean_ctor_get_uint8(v_s_1026_, sizeof(void*)*3 + 4);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_s_1026_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; lean_object* v_unused_1064_; 
v_unused_1063_ = lean_ctor_get(v_s_1026_, 2);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_s_1026_, 1);
lean_dec(v_unused_1064_);
v___x_1055_ = v_s_1026_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_imports_1049_);
lean_dec(v_s_1026_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = 0;
v___x_1058_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1058_);
lean_ctor_set(v___x_1055_, 1, v_pos_1025_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_imports_1049_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_pos_1025_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___x_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3 + 1, v_isModule_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3 + 2, v_isMeta_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3 + 3, v_isExported_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3 + 4, v_importAll_1053_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*3, v___x_1057_);
return v___x_1060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1065_, lean_object* v_s_1066_){
_start:
{
lean_object* v_imports_1067_; lean_object* v_pos_1068_; uint8_t v_badModifier_1069_; lean_object* v_error_x3f_1070_; uint8_t v_isMeta_1071_; uint8_t v_importAll_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_imports_1067_ = lean_ctor_get(v_s_1066_, 0);
v_pos_1068_ = lean_ctor_get(v_s_1066_, 1);
v_badModifier_1069_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3);
v_error_x3f_1070_ = lean_ctor_get(v_s_1066_, 2);
v_isMeta_1071_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 2);
v_importAll_1072_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_s_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v_s_1066_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_error_x3f_1070_);
lean_inc(v_pos_1068_);
lean_inc(v_imports_1067_);
lean_dec(v_s_1066_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
uint8_t v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_bool_not(v_isModule_1065_);
if (v_isShared_1075_ == 0)
{
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_imports_1067_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_pos_1068_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_error_x3f_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*3, v_badModifier_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*3 + 2, v_isMeta_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*3 + 4, v_importAll_1072_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*3 + 1, v_isModule_1065_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*3 + 3, v___x_1076_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* v_isModule_1081_, lean_object* v_s_1082_){
_start:
{
uint8_t v_isModule_boxed_1083_; lean_object* v_res_1084_; 
v_isModule_boxed_1083_ = lean_unbox(v_isModule_1081_);
v_res_1084_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_1083_, v_s_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1085_, lean_object* v_x_1086_, lean_object* v_s_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1085_, v_s_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1089_, lean_object* v_x_1090_, lean_object* v_s_1091_){
_start:
{
uint8_t v_isModule_boxed_1092_; lean_object* v_res_1093_; 
v_isModule_boxed_1092_ = lean_unbox(v_isModule_1089_);
v_res_1093_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1092_, v_x_1090_, v_s_1091_);
lean_dec_ref(v_x_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1094_){
_start:
{
lean_object* v_imports_1095_; lean_object* v_pos_1096_; uint8_t v_badModifier_1097_; lean_object* v_error_x3f_1098_; uint8_t v_isModule_1099_; uint8_t v_isMeta_1100_; uint8_t v_isExported_1101_; uint8_t v_importAll_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1113_; 
v_imports_1095_ = lean_ctor_get(v_s_1094_, 0);
v_pos_1096_ = lean_ctor_get(v_s_1094_, 1);
v_badModifier_1097_ = lean_ctor_get_uint8(v_s_1094_, sizeof(void*)*3);
v_error_x3f_1098_ = lean_ctor_get(v_s_1094_, 2);
v_isModule_1099_ = lean_ctor_get_uint8(v_s_1094_, sizeof(void*)*3 + 1);
v_isMeta_1100_ = lean_ctor_get_uint8(v_s_1094_, sizeof(void*)*3 + 2);
v_isExported_1101_ = lean_ctor_get_uint8(v_s_1094_, sizeof(void*)*3 + 3);
v_importAll_1102_ = lean_ctor_get_uint8(v_s_1094_, sizeof(void*)*3 + 4);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_s_1094_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1104_ = v_s_1094_;
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_error_x3f_1098_);
lean_inc(v_pos_1096_);
lean_inc(v_imports_1095_);
lean_dec(v_s_1094_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = 1;
if (v_isModule_1099_ == 0)
{
lean_object* v___x_1108_; 
if (v_isShared_1105_ == 0)
{
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_imports_1095_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_error_x3f_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*3 + 1, v_isModule_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*3 + 2, v_isMeta_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*3 + 3, v_isExported_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*3 + 4, v_importAll_1102_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*3, v___x_1106_);
return v___x_1108_;
}
}
else
{
lean_object* v___x_1111_; 
if (v_isShared_1105_ == 0)
{
v___x_1111_ = v___x_1104_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_imports_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_error_x3f_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3, v_badModifier_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 1, v_isModule_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 3, v_isExported_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 4, v_importAll_1102_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 2, v___x_1106_);
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1114_, lean_object* v_s_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_ParseImports_setMeta___redArg(v_s_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1117_, lean_object* v_s_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_ParseImports_setMeta(v_x_1117_, v_s_1118_);
lean_dec_ref(v_x_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1120_){
_start:
{
lean_object* v_imports_1121_; lean_object* v_pos_1122_; uint8_t v_badModifier_1123_; lean_object* v_error_x3f_1124_; uint8_t v_isModule_1125_; uint8_t v_isMeta_1126_; uint8_t v_isExported_1127_; uint8_t v_importAll_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1139_; 
v_imports_1121_ = lean_ctor_get(v_s_1120_, 0);
v_pos_1122_ = lean_ctor_get(v_s_1120_, 1);
v_badModifier_1123_ = lean_ctor_get_uint8(v_s_1120_, sizeof(void*)*3);
v_error_x3f_1124_ = lean_ctor_get(v_s_1120_, 2);
v_isModule_1125_ = lean_ctor_get_uint8(v_s_1120_, sizeof(void*)*3 + 1);
v_isMeta_1126_ = lean_ctor_get_uint8(v_s_1120_, sizeof(void*)*3 + 2);
v_isExported_1127_ = lean_ctor_get_uint8(v_s_1120_, sizeof(void*)*3 + 3);
v_importAll_1128_ = lean_ctor_get_uint8(v_s_1120_, sizeof(void*)*3 + 4);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_s_1120_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1130_ = v_s_1120_;
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_error_x3f_1124_);
lean_inc(v_pos_1122_);
lean_inc(v_imports_1121_);
lean_dec(v_s_1120_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = 1;
if (v_isModule_1125_ == 0)
{
lean_object* v___x_1134_; 
if (v_isShared_1131_ == 0)
{
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_imports_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_pos_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_error_x3f_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3 + 1, v_isModule_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3 + 2, v_isMeta_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3 + 3, v_isExported_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3 + 4, v_importAll_1128_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*3, v___x_1132_);
return v___x_1134_;
}
}
else
{
lean_object* v___x_1137_; 
if (v_isShared_1131_ == 0)
{
v___x_1137_ = v___x_1130_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_imports_1121_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_pos_1122_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_error_x3f_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3, v_badModifier_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 1, v_isModule_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 2, v_isMeta_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 4, v_importAll_1128_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*3 + 3, v___x_1132_);
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1140_, lean_object* v_s_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_ParseImports_setExported___redArg(v_s_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1143_, lean_object* v_s_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_ParseImports_setExported(v_x_1143_, v_s_1144_);
lean_dec_ref(v_x_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1146_){
_start:
{
lean_object* v_imports_1147_; lean_object* v_pos_1148_; uint8_t v_badModifier_1149_; lean_object* v_error_x3f_1150_; uint8_t v_isModule_1151_; uint8_t v_isMeta_1152_; uint8_t v_isExported_1153_; uint8_t v_importAll_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1165_; 
v_imports_1147_ = lean_ctor_get(v_s_1146_, 0);
v_pos_1148_ = lean_ctor_get(v_s_1146_, 1);
v_badModifier_1149_ = lean_ctor_get_uint8(v_s_1146_, sizeof(void*)*3);
v_error_x3f_1150_ = lean_ctor_get(v_s_1146_, 2);
v_isModule_1151_ = lean_ctor_get_uint8(v_s_1146_, sizeof(void*)*3 + 1);
v_isMeta_1152_ = lean_ctor_get_uint8(v_s_1146_, sizeof(void*)*3 + 2);
v_isExported_1153_ = lean_ctor_get_uint8(v_s_1146_, sizeof(void*)*3 + 3);
v_importAll_1154_ = lean_ctor_get_uint8(v_s_1146_, sizeof(void*)*3 + 4);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_s_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1156_ = v_s_1146_;
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_error_x3f_1150_);
lean_inc(v_pos_1148_);
lean_inc(v_imports_1147_);
lean_dec(v_s_1146_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = 1;
if (v_isModule_1151_ == 0)
{
lean_object* v___x_1160_; 
if (v_isShared_1157_ == 0)
{
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_imports_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_pos_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_error_x3f_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3 + 1, v_isModule_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3 + 2, v_isMeta_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3 + 3, v_isExported_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3 + 4, v_importAll_1154_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3, v___x_1158_);
return v___x_1160_;
}
}
else
{
lean_object* v___x_1163_; 
if (v_isShared_1157_ == 0)
{
v___x_1163_ = v___x_1156_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_imports_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_pos_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_error_x3f_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3, v_badModifier_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 1, v_isModule_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 2, v_isMeta_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 3, v_isExported_1153_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3 + 4, v___x_1158_);
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1166_, lean_object* v_s_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1169_, lean_object* v_s_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_ParseImports_setImportAll(v_x_1169_, v_s_1170_);
lean_dec_ref(v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1175_, lean_object* v_input_1176_, lean_object* v_s_1177_, lean_object* v_i_1178_, lean_object* v_j_1179_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_string_utf8_at_end(v_k_1175_, v_i_1178_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; lean_object* v_s_1183_; uint8_t v___x_1189_; 
v___x_1181_ = 1;
v___x_1189_ = lean_string_utf8_at_end(v_input_1176_, v_j_1179_);
if (v___x_1189_ == 0)
{
uint32_t v_curr_u2081_1190_; uint32_t v_curr_u2082_1191_; uint8_t v___x_1192_; uint8_t v___x_1193_; 
v_curr_u2081_1190_ = lean_string_utf8_get_fast(v_k_1175_, v_i_1178_);
v_curr_u2082_1191_ = lean_string_utf8_get_fast(v_input_1176_, v_j_1179_);
v___x_1192_ = lean_uint32_dec_eq(v_curr_u2081_1190_, v_curr_u2082_1191_);
v___x_1193_ = lean_bool_not(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_string_utf8_next_fast(v_k_1175_, v_i_1178_);
lean_dec(v_i_1178_);
v___x_1195_ = lean_string_utf8_next_fast(v_input_1176_, v_j_1179_);
lean_dec(v_j_1179_);
v_i_1178_ = v___x_1194_;
v_j_1179_ = v___x_1195_;
goto _start;
}
else
{
lean_dec(v_j_1179_);
lean_dec(v_i_1178_);
v_s_1183_ = v_s_1177_;
goto v___jp_1182_;
}
}
else
{
lean_dec(v_j_1179_);
lean_dec(v_i_1178_);
v_s_1183_ = v_s_1177_;
goto v___jp_1182_;
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1185_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*1, v___x_1180_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*1 + 1, v___x_1181_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*1 + 2, v___x_1181_);
v___x_1186_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1, v___x_1180_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1 + 1, v___x_1181_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1 + 2, v___x_1180_);
v___x_1187_ = l_Lean_ParseImports_State_pushImport(v___x_1186_, v_s_1183_);
v___x_1188_ = l_Lean_ParseImports_State_pushImport(v___x_1185_, v___x_1187_);
return v___x_1188_;
}
}
else
{
lean_object* v_imports_1197_; uint8_t v_badModifier_1198_; lean_object* v_error_x3f_1199_; uint8_t v_isModule_1200_; uint8_t v_isMeta_1201_; uint8_t v_isExported_1202_; uint8_t v_importAll_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_i_1178_);
v_imports_1197_ = lean_ctor_get(v_s_1177_, 0);
v_badModifier_1198_ = lean_ctor_get_uint8(v_s_1177_, sizeof(void*)*3);
v_error_x3f_1199_ = lean_ctor_get(v_s_1177_, 2);
v_isModule_1200_ = lean_ctor_get_uint8(v_s_1177_, sizeof(void*)*3 + 1);
v_isMeta_1201_ = lean_ctor_get_uint8(v_s_1177_, sizeof(void*)*3 + 2);
v_isExported_1202_ = lean_ctor_get_uint8(v_s_1177_, sizeof(void*)*3 + 3);
v_importAll_1203_ = lean_ctor_get_uint8(v_s_1177_, sizeof(void*)*3 + 4);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_s_1177_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_s_1177_, 1);
lean_dec(v_unused_1212_);
v___x_1205_ = v_s_1177_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_error_x3f_1199_);
lean_inc(v_imports_1197_);
lean_dec(v_s_1177_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_j_1179_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_imports_1197_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_j_1179_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_error_x3f_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3, v_badModifier_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3 + 1, v_isModule_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3 + 2, v_isMeta_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3 + 3, v_isExported_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3 + 4, v_importAll_1203_);
v___x_1208_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_ParseImports_whitespace(v_input_1176_, v___x_1208_);
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1213_, lean_object* v_input_1214_, lean_object* v_s_1215_, lean_object* v_i_1216_, lean_object* v_j_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1213_, v_input_1214_, v_s_1215_, v_i_1216_, v_j_1217_);
lean_dec_ref(v_input_1214_);
lean_dec_ref(v_k_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1222_, lean_object* v_input_1223_, lean_object* v_s_1224_, lean_object* v_i_1225_, lean_object* v_j_1226_){
_start:
{
lean_object* v_s_1228_; uint8_t v___x_1245_; 
v___x_1245_ = lean_string_utf8_at_end(v_k_1222_, v_i_1225_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_string_utf8_at_end(v_input_1223_, v_j_1226_);
if (v___x_1246_ == 0)
{
uint32_t v_curr_u2081_1247_; uint32_t v_curr_u2082_1248_; uint8_t v___x_1249_; uint8_t v___x_1250_; 
v_curr_u2081_1247_ = lean_string_utf8_get_fast(v_k_1222_, v_i_1225_);
v_curr_u2082_1248_ = lean_string_utf8_get_fast(v_input_1223_, v_j_1226_);
v___x_1249_ = lean_uint32_dec_eq(v_curr_u2081_1247_, v_curr_u2082_1248_);
v___x_1250_ = lean_bool_not(v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_string_utf8_next_fast(v_k_1222_, v_i_1225_);
lean_dec(v_i_1225_);
v___x_1252_ = lean_string_utf8_next_fast(v_input_1223_, v_j_1226_);
lean_dec(v_j_1226_);
v_i_1225_ = v___x_1251_;
v_j_1226_ = v___x_1252_;
goto _start;
}
else
{
lean_dec(v_j_1226_);
lean_dec(v_i_1225_);
v_s_1228_ = v_s_1224_;
goto v___jp_1227_;
}
}
else
{
lean_dec(v_j_1226_);
lean_dec(v_i_1225_);
v_s_1228_ = v_s_1224_;
goto v___jp_1227_;
}
}
else
{
lean_object* v_imports_1254_; uint8_t v_badModifier_1255_; lean_object* v_error_x3f_1256_; uint8_t v_isModule_1257_; uint8_t v_isMeta_1258_; uint8_t v_isExported_1259_; uint8_t v_importAll_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_i_1225_);
v_imports_1254_ = lean_ctor_get(v_s_1224_, 0);
v_badModifier_1255_ = lean_ctor_get_uint8(v_s_1224_, sizeof(void*)*3);
v_error_x3f_1256_ = lean_ctor_get(v_s_1224_, 2);
v_isModule_1257_ = lean_ctor_get_uint8(v_s_1224_, sizeof(void*)*3 + 1);
v_isMeta_1258_ = lean_ctor_get_uint8(v_s_1224_, sizeof(void*)*3 + 2);
v_isExported_1259_ = lean_ctor_get_uint8(v_s_1224_, sizeof(void*)*3 + 3);
v_importAll_1260_ = lean_ctor_get_uint8(v_s_1224_, sizeof(void*)*3 + 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_s_1224_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_s_1224_, 1);
lean_dec(v_unused_1269_);
v___x_1262_ = v_s_1224_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_error_x3f_1256_);
lean_inc(v_imports_1254_);
lean_dec(v_s_1224_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_j_1226_);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_imports_1254_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_j_1226_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_error_x3f_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3, v_badModifier_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 1, v_isModule_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 2, v_isMeta_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 3, v_isExported_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 4, v_importAll_1260_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_ParseImports_whitespace(v_input_1223_, v___x_1265_);
return v___x_1266_;
}
}
}
v___jp_1227_:
{
lean_object* v_imports_1229_; lean_object* v_pos_1230_; uint8_t v_badModifier_1231_; uint8_t v_isModule_1232_; uint8_t v_isMeta_1233_; uint8_t v_isExported_1234_; uint8_t v_importAll_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1243_; 
v_imports_1229_ = lean_ctor_get(v_s_1228_, 0);
v_pos_1230_ = lean_ctor_get(v_s_1228_, 1);
v_badModifier_1231_ = lean_ctor_get_uint8(v_s_1228_, sizeof(void*)*3);
v_isModule_1232_ = lean_ctor_get_uint8(v_s_1228_, sizeof(void*)*3 + 1);
v_isMeta_1233_ = lean_ctor_get_uint8(v_s_1228_, sizeof(void*)*3 + 2);
v_isExported_1234_ = lean_ctor_get_uint8(v_s_1228_, sizeof(void*)*3 + 3);
v_importAll_1235_ = lean_ctor_get_uint8(v_s_1228_, sizeof(void*)*3 + 4);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_s_1228_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_s_1228_, 2);
lean_dec(v_unused_1244_);
v___x_1237_ = v_s_1228_;
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_pos_1230_);
lean_inc(v_imports_1229_);
lean_dec(v_s_1228_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 2, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_imports_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_pos_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v___x_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*3, v_badModifier_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*3 + 1, v_isModule_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*3 + 2, v_isMeta_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*3 + 3, v_isExported_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*3 + 4, v_importAll_1235_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1270_, lean_object* v_input_1271_, lean_object* v_s_1272_, lean_object* v_i_1273_, lean_object* v_j_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1270_, v_input_1271_, v_s_1272_, v_i_1273_, v_j_1274_);
lean_dec_ref(v_input_1271_);
lean_dec_ref(v_k_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1276_, lean_object* v_input_1277_, lean_object* v_s_1278_, lean_object* v_i_1279_, lean_object* v_j_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_string_utf8_at_end(v_k_1276_, v_i_1279_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_string_utf8_at_end(v_input_1277_, v_j_1280_);
if (v___x_1282_ == 0)
{
uint32_t v_curr_u2081_1283_; uint32_t v_curr_u2082_1284_; uint8_t v___x_1285_; uint8_t v___x_1286_; 
v_curr_u2081_1283_ = lean_string_utf8_get_fast(v_k_1276_, v_i_1279_);
v_curr_u2082_1284_ = lean_string_utf8_get_fast(v_input_1277_, v_j_1280_);
v___x_1285_ = lean_uint32_dec_eq(v_curr_u2081_1283_, v_curr_u2082_1284_);
v___x_1286_ = lean_bool_not(v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_string_utf8_next_fast(v_k_1276_, v_i_1279_);
lean_dec(v_i_1279_);
v___x_1288_ = lean_string_utf8_next_fast(v_input_1277_, v_j_1280_);
lean_dec(v_j_1280_);
v_i_1279_ = v___x_1287_;
v_j_1280_ = v___x_1288_;
goto _start;
}
else
{
lean_dec(v_j_1280_);
lean_dec(v_i_1279_);
return v_s_1278_;
}
}
else
{
lean_dec(v_j_1280_);
lean_dec(v_i_1279_);
return v_s_1278_;
}
}
else
{
lean_object* v_imports_1290_; uint8_t v_badModifier_1291_; lean_object* v_error_x3f_1292_; uint8_t v_isModule_1293_; uint8_t v_isMeta_1294_; uint8_t v_isExported_1295_; uint8_t v_importAll_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_i_1279_);
v_imports_1290_ = lean_ctor_get(v_s_1278_, 0);
v_badModifier_1291_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3);
v_error_x3f_1292_ = lean_ctor_get(v_s_1278_, 2);
v_isModule_1293_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 1);
v_isMeta_1294_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 2);
v_isExported_1295_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 3);
v_importAll_1296_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 4);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_s_1278_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_s_1278_, 1);
lean_dec(v_unused_1306_);
v___x_1298_ = v_s_1278_;
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_error_x3f_1292_);
lean_inc(v_imports_1290_);
lean_dec(v_s_1278_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v_j_1280_);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_imports_1290_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_j_1280_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_error_x3f_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*3, v_badModifier_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*3 + 1, v_isModule_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*3 + 2, v_isMeta_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*3 + 3, v_isExported_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1304_, sizeof(void*)*3 + 4, v_importAll_1296_);
v___x_1301_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = l_Lean_ParseImports_whitespace(v_input_1277_, v___x_1301_);
v___x_1303_ = l_Lean_ParseImports_setImportAll___redArg(v___x_1302_);
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* v_k_1307_, lean_object* v_input_1308_, lean_object* v_s_1309_, lean_object* v_i_1310_, lean_object* v_j_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_1307_, v_input_1308_, v_s_1309_, v_i_1310_, v_j_1311_);
lean_dec_ref(v_input_1308_);
lean_dec_ref(v_k_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* v_k_1313_, lean_object* v_input_1314_, lean_object* v_s_1315_, lean_object* v_i_1316_, lean_object* v_j_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_string_utf8_at_end(v_k_1313_, v_i_1316_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_string_utf8_at_end(v_input_1314_, v_j_1317_);
if (v___x_1319_ == 0)
{
uint32_t v_curr_u2081_1320_; uint32_t v_curr_u2082_1321_; uint8_t v___x_1322_; uint8_t v___x_1323_; 
v_curr_u2081_1320_ = lean_string_utf8_get_fast(v_k_1313_, v_i_1316_);
v_curr_u2082_1321_ = lean_string_utf8_get_fast(v_input_1314_, v_j_1317_);
v___x_1322_ = lean_uint32_dec_eq(v_curr_u2081_1320_, v_curr_u2082_1321_);
v___x_1323_ = lean_bool_not(v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_string_utf8_next_fast(v_k_1313_, v_i_1316_);
lean_dec(v_i_1316_);
v___x_1325_ = lean_string_utf8_next_fast(v_input_1314_, v_j_1317_);
lean_dec(v_j_1317_);
v_i_1316_ = v___x_1324_;
v_j_1317_ = v___x_1325_;
goto _start;
}
else
{
lean_dec(v_j_1317_);
lean_dec(v_i_1316_);
return v_s_1315_;
}
}
else
{
lean_dec(v_j_1317_);
lean_dec(v_i_1316_);
return v_s_1315_;
}
}
else
{
lean_object* v_imports_1327_; uint8_t v_badModifier_1328_; lean_object* v_error_x3f_1329_; uint8_t v_isModule_1330_; uint8_t v_isMeta_1331_; uint8_t v_isExported_1332_; uint8_t v_importAll_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_i_1316_);
v_imports_1327_ = lean_ctor_get(v_s_1315_, 0);
v_badModifier_1328_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3);
v_error_x3f_1329_ = lean_ctor_get(v_s_1315_, 2);
v_isModule_1330_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 1);
v_isMeta_1331_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 2);
v_isExported_1332_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 3);
v_importAll_1333_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 4);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_s_1315_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_s_1315_, 1);
lean_dec(v_unused_1343_);
v___x_1335_ = v_s_1315_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_error_x3f_1329_);
lean_inc(v_imports_1327_);
lean_dec(v_s_1315_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v_j_1317_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_imports_1327_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_j_1317_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_error_x3f_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*3, v_badModifier_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*3 + 1, v_isModule_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*3 + 2, v_isMeta_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*3 + 3, v_isExported_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*3 + 4, v_importAll_1333_);
v___x_1338_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = l_Lean_ParseImports_whitespace(v_input_1314_, v___x_1338_);
v___x_1340_ = l_Lean_ParseImports_setExported___redArg(v___x_1339_);
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1344_, lean_object* v_input_1345_, lean_object* v_s_1346_, lean_object* v_i_1347_, lean_object* v_j_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1344_, v_input_1345_, v_s_1346_, v_i_1347_, v_j_1348_);
lean_dec_ref(v_input_1345_);
lean_dec_ref(v_k_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1350_, lean_object* v_input_1351_, lean_object* v_s_1352_, lean_object* v_i_1353_, lean_object* v_j_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_string_utf8_at_end(v_k_1350_, v_i_1353_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_string_utf8_at_end(v_input_1351_, v_j_1354_);
if (v___x_1356_ == 0)
{
uint32_t v_curr_u2081_1357_; uint32_t v_curr_u2082_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; 
v_curr_u2081_1357_ = lean_string_utf8_get_fast(v_k_1350_, v_i_1353_);
v_curr_u2082_1358_ = lean_string_utf8_get_fast(v_input_1351_, v_j_1354_);
v___x_1359_ = lean_uint32_dec_eq(v_curr_u2081_1357_, v_curr_u2082_1358_);
v___x_1360_ = lean_bool_not(v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_string_utf8_next_fast(v_k_1350_, v_i_1353_);
lean_dec(v_i_1353_);
v___x_1362_ = lean_string_utf8_next_fast(v_input_1351_, v_j_1354_);
lean_dec(v_j_1354_);
v_i_1353_ = v___x_1361_;
v_j_1354_ = v___x_1362_;
goto _start;
}
else
{
lean_dec(v_j_1354_);
lean_dec(v_i_1353_);
return v_s_1352_;
}
}
else
{
lean_dec(v_j_1354_);
lean_dec(v_i_1353_);
return v_s_1352_;
}
}
else
{
lean_object* v_imports_1364_; uint8_t v_badModifier_1365_; lean_object* v_error_x3f_1366_; uint8_t v_isModule_1367_; uint8_t v_isMeta_1368_; uint8_t v_isExported_1369_; uint8_t v_importAll_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_i_1353_);
v_imports_1364_ = lean_ctor_get(v_s_1352_, 0);
v_badModifier_1365_ = lean_ctor_get_uint8(v_s_1352_, sizeof(void*)*3);
v_error_x3f_1366_ = lean_ctor_get(v_s_1352_, 2);
v_isModule_1367_ = lean_ctor_get_uint8(v_s_1352_, sizeof(void*)*3 + 1);
v_isMeta_1368_ = lean_ctor_get_uint8(v_s_1352_, sizeof(void*)*3 + 2);
v_isExported_1369_ = lean_ctor_get_uint8(v_s_1352_, sizeof(void*)*3 + 3);
v_importAll_1370_ = lean_ctor_get_uint8(v_s_1352_, sizeof(void*)*3 + 4);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_s_1352_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_s_1352_, 1);
lean_dec(v_unused_1380_);
v___x_1372_ = v_s_1352_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_error_x3f_1366_);
lean_inc(v_imports_1364_);
lean_dec(v_s_1352_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_j_1354_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_imports_1364_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_j_1354_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_error_x3f_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*3, v_badModifier_1365_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*3 + 1, v_isModule_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*3 + 2, v_isMeta_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*3 + 3, v_isExported_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1378_, sizeof(void*)*3 + 4, v_importAll_1370_);
v___x_1375_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = l_Lean_ParseImports_whitespace(v_input_1351_, v___x_1375_);
v___x_1377_ = l_Lean_ParseImports_setMeta___redArg(v___x_1376_);
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1381_, lean_object* v_input_1382_, lean_object* v_s_1383_, lean_object* v_i_1384_, lean_object* v_j_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1381_, v_input_1382_, v_s_1383_, v_i_1384_, v_j_1385_);
lean_dec_ref(v_input_1382_);
lean_dec_ref(v_k_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1391_, lean_object* v_s_1392_){
_start:
{
lean_object* v_pos_1393_; lean_object* v___y_1395_; lean_object* v_imports_1396_; lean_object* v_pos_1397_; uint8_t v_isModule_1398_; uint8_t v_isMeta_1399_; uint8_t v_isExported_1400_; uint8_t v_importAll_1401_; lean_object* v___y_1407_; lean_object* v___y_1434_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_error_x3f_1466_; 
v_pos_1393_ = lean_ctor_get(v_s_1392_, 1);
lean_inc_n(v_pos_1393_, 2);
v___x_1463_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1463_, v_input_1391_, v_s_1392_, v___x_1464_, v_pos_1393_);
v_error_x3f_1466_ = lean_ctor_get(v___x_1465_, 2);
lean_inc(v_error_x3f_1466_);
if (lean_obj_tag(v_error_x3f_1466_) == 1)
{
lean_dec_ref_known(v_error_x3f_1466_, 1);
v___y_1434_ = v___x_1465_;
goto v___jp_1433_;
}
else
{
lean_object* v_pos_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_error_x3f_1470_; 
lean_dec(v_error_x3f_1466_);
v_pos_1467_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_pos_1467_);
v___x_1468_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1469_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1468_, v_input_1391_, v___x_1465_, v___x_1464_, v_pos_1467_);
v_error_x3f_1470_ = lean_ctor_get(v___x_1469_, 2);
lean_inc(v_error_x3f_1470_);
if (lean_obj_tag(v_error_x3f_1470_) == 1)
{
lean_dec_ref_known(v_error_x3f_1470_, 1);
v___y_1434_ = v___x_1469_;
goto v___jp_1433_;
}
else
{
lean_object* v_pos_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_error_x3f_1470_);
v_pos_1471_ = lean_ctor_get(v___x_1469_, 1);
lean_inc(v_pos_1471_);
v___x_1472_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1473_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1472_, v_input_1391_, v___x_1469_, v___x_1464_, v_pos_1471_);
v___y_1434_ = v___x_1473_;
goto v___jp_1433_;
}
}
v___jp_1394_:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_eq(v_pos_1397_, v_pos_1393_);
lean_dec(v_pos_1393_);
if (v___x_1402_ == 0)
{
lean_dec(v_pos_1397_);
lean_dec_ref(v_imports_1396_);
return v___y_1395_;
}
else
{
uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v___y_1395_);
v___x_1403_ = 0;
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1405_, 0, v_imports_1396_);
lean_ctor_set(v___x_1405_, 1, v_pos_1397_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3, v___x_1403_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3 + 1, v_isModule_1398_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3 + 2, v_isMeta_1399_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3 + 3, v_isExported_1400_);
lean_ctor_set_uint8(v___x_1405_, sizeof(void*)*3 + 4, v_importAll_1401_);
return v___x_1405_;
}
}
v___jp_1406_:
{
lean_object* v_error_x3f_1408_; 
v_error_x3f_1408_ = lean_ctor_get(v___y_1407_, 2);
if (lean_obj_tag(v_error_x3f_1408_) == 1)
{
lean_object* v_imports_1409_; lean_object* v_pos_1410_; uint8_t v_isModule_1411_; uint8_t v_isMeta_1412_; uint8_t v_isExported_1413_; uint8_t v_importAll_1414_; 
lean_dec_ref(v_input_1391_);
v_imports_1409_ = lean_ctor_get(v___y_1407_, 0);
lean_inc_ref(v_imports_1409_);
v_pos_1410_ = lean_ctor_get(v___y_1407_, 1);
lean_inc(v_pos_1410_);
v_isModule_1411_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 1);
v_isMeta_1412_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 2);
v_isExported_1413_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 3);
v_importAll_1414_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 4);
v___y_1395_ = v___y_1407_;
v_imports_1396_ = v_imports_1409_;
v_pos_1397_ = v_pos_1410_;
v_isModule_1398_ = v_isModule_1411_;
v_isMeta_1399_ = v_isMeta_1412_;
v_isExported_1400_ = v_isExported_1413_;
v_importAll_1401_ = v_importAll_1414_;
goto v___jp_1394_;
}
else
{
uint8_t v_badModifier_1415_; 
v_badModifier_1415_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3);
if (v_badModifier_1415_ == 0)
{
lean_dec(v_pos_1393_);
v_s_1392_ = v___y_1407_;
goto _start;
}
else
{
lean_object* v_imports_1417_; uint8_t v_isModule_1418_; uint8_t v_isMeta_1419_; uint8_t v_isExported_1420_; uint8_t v_importAll_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v_input_1391_);
v_imports_1417_ = lean_ctor_get(v___y_1407_, 0);
v_isModule_1418_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 1);
v_isMeta_1419_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 2);
v_isExported_1420_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 3);
v_importAll_1421_ = lean_ctor_get_uint8(v___y_1407_, sizeof(void*)*3 + 4);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___y_1407_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1431_ = lean_ctor_get(v___y_1407_, 2);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v___y_1407_, 1);
lean_dec(v_unused_1432_);
v___x_1423_ = v___y_1407_;
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_imports_1417_);
lean_dec(v___y_1407_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1430_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = 0;
v___x_1426_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 2, v___x_1426_);
lean_ctor_set(v___x_1423_, 1, v_pos_1393_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_imports_1417_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_pos_1393_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v___x_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*3 + 1, v_isModule_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*3 + 2, v_isMeta_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*3 + 3, v_isExported_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*3 + 4, v_importAll_1421_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*3, v___x_1425_);
return v___x_1428_;
}
}
}
}
}
v___jp_1433_:
{
lean_object* v_error_x3f_1435_; 
v_error_x3f_1435_ = lean_ctor_get(v___y_1434_, 2);
if (lean_obj_tag(v_error_x3f_1435_) == 1)
{
lean_object* v_imports_1436_; uint8_t v_badModifier_1437_; uint8_t v_isModule_1438_; uint8_t v_isMeta_1439_; uint8_t v_isExported_1440_; uint8_t v_importAll_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_inc_ref(v_error_x3f_1435_);
lean_dec_ref(v_input_1391_);
v_imports_1436_ = lean_ctor_get(v___y_1434_, 0);
v_badModifier_1437_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3);
v_isModule_1438_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 1);
v_isMeta_1439_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 2);
v_isExported_1440_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 3);
v_importAll_1441_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 4);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___y_1434_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v___y_1434_, 2);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v___y_1434_, 1);
lean_dec(v_unused_1450_);
v___x_1443_ = v___y_1434_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_imports_1436_);
lean_dec(v___y_1434_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
lean_inc(v_pos_1393_);
lean_inc_ref(v_imports_1436_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_pos_1393_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_imports_1436_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_pos_1393_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_error_x3f_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*3, v_badModifier_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*3 + 1, v_isModule_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*3 + 2, v_isMeta_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*3 + 3, v_isExported_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*3 + 4, v_importAll_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_inc(v_pos_1393_);
v___y_1395_ = v___x_1446_;
v_imports_1396_ = v_imports_1436_;
v_pos_1397_ = v_pos_1393_;
v_isModule_1398_ = v_isModule_1438_;
v_isMeta_1399_ = v_isMeta_1439_;
v_isExported_1400_ = v_isExported_1440_;
v_importAll_1401_ = v_importAll_1441_;
goto v___jp_1394_;
}
}
}
else
{
if (lean_obj_tag(v_error_x3f_1435_) == 1)
{
lean_object* v_imports_1451_; lean_object* v_pos_1452_; uint8_t v_isModule_1453_; uint8_t v_isMeta_1454_; uint8_t v_isExported_1455_; uint8_t v_importAll_1456_; 
lean_dec_ref(v_input_1391_);
v_imports_1451_ = lean_ctor_get(v___y_1434_, 0);
lean_inc_ref(v_imports_1451_);
v_pos_1452_ = lean_ctor_get(v___y_1434_, 1);
lean_inc(v_pos_1452_);
v_isModule_1453_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 1);
v_isMeta_1454_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 2);
v_isExported_1455_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 3);
v_importAll_1456_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 4);
v___y_1395_ = v___y_1434_;
v_imports_1396_ = v_imports_1451_;
v_pos_1397_ = v_pos_1452_;
v_isModule_1398_ = v_isModule_1453_;
v_isMeta_1399_ = v_isMeta_1454_;
v_isExported_1400_ = v_isExported_1455_;
v_importAll_1401_ = v_importAll_1456_;
goto v___jp_1394_;
}
else
{
lean_object* v_pos_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_error_x3f_1461_; 
v_pos_1457_ = lean_ctor_get(v___y_1434_, 1);
lean_inc(v_pos_1457_);
v___x_1458_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1458_, v_input_1391_, v___y_1434_, v___x_1459_, v_pos_1457_);
v_error_x3f_1461_ = lean_ctor_get(v___x_1460_, 2);
lean_inc(v_error_x3f_1461_);
if (lean_obj_tag(v_error_x3f_1461_) == 1)
{
lean_dec_ref_known(v_error_x3f_1461_, 1);
v___y_1407_ = v___x_1460_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1462_; 
lean_dec(v_error_x3f_1461_);
lean_inc_ref(v_input_1391_);
v___x_1462_ = l_Lean_ParseImports_moduleIdent(v_input_1391_, v___x_1460_);
v___y_1407_ = v___x_1462_;
goto v___jp_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1474_, lean_object* v_input_1475_, lean_object* v_s_1476_, lean_object* v_i_1477_, lean_object* v_j_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_string_utf8_at_end(v_k_1474_, v_i_1477_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_string_utf8_at_end(v_input_1475_, v_j_1478_);
if (v___x_1480_ == 0)
{
uint32_t v_curr_u2081_1481_; uint32_t v_curr_u2082_1482_; uint8_t v___x_1483_; uint8_t v___x_1484_; 
v_curr_u2081_1481_ = lean_string_utf8_get_fast(v_k_1474_, v_i_1477_);
v_curr_u2082_1482_ = lean_string_utf8_get_fast(v_input_1475_, v_j_1478_);
v___x_1483_ = lean_uint32_dec_eq(v_curr_u2081_1481_, v_curr_u2082_1482_);
v___x_1484_ = lean_bool_not(v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_string_utf8_next_fast(v_k_1474_, v_i_1477_);
lean_dec(v_i_1477_);
v___x_1486_ = lean_string_utf8_next_fast(v_input_1475_, v_j_1478_);
lean_dec(v_j_1478_);
v_i_1477_ = v___x_1485_;
v_j_1478_ = v___x_1486_;
goto _start;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_j_1478_);
lean_dec(v_i_1477_);
v___x_1488_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1479_, v_s_1476_);
return v___x_1488_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_j_1478_);
lean_dec(v_i_1477_);
v___x_1489_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1479_, v_s_1476_);
return v___x_1489_;
}
}
else
{
lean_object* v_imports_1490_; uint8_t v_badModifier_1491_; lean_object* v_error_x3f_1492_; uint8_t v_isModule_1493_; uint8_t v_isMeta_1494_; uint8_t v_isExported_1495_; uint8_t v_importAll_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_i_1477_);
v_imports_1490_ = lean_ctor_get(v_s_1476_, 0);
v_badModifier_1491_ = lean_ctor_get_uint8(v_s_1476_, sizeof(void*)*3);
v_error_x3f_1492_ = lean_ctor_get(v_s_1476_, 2);
v_isModule_1493_ = lean_ctor_get_uint8(v_s_1476_, sizeof(void*)*3 + 1);
v_isMeta_1494_ = lean_ctor_get_uint8(v_s_1476_, sizeof(void*)*3 + 2);
v_isExported_1495_ = lean_ctor_get_uint8(v_s_1476_, sizeof(void*)*3 + 3);
v_importAll_1496_ = lean_ctor_get_uint8(v_s_1476_, sizeof(void*)*3 + 4);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_s_1476_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_s_1476_, 1);
lean_dec(v_unused_1506_);
v___x_1498_ = v_s_1476_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_error_x3f_1492_);
lean_inc(v_imports_1490_);
lean_dec(v_s_1476_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_j_1478_);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_imports_1490_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_j_1478_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_error_x3f_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3, v_badModifier_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3 + 1, v_isModule_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3 + 2, v_isMeta_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3 + 3, v_isExported_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*3 + 4, v_importAll_1496_);
v___x_1501_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_ParseImports_whitespace(v_input_1475_, v___x_1501_);
v___x_1503_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1479_, v___x_1502_);
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1507_, lean_object* v_input_1508_, lean_object* v_s_1509_, lean_object* v_i_1510_, lean_object* v_j_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1507_, v_input_1508_, v_s_1509_, v_i_1510_, v_j_1511_);
lean_dec_ref(v_input_1508_);
lean_dec_ref(v_k_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_pos_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_s_1520_; lean_object* v_error_x3f_1521_; 
v_pos_1517_ = lean_ctor_get(v_a_1516_, 1);
lean_inc(v_pos_1517_);
v___x_1518_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1519_ = lean_unsigned_to_nat(0u);
v_s_1520_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1518_, v_a_1515_, v_a_1516_, v___x_1519_, v_pos_1517_);
v_error_x3f_1521_ = lean_ctor_get(v_s_1520_, 2);
lean_inc(v_error_x3f_1521_);
if (lean_obj_tag(v_error_x3f_1521_) == 1)
{
lean_dec_ref_known(v_error_x3f_1521_, 1);
lean_dec_ref(v_a_1515_);
return v_s_1520_;
}
else
{
lean_object* v_pos_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_error_x3f_1525_; 
lean_dec(v_error_x3f_1521_);
v_pos_1522_ = lean_ctor_get(v_s_1520_, 1);
lean_inc(v_pos_1522_);
v___x_1523_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1524_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1523_, v_a_1515_, v_s_1520_, v___x_1519_, v_pos_1522_);
v_error_x3f_1525_ = lean_ctor_get(v___x_1524_, 2);
lean_inc(v_error_x3f_1525_);
if (lean_obj_tag(v_error_x3f_1525_) == 1)
{
lean_dec_ref_known(v_error_x3f_1525_, 1);
lean_dec_ref(v_a_1515_);
return v___x_1524_;
}
else
{
lean_object* v___x_1526_; 
lean_dec(v_error_x3f_1525_);
v___x_1526_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1515_, v___x_1524_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* v_input_1529_, lean_object* v_fileName_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_s_1534_; lean_object* v_error_x3f_1535_; 
v___x_1532_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1533_ = l_Lean_ParseImports_whitespace(v_input_1529_, v___x_1532_);
lean_inc_ref(v_input_1529_);
v_s_1534_ = l_Lean_ParseImports_main(v_input_1529_, v___x_1533_);
v_error_x3f_1535_ = lean_ctor_get(v_s_1534_, 2);
lean_inc(v_error_x3f_1535_);
if (lean_obj_tag(v_error_x3f_1535_) == 1)
{
lean_object* v_pos_1536_; lean_object* v_val_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1559_; 
v_pos_1536_ = lean_ctor_get(v_s_1534_, 1);
lean_inc(v_pos_1536_);
lean_dec_ref(v_s_1534_);
v_val_1537_ = lean_ctor_get(v_error_x3f_1535_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_error_x3f_1535_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1539_ = v_error_x3f_1535_;
v_isShared_1540_ = v_isSharedCheck_1559_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_val_1537_);
lean_dec(v_error_x3f_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1559_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_fileMap_1541_; lean_object* v_pos_1542_; lean_object* v_line_1543_; lean_object* v_column_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v_fileMap_1541_ = l_String_toFileMap(v_input_1529_);
v_pos_1542_ = l_Lean_FileMap_toPosition(v_fileMap_1541_, v_pos_1536_);
lean_dec(v_pos_1536_);
v_line_1543_ = lean_ctor_get(v_pos_1542_, 0);
lean_inc(v_line_1543_);
v_column_1544_ = lean_ctor_get(v_pos_1542_, 1);
lean_inc(v_column_1544_);
lean_dec_ref(v_pos_1542_);
v___x_1545_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1546_ = lean_string_append(v_fileName_1530_, v___x_1545_);
v___x_1547_ = l_Nat_reprFast(v_line_1543_);
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = lean_string_append(v___x_1548_, v___x_1545_);
v___x_1550_ = l_Nat_reprFast(v_column_1544_);
v___x_1551_ = lean_string_append(v___x_1549_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1553_ = lean_string_append(v___x_1551_, v___x_1552_);
v___x_1554_ = lean_string_append(v___x_1553_, v_val_1537_);
lean_dec(v_val_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 18);
lean_ctor_set(v___x_1539_, 0, v___x_1554_);
v___x_1556_ = v___x_1539_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
else
{
lean_object* v_imports_1560_; uint8_t v_isModule_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_error_x3f_1535_);
lean_dec_ref(v_fileName_1530_);
lean_dec_ref(v_input_1529_);
v_imports_1560_ = lean_ctor_get(v_s_1534_, 0);
lean_inc_ref(v_imports_1560_);
v_isModule_1561_ = lean_ctor_get_uint8(v_s_1534_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1534_);
v___x_1562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1562_, 0, v_imports_1560_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*1, v_isModule_1561_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1564_, lean_object* v_fileName_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_parseImports_x27(v_input_1564_, v_fileName_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref(v_k_1568_);
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_val_1571_ = lean_ctor_get(v_x_1569_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v_x_1569_, 1);
v___x_1572_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1571_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_k_1568_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
if (lean_obj_tag(v_a_1576_) == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_array_to_list(v_a_1577_);
return v___x_1578_;
}
else
{
lean_object* v_head_1579_; lean_object* v_tail_1580_; lean_object* v___x_1581_; 
v_head_1579_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_head_1579_);
v_tail_1580_ = lean_ctor_get(v_a_1576_, 1);
lean_inc(v_tail_1580_);
lean_dec_ref_known(v_a_1576_, 2);
v___x_1581_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1577_, v_head_1579_);
v_a_1576_ = v_tail_1580_;
v_a_1577_ = v___x_1581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1583_, size_t v_i_1584_, lean_object* v_bs_1585_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_usize_dec_lt(v_i_1584_, v_sz_1583_);
if (v___x_1586_ == 0)
{
return v_bs_1585_;
}
else
{
lean_object* v_v_1587_; lean_object* v___x_1588_; lean_object* v_bs_x27_1589_; lean_object* v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_v_1587_ = lean_array_uget(v_bs_1585_, v_i_1584_);
v___x_1588_ = lean_unsigned_to_nat(0u);
v_bs_x27_1589_ = lean_array_uset(v_bs_1585_, v_i_1584_, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_v_1587_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1584_, v___x_1591_);
v___x_1593_ = lean_array_uset(v_bs_x27_1589_, v_i_1584_, v___x_1590_);
v_i_1584_ = v___x_1592_;
v_bs_1585_ = v___x_1593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_bs_1597_){
_start:
{
size_t v_sz_boxed_1598_; size_t v_i_boxed_1599_; lean_object* v_res_1600_; 
v_sz_boxed_1598_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1599_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1598_, v_i_boxed_1599_, v_bs_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1601_){
_start:
{
size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_sz_1602_ = lean_array_size(v_a_1601_);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1602_, v___x_1603_, v_a_1601_);
v___x_1605_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1610_){
_start:
{
lean_object* v_result_x3f_1611_; lean_object* v_errors_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1630_; 
v_result_x3f_1611_ = lean_ctor_get(v_x_1610_, 0);
v_errors_1612_ = lean_ctor_get(v_x_1610_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1614_ = v_x_1610_;
v_isShared_1615_ = v_isSharedCheck_1630_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_errors_1612_);
lean_inc(v_result_x3f_1611_);
lean_dec(v_x_1610_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1630_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1616_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1617_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1616_, v_result_x3f_1611_);
v___x_1618_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1619_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v___x_1619_);
lean_ctor_set(v___x_1614_, 0, v___x_1618_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1622_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1617_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1627_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1625_, v___x_1626_);
v___x_1628_ = l_Lean_Json_mkObj(v___x_1627_);
lean_dec(v___x_1627_);
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1633_, size_t v_i_1634_, lean_object* v_bs_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1634_, v_sz_1633_);
if (v___x_1636_ == 0)
{
return v_bs_1635_;
}
else
{
lean_object* v_v_1637_; lean_object* v___x_1638_; lean_object* v_bs_x27_1639_; lean_object* v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
v_v_1637_ = lean_array_uget(v_bs_1635_, v_i_1634_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v_bs_x27_1639_ = lean_array_uset(v_bs_1635_, v_i_1634_, v___x_1638_);
v___x_1640_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1637_);
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_add(v_i_1634_, v___x_1641_);
v___x_1643_ = lean_array_uset(v_bs_x27_1639_, v_i_1634_, v___x_1640_);
v_i_1634_ = v___x_1642_;
v_bs_1635_ = v___x_1643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1645_, lean_object* v_i_1646_, lean_object* v_bs_1647_){
_start:
{
size_t v_sz_boxed_1648_; size_t v_i_boxed_1649_; lean_object* v_res_1650_; 
v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1645_);
lean_dec(v_sz_1645_);
v_i_boxed_1649_ = lean_unbox_usize(v_i_1646_);
lean_dec(v_i_1646_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_1648_, v_i_boxed_1649_, v_bs_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* v_a_1651_){
_start:
{
size_t v_sz_1652_; size_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_sz_1652_ = lean_array_size(v_a_1651_);
v___x_1653_ = ((size_t)0ULL);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1652_, v___x_1653_, v_a_1651_);
v___x_1655_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1658_ = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
v___x_1659_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_1657_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
v___x_1664_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1665_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1663_, v___x_1664_);
v___x_1666_ = l_Lean_Json_mkObj(v___x_1665_);
lean_dec(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_bs_1673_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_bs_1673_);
return v___x_1676_;
}
else
{
lean_object* v_v_1677_; lean_object* v___x_1678_; lean_object* v_bs_x27_1679_; lean_object* v_a_1681_; lean_object* v_a_1687_; lean_object* v___x_1694_; 
v_v_1677_ = lean_array_uget(v_bs_1673_, v_i_1672_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v_bs_x27_1679_ = lean_array_uset(v_bs_1673_, v_i_1672_, v___x_1678_);
v___x_1694_ = l_IO_FS_readFile(v_v_1677_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = l_Lean_parseImports_x27(v_a_1695_, v_v_1677_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1706_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1706_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1706_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 1);
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v_a_1681_ = v___x_1704_;
goto v___jp_1680_;
}
}
}
else
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1696_, 1);
v_a_1687_ = v_a_1707_;
goto v___jp_1686_;
}
}
else
{
lean_object* v_a_1708_; 
lean_dec(v_v_1677_);
v_a_1708_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1694_, 1);
v_a_1687_ = v_a_1708_;
goto v___jp_1686_;
}
v___jp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1672_, v___x_1682_);
v___x_1684_ = lean_array_uset(v_bs_x27_1679_, v_i_1672_, v_a_1681_);
v_i_1672_ = v___x_1683_;
v_bs_1673_ = v___x_1684_;
goto _start;
}
v___jp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_io_error_to_string(v_a_1687_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = lean_array_push(v___x_1691_, v___x_1689_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1688_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v_a_1681_ = v___x_1693_;
goto v___jp_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1709_, lean_object* v_i_1710_, lean_object* v_bs_1711_, lean_object* v___y_1712_){
_start:
{
size_t v_sz_boxed_1713_; size_t v_i_boxed_1714_; lean_object* v_res_1715_; 
v_sz_boxed_1713_ = lean_unbox_usize(v_sz_1709_);
lean_dec(v_sz_1709_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1713_, v_i_boxed_1714_, v_bs_1711_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_putStr_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_get_stdout();
v_putStr_1719_ = lean_ctor_get(v___x_1718_, 4);
lean_inc_ref(v_putStr_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = lean_apply_2(v_putStr_1719_, v_s_1716_, lean_box(0));
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1724_){
_start:
{
uint32_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = 10;
v___x_1727_ = lean_string_push(v_s_1724_, v___x_1726_);
v___x_1728_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1732_){
_start:
{
size_t v_sz_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v_sz_1734_ = lean_array_size(v_fileNames_1732_);
v___x_1735_ = ((size_t)0ULL);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1734_, v___x_1735_, v_fileNames_1732_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1737_);
v___x_1739_ = l_Lean_Json_compress(v___x_1738_);
v___x_1740_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1739_);
return v___x_1740_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_a_1741_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1736_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1736_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_printImportsJson(v_fileNames_1749_);
return v_res_1751_;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
