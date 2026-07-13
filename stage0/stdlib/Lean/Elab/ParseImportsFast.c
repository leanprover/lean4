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
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object* v_p_298_, uint32_t v_c_299_){
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object* v_p_305_, lean_object* v_c_306_){
_start:
{
uint32_t v_c_boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_c_boxed_307_ = lean_unbox_uint32(v_c_306_);
lean_dec(v_c_306_);
v_res_308_ = l_Lean_ParseImports_takeWhile___lam__0(v_p_305_, v_c_boxed_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* v_p_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___f_313_; lean_object* v___x_314_; 
v___f_313_ = lean_alloc_closure((void*)(l_Lean_ParseImports_takeWhile___lam__0___boxed), 2, 1);
lean_closure_set(v___f_313_, 0, v_p_310_);
v___x_314_ = l_Lean_ParseImports_takeUntil(v___f_313_, v_a_311_, v_a_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* v_p_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_ParseImports_takeWhile(v_p_315_, v_a_316_, v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* v_p_319_, lean_object* v_q_320_, lean_object* v_input_321_, lean_object* v_s_322_){
_start:
{
lean_object* v_s_323_; lean_object* v_error_x3f_324_; 
lean_inc_ref(v_input_321_);
v_s_323_ = lean_apply_2(v_p_319_, v_input_321_, v_s_322_);
v_error_x3f_324_ = lean_ctor_get(v_s_323_, 2);
lean_inc(v_error_x3f_324_);
if (lean_obj_tag(v_error_x3f_324_) == 1)
{
lean_dec_ref_known(v_error_x3f_324_, 1);
lean_dec_ref(v_input_321_);
lean_dec_ref(v_q_320_);
return v_s_323_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_error_x3f_324_);
v___x_325_ = lean_apply_2(v_q_320_, v_input_321_, v_s_323_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object* v_p_326_, lean_object* v_q_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_s_330_; lean_object* v_error_x3f_331_; 
lean_inc_ref(v___y_328_);
v_s_330_ = lean_apply_2(v_p_326_, v___y_328_, v___y_329_);
v_error_x3f_331_ = lean_ctor_get(v_s_330_, 2);
lean_inc(v_error_x3f_331_);
if (lean_obj_tag(v_error_x3f_331_) == 1)
{
lean_dec_ref_known(v_error_x3f_331_, 1);
lean_dec_ref(v___y_328_);
lean_dec_ref(v_q_327_);
return v_s_330_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_error_x3f_331_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_3(v_q_327_, v___x_332_, v___y_328_, v_s_330_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(lean_object* v_input_336_, lean_object* v_s_337_){
_start:
{
lean_object* v_imports_338_; lean_object* v_pos_339_; uint8_t v_badModifier_340_; lean_object* v_error_x3f_341_; uint8_t v_isModule_342_; uint8_t v_isMeta_343_; uint8_t v_isExported_344_; uint8_t v_importAll_345_; uint8_t v___x_346_; 
v_imports_338_ = lean_ctor_get(v_s_337_, 0);
v_pos_339_ = lean_ctor_get(v_s_337_, 1);
v_badModifier_340_ = lean_ctor_get_uint8(v_s_337_, sizeof(void*)*3);
v_error_x3f_341_ = lean_ctor_get(v_s_337_, 2);
v_isModule_342_ = lean_ctor_get_uint8(v_s_337_, sizeof(void*)*3 + 1);
v_isMeta_343_ = lean_ctor_get_uint8(v_s_337_, sizeof(void*)*3 + 2);
v_isExported_344_ = lean_ctor_get_uint8(v_s_337_, sizeof(void*)*3 + 3);
v_importAll_345_ = lean_ctor_get_uint8(v_s_337_, sizeof(void*)*3 + 4);
v___x_346_ = lean_string_utf8_at_end(v_input_336_, v_pos_339_);
if (v___x_346_ == 0)
{
uint32_t v___x_347_; uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_string_utf8_get_fast(v_input_336_, v_pos_339_);
v___x_348_ = 10;
v___x_349_ = lean_uint32_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_358_; 
lean_inc(v_error_x3f_341_);
lean_inc(v_pos_339_);
lean_inc_ref(v_imports_338_);
v_isSharedCheck_358_ = !lean_is_exclusive(v_s_337_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; lean_object* v_unused_361_; 
v_unused_359_ = lean_ctor_get(v_s_337_, 2);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_s_337_, 1);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_s_337_, 0);
lean_dec(v_unused_361_);
v___x_351_ = v_s_337_;
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_s_337_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_string_utf8_next_fast(v_input_336_, v_pos_339_);
lean_dec(v_pos_339_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_imports_338_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_error_x3f_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*3, v_badModifier_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*3 + 1, v_isModule_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*3 + 2, v_isMeta_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*3 + 3, v_isExported_344_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*3 + 4, v_importAll_345_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
v_s_337_ = v___x_355_;
goto _start;
}
}
}
else
{
return v_s_337_;
}
}
else
{
return v_s_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(lean_object* v_input_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_362_, v_s_363_);
lean_dec_ref(v_input_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* v_input_368_, lean_object* v_s_369_){
_start:
{
lean_object* v_imports_370_; lean_object* v_pos_371_; uint8_t v_badModifier_372_; lean_object* v_error_x3f_373_; uint8_t v_isModule_374_; uint8_t v_isMeta_375_; uint8_t v_isExported_376_; uint8_t v_importAll_377_; uint8_t v___x_382_; 
v_imports_370_ = lean_ctor_get(v_s_369_, 0);
v_pos_371_ = lean_ctor_get(v_s_369_, 1);
v_badModifier_372_ = lean_ctor_get_uint8(v_s_369_, sizeof(void*)*3);
v_error_x3f_373_ = lean_ctor_get(v_s_369_, 2);
v_isModule_374_ = lean_ctor_get_uint8(v_s_369_, sizeof(void*)*3 + 1);
v_isMeta_375_ = lean_ctor_get_uint8(v_s_369_, sizeof(void*)*3 + 2);
v_isExported_376_ = lean_ctor_get_uint8(v_s_369_, sizeof(void*)*3 + 3);
v_importAll_377_ = lean_ctor_get_uint8(v_s_369_, sizeof(void*)*3 + 4);
v___x_382_ = lean_string_utf8_at_end(v_input_368_, v_pos_371_);
if (v___x_382_ == 0)
{
uint32_t v_curr_383_; uint8_t v___y_385_; uint8_t v___y_431_; uint32_t v___x_436_; uint8_t v___x_437_; 
v_curr_383_ = lean_string_utf8_get_fast(v_input_368_, v_pos_371_);
v___x_436_ = 9;
v___x_437_ = lean_uint32_dec_eq(v_curr_383_, v___x_436_);
if (v___x_437_ == 0)
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 32;
v___x_439_ = lean_uint32_dec_eq(v_curr_383_, v___x_438_);
if (v___x_439_ == 0)
{
v___y_431_ = v___x_437_;
goto v___jp_430_;
}
else
{
v___y_431_ = v___x_439_;
goto v___jp_430_;
}
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_450_);
v___x_441_ = v_s_369_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_s_369_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l_Lean_ParseImports_whitespace___closed__1));
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_pos_371_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v___x_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
v___jp_384_:
{
if (v___y_385_ == 0)
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 45;
v___x_387_ = lean_uint32_dec_eq(v_curr_383_, v___x_386_);
if (v___x_387_ == 0)
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 47;
v___x_389_ = lean_uint32_dec_eq(v_curr_383_, v___x_388_);
if (v___x_389_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v_i_390_; uint32_t v_curr_391_; uint8_t v___x_392_; 
v_i_390_ = lean_string_utf8_next_fast(v_input_368_, v_pos_371_);
v_curr_391_ = lean_string_utf8_get(v_input_368_, v_i_390_);
v___x_392_ = lean_uint32_dec_eq(v_curr_391_, v___x_386_);
if (v___x_392_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v_i_393_; uint32_t v_curr_394_; uint8_t v___x_395_; 
v_i_393_ = lean_string_utf8_next(v_input_368_, v_i_390_);
v_curr_394_ = lean_string_utf8_get(v_input_368_, v_i_393_);
v___x_395_ = lean_uint32_dec_eq(v_curr_394_, v___x_386_);
if (v___x_395_ == 0)
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 33;
v___x_397_ = lean_uint32_dec_eq(v_curr_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_409_; 
lean_inc(v_error_x3f_373_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_409_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; lean_object* v_unused_412_; 
v_unused_410_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_412_);
v___x_399_ = v_s_369_;
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_s_369_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_string_utf8_next(v_input_368_, v_i_393_);
lean_dec(v_i_393_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_error_x3f_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v_s_405_; lean_object* v_error_x3f_406_; 
v_s_405_ = l_Lean_ParseImports_finishCommentBlock(v___x_401_, v_input_368_, v___x_404_);
v_error_x3f_406_ = lean_ctor_get(v_s_405_, 2);
lean_inc(v_error_x3f_406_);
if (lean_obj_tag(v_error_x3f_406_) == 1)
{
lean_dec_ref_known(v_error_x3f_406_, 1);
return v_s_405_;
}
else
{
lean_dec(v_error_x3f_406_);
v_s_369_ = v_s_405_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_393_);
return v_s_369_;
}
}
else
{
lean_dec(v_i_393_);
return v_s_369_;
}
}
}
}
else
{
lean_object* v_i_413_; uint32_t v_curr_414_; uint8_t v___x_415_; 
v_i_413_ = lean_string_utf8_next_fast(v_input_368_, v_pos_371_);
v_curr_414_ = lean_string_utf8_get(v_input_368_, v_i_413_);
v___x_415_ = lean_uint32_dec_eq(v_curr_414_, v___x_386_);
if (v___x_415_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_426_; 
lean_inc(v_error_x3f_373_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_426_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_427_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_429_);
v___x_417_ = v_s_369_;
v_isShared_418_ = v_isSharedCheck_426_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_s_369_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_426_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_string_utf8_next(v_input_368_, v_i_413_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_error_x3f_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v_s_422_; lean_object* v_error_x3f_423_; 
v_s_422_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_368_, v___x_421_);
v_error_x3f_423_ = lean_ctor_get(v_s_422_, 2);
lean_inc(v_error_x3f_423_);
if (lean_obj_tag(v_error_x3f_423_) == 1)
{
lean_dec_ref_known(v_error_x3f_423_, 1);
return v_s_422_;
}
else
{
lean_dec(v_error_x3f_423_);
v_s_369_ = v_s_422_;
goto _start;
}
}
}
}
}
}
else
{
lean_inc(v_error_x3f_373_);
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
lean_dec_ref(v_s_369_);
goto v___jp_378_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 13;
v___x_433_ = lean_uint32_dec_eq(v_curr_383_, v___x_432_);
if (v___x_433_ == 0)
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 10;
v___x_435_ = lean_uint32_dec_eq(v_curr_383_, v___x_434_);
v___y_385_ = v___x_435_;
goto v___jp_384_;
}
else
{
v___y_385_ = v___x_433_;
goto v___jp_384_;
}
}
else
{
lean_inc(v_error_x3f_373_);
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
lean_dec_ref(v_s_369_);
goto v___jp_378_;
}
}
}
else
{
return v_s_369_;
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_string_utf8_next(v_input_368_, v_pos_371_);
lean_dec(v_pos_371_);
v___x_380_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_380_, 0, v_imports_370_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
lean_ctor_set(v___x_380_, 2, v_error_x3f_373_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 4, v_importAll_377_);
v_s_369_ = v___x_380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* v_input_451_, lean_object* v_s_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_ParseImports_whitespace(v_input_451_, v_s_452_);
lean_dec_ref(v_input_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object* v_k_454_, lean_object* v_failure_455_, lean_object* v_success_456_, lean_object* v_input_457_, lean_object* v_s_458_, lean_object* v_i_459_, lean_object* v_j_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = lean_string_utf8_at_end(v_k_454_, v_i_459_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = lean_string_utf8_at_end(v_input_457_, v_j_460_);
if (v___x_462_ == 0)
{
uint32_t v_curr_u2081_463_; uint32_t v_curr_u2082_464_; uint8_t v___x_465_; 
v_curr_u2081_463_ = lean_string_utf8_get_fast(v_k_454_, v_i_459_);
v_curr_u2082_464_ = lean_string_utf8_get_fast(v_input_457_, v_j_460_);
v___x_465_ = lean_uint32_dec_eq(v_curr_u2081_463_, v_curr_u2082_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v_j_460_);
lean_dec(v_i_459_);
lean_dec_ref(v_success_456_);
v___x_466_ = lean_apply_2(v_failure_455_, v_input_457_, v_s_458_);
return v___x_466_;
}
else
{
if (v___x_462_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_string_utf8_next_fast(v_k_454_, v_i_459_);
lean_dec(v_i_459_);
v___x_468_ = lean_string_utf8_next_fast(v_input_457_, v_j_460_);
lean_dec(v_j_460_);
v_i_459_ = v___x_467_;
v_j_460_ = v___x_468_;
goto _start;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_j_460_);
lean_dec(v_i_459_);
lean_dec_ref(v_success_456_);
v___x_470_ = lean_apply_2(v_failure_455_, v_input_457_, v_s_458_);
return v___x_470_;
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_j_460_);
lean_dec(v_i_459_);
lean_dec_ref(v_success_456_);
v___x_471_ = lean_apply_2(v_failure_455_, v_input_457_, v_s_458_);
return v___x_471_;
}
}
else
{
lean_object* v_imports_472_; uint8_t v_badModifier_473_; lean_object* v_error_x3f_474_; uint8_t v_isModule_475_; uint8_t v_isMeta_476_; uint8_t v_isExported_477_; uint8_t v_importAll_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_i_459_);
lean_dec_ref(v_failure_455_);
v_imports_472_ = lean_ctor_get(v_s_458_, 0);
v_badModifier_473_ = lean_ctor_get_uint8(v_s_458_, sizeof(void*)*3);
v_error_x3f_474_ = lean_ctor_get(v_s_458_, 2);
v_isModule_475_ = lean_ctor_get_uint8(v_s_458_, sizeof(void*)*3 + 1);
v_isMeta_476_ = lean_ctor_get_uint8(v_s_458_, sizeof(void*)*3 + 2);
v_isExported_477_ = lean_ctor_get_uint8(v_s_458_, sizeof(void*)*3 + 3);
v_importAll_478_ = lean_ctor_get_uint8(v_s_458_, sizeof(void*)*3 + 4);
v_isSharedCheck_487_ = !lean_is_exclusive(v_s_458_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_s_458_, 1);
lean_dec(v_unused_488_);
v___x_480_ = v_s_458_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_error_x3f_474_);
lean_inc(v_imports_472_);
lean_dec(v_s_458_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v_j_460_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_imports_472_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_j_460_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_error_x3f_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*3, v_badModifier_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*3 + 1, v_isModule_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*3 + 2, v_isMeta_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*3 + 3, v_isExported_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*3 + 4, v_importAll_478_);
v___x_483_ = v_reuseFailAlloc_486_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = l_Lean_ParseImports_whitespace(v_input_457_, v___x_483_);
v___x_485_ = lean_apply_2(v_success_456_, v_input_457_, v___x_484_);
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* v_k_489_, lean_object* v_failure_490_, lean_object* v_success_491_, lean_object* v_input_492_, lean_object* v_s_493_, lean_object* v_i_494_, lean_object* v_j_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_489_, v_failure_490_, v_success_491_, v_input_492_, v_s_493_, v_i_494_, v_j_495_);
lean_dec_ref(v_k_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* v_k_497_, lean_object* v_failure_498_, lean_object* v_success_499_, lean_object* v_input_500_, lean_object* v_s_501_){
_start:
{
lean_object* v_pos_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_pos_502_ = lean_ctor_get(v_s_501_, 1);
lean_inc(v_pos_502_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_497_, v_failure_498_, v_success_499_, v_input_500_, v_s_501_, v___x_503_, v_pos_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* v_k_505_, lean_object* v_failure_506_, lean_object* v_success_507_, lean_object* v_input_508_, lean_object* v_s_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_ParseImports_keywordCore(v_k_505_, v_failure_506_, v_success_507_, v_input_508_, v_s_509_);
lean_dec_ref(v_k_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* v_k_513_, lean_object* v_x_514_, lean_object* v_s_515_){
_start:
{
lean_object* v_imports_516_; lean_object* v_pos_517_; uint8_t v_badModifier_518_; uint8_t v_isModule_519_; uint8_t v_isMeta_520_; uint8_t v_isExported_521_; uint8_t v_importAll_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_imports_516_ = lean_ctor_get(v_s_515_, 0);
v_pos_517_ = lean_ctor_get(v_s_515_, 1);
v_badModifier_518_ = lean_ctor_get_uint8(v_s_515_, sizeof(void*)*3);
v_isModule_519_ = lean_ctor_get_uint8(v_s_515_, sizeof(void*)*3 + 1);
v_isMeta_520_ = lean_ctor_get_uint8(v_s_515_, sizeof(void*)*3 + 2);
v_isExported_521_ = lean_ctor_get_uint8(v_s_515_, sizeof(void*)*3 + 3);
v_importAll_522_ = lean_ctor_get_uint8(v_s_515_, sizeof(void*)*3 + 4);
v_isSharedCheck_534_ = !lean_is_exclusive(v_s_515_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_s_515_, 2);
lean_dec(v_unused_535_);
v___x_524_ = v_s_515_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_pos_517_);
lean_inc(v_imports_516_);
lean_dec(v_s_515_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_526_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
v___x_527_ = lean_string_append(v___x_526_, v_k_513_);
v___x_528_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 2, v___x_530_);
v___x_532_ = v___x_524_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_imports_516_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_pos_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___x_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*3, v_badModifier_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*3 + 1, v_isModule_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*3 + 2, v_isMeta_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*3 + 3, v_isExported_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*3 + 4, v_importAll_522_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* v_k_536_, lean_object* v_x_537_, lean_object* v_s_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_ParseImports_keyword___lam__0(v_k_536_, v_x_537_, v_s_538_);
lean_dec_ref(v_x_537_);
lean_dec_ref(v_k_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* v_k_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_pos_543_; lean_object* v___f_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_pos_543_ = lean_ctor_get(v_a_542_, 1);
lean_inc(v_pos_543_);
lean_inc_ref(v_k_540_);
v___f_544_ = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(v___f_544_, 0, v_k_540_);
v___x_545_ = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_540_, v___f_544_, v___x_545_, v_a_541_, v_a_542_, v___x_546_, v_pos_543_);
lean_dec_ref(v_k_540_);
return v___x_547_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* v_input_548_, lean_object* v_s_549_){
_start:
{
lean_object* v_pos_550_; uint32_t v_curr_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v_pos_550_ = lean_ctor_get(v_s_549_, 1);
v_curr_551_ = lean_string_utf8_get(v_input_548_, v_pos_550_);
v___x_552_ = 46;
v___x_553_ = lean_uint32_dec_eq(v_curr_551_, v___x_552_);
if (v___x_553_ == 0)
{
return v___x_553_;
}
else
{
lean_object* v_i_554_; uint8_t v___x_555_; 
v_i_554_ = lean_string_utf8_next(v_input_548_, v_pos_550_);
v___x_555_ = lean_string_utf8_at_end(v_input_548_, v_i_554_);
if (v___x_555_ == 0)
{
uint32_t v_curr_556_; uint8_t v___y_558_; uint8_t v___y_562_; uint32_t v___x_571_; uint8_t v___x_572_; 
v_curr_556_ = lean_string_utf8_get_fast(v_input_548_, v_i_554_);
lean_dec(v_i_554_);
v___x_571_ = 65;
v___x_572_ = lean_uint32_dec_le(v___x_571_, v_curr_556_);
if (v___x_572_ == 0)
{
goto v___jp_566_;
}
else
{
uint32_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = 90;
v___x_574_ = lean_uint32_dec_le(v_curr_556_, v___x_573_);
if (v___x_574_ == 0)
{
goto v___jp_566_;
}
else
{
return v___x_553_;
}
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
uint32_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 171;
v___x_560_ = lean_uint32_dec_eq(v_curr_556_, v___x_559_);
return v___x_560_;
}
else
{
return v___x_553_;
}
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
uint32_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 95;
v___x_564_ = lean_uint32_dec_eq(v_curr_556_, v___x_563_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; 
v___x_565_ = l_Lean_isLetterLike(v_curr_556_);
v___y_558_ = v___x_565_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___x_564_;
goto v___jp_557_;
}
}
else
{
return v___x_553_;
}
}
v___jp_566_:
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 97;
v___x_568_ = lean_uint32_dec_le(v___x_567_, v_curr_556_);
if (v___x_568_ == 0)
{
v___y_562_ = v___x_568_;
goto v___jp_561_;
}
else
{
uint32_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 122;
v___x_570_ = lean_uint32_dec_le(v_curr_556_, v___x_569_);
v___y_562_ = v___x_570_;
goto v___jp_561_;
}
}
}
else
{
uint8_t v___x_575_; 
lean_dec(v_i_554_);
v___x_575_ = 0;
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_576_, lean_object* v_s_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_Lean_ParseImports_isIdCont(v_input_576_, v_s_577_);
lean_dec_ref(v_s_577_);
lean_dec_ref(v_input_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_580_, lean_object* v_s_581_){
_start:
{
lean_object* v_imports_582_; lean_object* v_pos_583_; uint8_t v_badModifier_584_; lean_object* v_error_x3f_585_; uint8_t v_isModule_586_; uint8_t v_isMeta_587_; uint8_t v_isExported_588_; uint8_t v_importAll_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
v_imports_582_ = lean_ctor_get(v_s_581_, 0);
v_pos_583_ = lean_ctor_get(v_s_581_, 1);
v_badModifier_584_ = lean_ctor_get_uint8(v_s_581_, sizeof(void*)*3);
v_error_x3f_585_ = lean_ctor_get(v_s_581_, 2);
v_isModule_586_ = lean_ctor_get_uint8(v_s_581_, sizeof(void*)*3 + 1);
v_isMeta_587_ = lean_ctor_get_uint8(v_s_581_, sizeof(void*)*3 + 2);
v_isExported_588_ = lean_ctor_get_uint8(v_s_581_, sizeof(void*)*3 + 3);
v_importAll_589_ = lean_ctor_get_uint8(v_s_581_, sizeof(void*)*3 + 4);
v_isSharedCheck_597_ = !lean_is_exclusive(v_s_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v_s_581_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_error_x3f_585_);
lean_inc(v_pos_583_);
lean_inc(v_imports_582_);
lean_dec(v_s_581_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_array_push(v_imports_582_, v_i_580_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_pos_583_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_error_x3f_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3, v_badModifier_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 1, v_isModule_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 2, v_isMeta_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 3, v_isExported_588_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 4, v_importAll_589_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_598_){
_start:
{
uint8_t v___y_600_; uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 95;
v___x_608_ = lean_uint32_dec_eq(v_c_598_, v___x_607_);
if (v___x_608_ == 0)
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 39;
v___x_610_ = lean_uint32_dec_eq(v_c_598_, v___x_609_);
v___y_600_ = v___x_610_;
goto v___jp_599_;
}
else
{
v___y_600_ = v___x_608_;
goto v___jp_599_;
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
uint32_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 33;
v___x_602_ = lean_uint32_dec_eq(v_c_598_, v___x_601_);
if (v___x_602_ == 0)
{
uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 63;
v___x_604_ = lean_uint32_dec_eq(v_c_598_, v___x_603_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = l_Lean_isLetterLike(v_c_598_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_isSubScriptAlnum(v_c_598_);
return v___x_606_;
}
else
{
return v___x_605_;
}
}
else
{
return v___x_604_;
}
}
else
{
return v___x_602_;
}
}
else
{
return v___y_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_611_){
_start:
{
uint32_t v_c_boxed_612_; uint8_t v_res_613_; lean_object* v_r_614_; 
v_c_boxed_612_ = lean_unbox_uint32(v_c_611_);
lean_dec(v_c_611_);
v_res_613_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_612_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_615_){
_start:
{
uint8_t v___y_617_; uint8_t v___y_625_; uint8_t v___y_637_; uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 65;
v___x_648_ = lean_uint32_dec_le(v___x_647_, v_c_615_);
if (v___x_648_ == 0)
{
goto v___jp_642_;
}
else
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 90;
v___x_650_ = lean_uint32_dec_le(v_c_615_, v___x_649_);
if (v___x_650_ == 0)
{
goto v___jp_642_;
}
else
{
return v___x_650_;
}
}
v___jp_616_:
{
if (v___y_617_ == 0)
{
uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 33;
v___x_619_ = lean_uint32_dec_eq(v_c_615_, v___x_618_);
if (v___x_619_ == 0)
{
uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 63;
v___x_621_ = lean_uint32_dec_eq(v_c_615_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_isLetterLike(v_c_615_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_isSubScriptAlnum(v_c_615_);
return v___x_623_;
}
else
{
return v___x_622_;
}
}
else
{
return v___x_621_;
}
}
else
{
return v___x_619_;
}
}
else
{
return v___y_617_;
}
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 46;
v___x_627_ = lean_uint32_dec_eq(v_c_615_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 10;
v___x_629_ = lean_uint32_dec_eq(v_c_615_, v___x_628_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 32;
v___x_631_ = lean_uint32_dec_eq(v_c_615_, v___x_630_);
if (v___x_631_ == 0)
{
uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 95;
v___x_633_ = lean_uint32_dec_eq(v_c_615_, v___x_632_);
if (v___x_633_ == 0)
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 39;
v___x_635_ = lean_uint32_dec_eq(v_c_615_, v___x_634_);
v___y_617_ = v___x_635_;
goto v___jp_616_;
}
else
{
v___y_617_ = v___x_633_;
goto v___jp_616_;
}
}
else
{
return v___y_625_;
}
}
else
{
return v___y_625_;
}
}
else
{
return v___y_625_;
}
}
else
{
return v___y_625_;
}
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
uint32_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 48;
v___x_639_ = lean_uint32_dec_le(v___x_638_, v_c_615_);
if (v___x_639_ == 0)
{
v___y_625_ = v___x_639_;
goto v___jp_624_;
}
else
{
uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 57;
v___x_641_ = lean_uint32_dec_le(v_c_615_, v___x_640_);
v___y_625_ = v___x_641_;
goto v___jp_624_;
}
}
else
{
return v___y_637_;
}
}
v___jp_642_:
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 97;
v___x_644_ = lean_uint32_dec_le(v___x_643_, v_c_615_);
if (v___x_644_ == 0)
{
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
else
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 122;
v___x_646_ = lean_uint32_dec_le(v_c_615_, v___x_645_);
v___y_637_ = v___x_646_;
goto v___jp_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_651_){
_start:
{
uint32_t v_c_boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_c_boxed_652_ = lean_unbox_uint32(v_c_651_);
lean_dec(v_c_651_);
v_res_653_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_652_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_655_, lean_object* v_s_656_){
_start:
{
lean_object* v_imports_657_; lean_object* v_pos_658_; uint8_t v_badModifier_659_; lean_object* v_error_x3f_660_; uint8_t v_isModule_661_; uint8_t v_isMeta_662_; uint8_t v_isExported_663_; uint8_t v_importAll_664_; uint8_t v___x_665_; 
v_imports_657_ = lean_ctor_get(v_s_656_, 0);
v_pos_658_ = lean_ctor_get(v_s_656_, 1);
v_badModifier_659_ = lean_ctor_get_uint8(v_s_656_, sizeof(void*)*3);
v_error_x3f_660_ = lean_ctor_get(v_s_656_, 2);
v_isModule_661_ = lean_ctor_get_uint8(v_s_656_, sizeof(void*)*3 + 1);
v_isMeta_662_ = lean_ctor_get_uint8(v_s_656_, sizeof(void*)*3 + 2);
v_isExported_663_ = lean_ctor_get_uint8(v_s_656_, sizeof(void*)*3 + 3);
v_importAll_664_ = lean_ctor_get_uint8(v_s_656_, sizeof(void*)*3 + 4);
v___x_665_ = lean_string_utf8_at_end(v_input_655_, v_pos_658_);
if (v___x_665_ == 0)
{
uint32_t v___x_666_; uint32_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_string_utf8_get_fast(v_input_655_, v_pos_658_);
v___x_667_ = 187;
v___x_668_ = lean_uint32_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
lean_inc(v_error_x3f_660_);
lean_inc(v_pos_658_);
lean_inc_ref(v_imports_657_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_s_656_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_678_ = lean_ctor_get(v_s_656_, 2);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_s_656_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_s_656_, 0);
lean_dec(v_unused_680_);
v___x_670_ = v_s_656_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_s_656_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_string_utf8_next_fast(v_input_655_, v_pos_658_);
lean_dec(v_pos_658_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_imports_657_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_error_x3f_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*3, v_badModifier_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*3 + 1, v_isModule_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*3 + 2, v_isMeta_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*3 + 3, v_isExported_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*3 + 4, v_importAll_664_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v_s_656_ = v___x_674_;
goto _start;
}
}
}
else
{
return v_s_656_;
}
}
else
{
return v_s_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_681_, lean_object* v_s_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_681_, v_s_682_);
lean_dec_ref(v_input_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_684_, uint32_t v_curr_685_, lean_object* v_input_686_, lean_object* v_s_687_){
_start:
{
lean_object* v_imports_688_; lean_object* v_pos_689_; uint8_t v_badModifier_690_; lean_object* v_error_x3f_691_; uint8_t v_isModule_692_; uint8_t v_isMeta_693_; uint8_t v_isExported_694_; uint8_t v_importAll_695_; uint8_t v___y_697_; uint8_t v___x_710_; 
v_imports_688_ = lean_ctor_get(v_s_687_, 0);
v_pos_689_ = lean_ctor_get(v_s_687_, 1);
v_badModifier_690_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*3);
v_error_x3f_691_ = lean_ctor_get(v_s_687_, 2);
v_isModule_692_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*3 + 1);
v_isMeta_693_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*3 + 2);
v_isExported_694_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*3 + 3);
v_importAll_695_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*3 + 4);
v___x_710_ = lean_string_utf8_at_end(v_input_686_, v_pos_689_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; uint32_t v___x_713_; uint8_t v___y_715_; uint8_t v___y_723_; uint8_t v___y_735_; uint32_t v___x_745_; uint8_t v___x_746_; 
v___x_711_ = 171;
v___x_712_ = lean_uint32_dec_eq(v_curr_685_, v___x_711_);
v___x_713_ = lean_string_utf8_get_fast(v_input_686_, v_pos_689_);
v___x_745_ = 65;
v___x_746_ = lean_uint32_dec_le(v___x_745_, v___x_713_);
if (v___x_746_ == 0)
{
goto v___jp_740_;
}
else
{
uint32_t v___x_747_; uint8_t v___x_748_; 
v___x_747_ = 90;
v___x_748_ = lean_uint32_dec_le(v___x_713_, v___x_747_);
if (v___x_748_ == 0)
{
goto v___jp_740_;
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 33;
v___x_717_ = lean_uint32_dec_eq(v___x_713_, v___x_716_);
if (v___x_717_ == 0)
{
uint32_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 63;
v___x_719_ = lean_uint32_dec_eq(v___x_713_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_isLetterLike(v___x_713_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_isSubScriptAlnum(v___x_713_);
if (v___x_721_ == 0)
{
v___y_697_ = v___y_684_;
goto v___jp_696_;
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
else
{
if (v___x_720_ == 0)
{
v___y_697_ = v___y_684_;
goto v___jp_696_;
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
}
else
{
if (v___x_719_ == 0)
{
v___y_697_ = v___y_684_;
goto v___jp_696_;
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
}
else
{
if (v___x_717_ == 0)
{
v___y_697_ = v___y_684_;
goto v___jp_696_;
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
v___jp_722_:
{
if (v___y_723_ == 0)
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 46;
v___x_725_ = lean_uint32_dec_eq(v___x_713_, v___x_724_);
if (v___x_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 10;
v___x_727_ = lean_uint32_dec_eq(v___x_713_, v___x_726_);
if (v___x_727_ == 0)
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 32;
v___x_729_ = lean_uint32_dec_eq(v___x_713_, v___x_728_);
if (v___x_729_ == 0)
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 95;
v___x_731_ = lean_uint32_dec_eq(v___x_713_, v___x_730_);
if (v___x_731_ == 0)
{
uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 39;
v___x_733_ = lean_uint32_dec_eq(v___x_713_, v___x_732_);
v___y_715_ = v___x_733_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___x_731_;
goto v___jp_714_;
}
}
else
{
v___y_697_ = v___x_729_;
goto v___jp_696_;
}
}
else
{
v___y_697_ = v___x_727_;
goto v___jp_696_;
}
}
else
{
v___y_697_ = v___x_725_;
goto v___jp_696_;
}
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
v___jp_734_:
{
if (v___y_735_ == 0)
{
uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 48;
v___x_737_ = lean_uint32_dec_le(v___x_736_, v___x_713_);
if (v___x_737_ == 0)
{
v___y_723_ = v___x_737_;
goto v___jp_722_;
}
else
{
uint32_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 57;
v___x_739_ = lean_uint32_dec_le(v___x_713_, v___x_738_);
v___y_723_ = v___x_739_;
goto v___jp_722_;
}
}
else
{
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
}
v___jp_740_:
{
uint32_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = 97;
v___x_742_ = lean_uint32_dec_le(v___x_741_, v___x_713_);
if (v___x_742_ == 0)
{
v___y_735_ = v___x_742_;
goto v___jp_734_;
}
else
{
uint32_t v___x_743_; uint8_t v___x_744_; 
v___x_743_ = 122;
v___x_744_ = lean_uint32_dec_le(v___x_713_, v___x_743_);
v___y_735_ = v___x_744_;
goto v___jp_734_;
}
}
}
else
{
return v_s_687_;
}
v___jp_696_:
{
if (v___y_697_ == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_706_; 
lean_inc(v_error_x3f_691_);
lean_inc(v_pos_689_);
lean_inc_ref(v_imports_688_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_s_687_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_707_ = lean_ctor_get(v_s_687_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_s_687_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_s_687_, 0);
lean_dec(v_unused_709_);
v___x_699_ = v_s_687_;
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
else
{
lean_dec(v_s_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_string_utf8_next_fast(v_input_686_, v_pos_689_);
lean_dec(v_pos_689_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_imports_688_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_error_x3f_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3, v_badModifier_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3 + 1, v_isModule_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3 + 2, v_isMeta_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3 + 3, v_isExported_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_705_, sizeof(void*)*3 + 4, v_importAll_695_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_s_687_ = v___x_703_;
goto _start;
}
}
}
else
{
return v_s_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_749_, lean_object* v_curr_750_, lean_object* v_input_751_, lean_object* v_s_752_){
_start:
{
uint8_t v___y_2267__boxed_753_; uint32_t v_curr_boxed_754_; lean_object* v_res_755_; 
v___y_2267__boxed_753_ = lean_unbox(v___y_749_);
v_curr_boxed_754_ = lean_unbox_uint32(v_curr_750_);
lean_dec(v_curr_750_);
v_res_755_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_2267__boxed_753_, v_curr_boxed_754_, v_input_751_, v_s_752_);
lean_dec_ref(v_input_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_762_, lean_object* v_finalize_763_, lean_object* v_module_764_, lean_object* v_s_765_){
_start:
{
lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; uint8_t v___y_771_; lean_object* v___y_772_; uint8_t v___y_773_; lean_object* v___y_774_; uint8_t v___y_775_; uint8_t v___y_776_; uint8_t v___y_777_; lean_object* v_imports_782_; lean_object* v_pos_783_; uint8_t v_badModifier_784_; lean_object* v_error_x3f_785_; uint8_t v_isModule_786_; uint8_t v_isMeta_787_; uint8_t v_isExported_788_; uint8_t v_importAll_789_; uint8_t v___x_790_; 
v_imports_782_ = lean_ctor_get(v_s_765_, 0);
v_pos_783_ = lean_ctor_get(v_s_765_, 1);
v_badModifier_784_ = lean_ctor_get_uint8(v_s_765_, sizeof(void*)*3);
v_error_x3f_785_ = lean_ctor_get(v_s_765_, 2);
v_isModule_786_ = lean_ctor_get_uint8(v_s_765_, sizeof(void*)*3 + 1);
v_isMeta_787_ = lean_ctor_get_uint8(v_s_765_, sizeof(void*)*3 + 2);
v_isExported_788_ = lean_ctor_get_uint8(v_s_765_, sizeof(void*)*3 + 3);
v_importAll_789_ = lean_ctor_get_uint8(v_s_765_, sizeof(void*)*3 + 4);
v___x_790_ = lean_string_utf8_at_end(v_input_762_, v_pos_783_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_error_x3f_785_);
lean_inc(v_pos_783_);
lean_inc_ref(v_imports_782_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_s_765_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; 
v_unused_947_ = lean_ctor_get(v_s_765_, 2);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_s_765_, 1);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_s_765_, 0);
lean_dec(v_unused_949_);
v___x_792_ = v_s_765_;
v_isShared_793_ = v_isSharedCheck_946_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_s_765_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_946_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint32_t v_curr_794_; uint32_t v___x_795_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint32_t v___y_800_; uint8_t v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; uint8_t v___y_807_; uint8_t v___y_808_; uint8_t v___y_809_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint32_t v___y_815_; uint8_t v___y_816_; uint8_t v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; uint8_t v___y_822_; uint8_t v___y_823_; uint8_t v___y_824_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint32_t v___y_832_; uint8_t v___y_833_; uint8_t v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; uint8_t v___y_840_; uint8_t v___x_845_; uint8_t v___y_847_; uint8_t v___y_874_; uint8_t v___y_878_; 
v_curr_794_ = lean_string_utf8_get_fast(v_input_762_, v_pos_783_);
v___x_795_ = 171;
v___x_845_ = lean_uint32_dec_eq(v_curr_794_, v___x_795_);
if (v___x_845_ == 0)
{
uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 65;
v___x_888_ = lean_uint32_dec_le(v___x_887_, v_curr_794_);
if (v___x_888_ == 0)
{
goto v___jp_882_;
}
else
{
uint32_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 90;
v___x_890_ = lean_uint32_dec_le(v_curr_794_, v___x_889_);
if (v___x_890_ == 0)
{
goto v___jp_882_;
}
else
{
v___y_847_ = v___x_890_;
goto v___jp_846_;
}
}
}
else
{
lean_object* v_startPart_891_; lean_object* v___x_892_; lean_object* v_s_893_; lean_object* v_imports_894_; lean_object* v_pos_895_; uint8_t v_badModifier_896_; lean_object* v_error_x3f_897_; uint8_t v_isModule_898_; uint8_t v_isMeta_899_; uint8_t v_isExported_900_; uint8_t v_importAll_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_945_; 
lean_del_object(v___x_792_);
v_startPart_891_ = lean_string_utf8_next_fast(v_input_762_, v_pos_783_);
lean_dec(v_pos_783_);
v___x_892_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_892_, 0, v_imports_782_);
lean_ctor_set(v___x_892_, 1, v_startPart_891_);
lean_ctor_set(v___x_892_, 2, v_error_x3f_785_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*3, v_badModifier_784_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*3 + 1, v_isModule_786_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*3 + 2, v_isMeta_787_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*3 + 3, v_isExported_788_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*3 + 4, v_importAll_789_);
v_s_893_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_762_, v___x_892_);
v_imports_894_ = lean_ctor_get(v_s_893_, 0);
v_pos_895_ = lean_ctor_get(v_s_893_, 1);
v_badModifier_896_ = lean_ctor_get_uint8(v_s_893_, sizeof(void*)*3);
v_error_x3f_897_ = lean_ctor_get(v_s_893_, 2);
v_isModule_898_ = lean_ctor_get_uint8(v_s_893_, sizeof(void*)*3 + 1);
v_isMeta_899_ = lean_ctor_get_uint8(v_s_893_, sizeof(void*)*3 + 2);
v_isExported_900_ = lean_ctor_get_uint8(v_s_893_, sizeof(void*)*3 + 3);
v_importAll_901_ = lean_ctor_get_uint8(v_s_893_, sizeof(void*)*3 + 4);
v_isSharedCheck_945_ = !lean_is_exclusive(v_s_893_);
if (v_isSharedCheck_945_ == 0)
{
v___x_903_ = v_s_893_;
v_isShared_904_ = v_isSharedCheck_945_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_error_x3f_897_);
lean_inc(v_pos_895_);
lean_inc(v_imports_894_);
lean_dec(v_s_893_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_945_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___x_905_; 
v___x_905_ = lean_string_utf8_at_end(v_input_762_, v_pos_895_);
if (v___x_905_ == 0)
{
lean_object* v_i_906_; lean_object* v_s_908_; 
v_i_906_ = lean_string_utf8_next_fast(v_input_762_, v_pos_895_);
lean_inc(v_error_x3f_897_);
lean_inc_ref(v_imports_894_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_i_906_);
v_s_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_imports_894_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_i_906_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_error_x3f_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3, v_badModifier_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3 + 1, v_isModule_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3 + 2, v_isMeta_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3 + 3, v_isExported_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3 + 4, v_importAll_901_);
v_s_908_ = v_reuseFailAlloc_940_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v_module_910_; uint8_t v___y_912_; uint32_t v_curr_917_; uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_909_ = lean_string_utf8_extract(v_input_762_, v_startPart_891_, v_pos_895_);
lean_dec(v_pos_895_);
v_module_910_ = l_Lean_Name_str___override(v_module_764_, v___x_909_);
v_curr_917_ = lean_string_utf8_get(v_input_762_, v_i_906_);
v___x_918_ = 46;
v___x_919_ = lean_uint32_dec_eq(v_curr_917_, v___x_918_);
if (v___x_919_ == 0)
{
v___y_912_ = v___x_919_;
goto v___jp_911_;
}
else
{
lean_object* v_i_920_; uint8_t v___x_921_; 
v_i_920_ = lean_string_utf8_next(v_input_762_, v_i_906_);
v___x_921_ = lean_string_utf8_at_end(v_input_762_, v_i_920_);
if (v___x_921_ == 0)
{
uint32_t v_curr_922_; uint8_t v___y_924_; uint8_t v___y_927_; uint32_t v___x_936_; uint8_t v___x_937_; 
v_curr_922_ = lean_string_utf8_get_fast(v_input_762_, v_i_920_);
lean_dec(v_i_920_);
v___x_936_ = 65;
v___x_937_ = lean_uint32_dec_le(v___x_936_, v_curr_922_);
if (v___x_937_ == 0)
{
goto v___jp_931_;
}
else
{
uint32_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = 90;
v___x_939_ = lean_uint32_dec_le(v_curr_922_, v___x_938_);
if (v___x_939_ == 0)
{
goto v___jp_931_;
}
else
{
v___y_912_ = v___x_919_;
goto v___jp_911_;
}
}
v___jp_923_:
{
if (v___y_924_ == 0)
{
uint8_t v___x_925_; 
v___x_925_ = lean_uint32_dec_eq(v_curr_922_, v___x_795_);
v___y_912_ = v___x_925_;
goto v___jp_911_;
}
else
{
v___y_912_ = v___x_919_;
goto v___jp_911_;
}
}
v___jp_926_:
{
if (v___y_927_ == 0)
{
uint32_t v___x_928_; uint8_t v___x_929_; 
v___x_928_ = 95;
v___x_929_ = lean_uint32_dec_eq(v_curr_922_, v___x_928_);
if (v___x_929_ == 0)
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_isLetterLike(v_curr_922_);
v___y_924_ = v___x_930_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___x_929_;
goto v___jp_923_;
}
}
else
{
v___y_912_ = v___x_919_;
goto v___jp_911_;
}
}
v___jp_931_:
{
uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 97;
v___x_933_ = lean_uint32_dec_le(v___x_932_, v_curr_922_);
if (v___x_933_ == 0)
{
v___y_927_ = v___x_933_;
goto v___jp_926_;
}
else
{
uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 122;
v___x_935_ = lean_uint32_dec_le(v_curr_922_, v___x_934_);
v___y_927_ = v___x_935_;
goto v___jp_926_;
}
}
}
else
{
lean_dec(v_i_920_);
v___y_912_ = v___x_905_;
goto v___jp_911_;
}
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
lean_object* v___x_913_; 
lean_dec(v_error_x3f_897_);
lean_dec_ref(v_imports_894_);
v___x_913_ = lean_apply_3(v_finalize_763_, v_module_910_, v_input_762_, v_s_908_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v_s_915_; 
lean_dec_ref(v_s_908_);
v___x_914_ = lean_string_utf8_next(v_input_762_, v_i_906_);
v_s_915_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_915_, 0, v_imports_894_);
lean_ctor_set(v_s_915_, 1, v___x_914_);
lean_ctor_set(v_s_915_, 2, v_error_x3f_897_);
lean_ctor_set_uint8(v_s_915_, sizeof(void*)*3, v_badModifier_896_);
lean_ctor_set_uint8(v_s_915_, sizeof(void*)*3 + 1, v_isModule_898_);
lean_ctor_set_uint8(v_s_915_, sizeof(void*)*3 + 2, v_isMeta_899_);
lean_ctor_set_uint8(v_s_915_, sizeof(void*)*3 + 3, v_isExported_900_);
lean_ctor_set_uint8(v_s_915_, sizeof(void*)*3 + 4, v_importAll_901_);
v_module_764_ = v_module_910_;
v_s_765_ = v_s_915_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_error_x3f_897_);
lean_dec(v_module_764_);
lean_dec_ref(v_finalize_763_);
lean_dec_ref(v_input_762_);
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_941_);
v___x_943_ = v___x_903_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_imports_894_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_pos_895_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v___x_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3, v_badModifier_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 1, v_isModule_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 2, v_isMeta_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 3, v_isExported_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 4, v_importAll_901_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
v___jp_796_:
{
if (v___y_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = lean_uint32_dec_eq(v___y_800_, v___x_795_);
v___y_767_ = v___y_797_;
v___y_768_ = v___y_798_;
v___y_769_ = v___y_799_;
v___y_770_ = v___y_801_;
v___y_771_ = v___y_804_;
v___y_772_ = v___y_803_;
v___y_773_ = v___y_805_;
v___y_774_ = v___y_806_;
v___y_775_ = v___y_807_;
v___y_776_ = v___y_808_;
v___y_777_ = v___x_810_;
goto v___jp_766_;
}
else
{
v___y_767_ = v___y_797_;
v___y_768_ = v___y_798_;
v___y_769_ = v___y_799_;
v___y_770_ = v___y_801_;
v___y_771_ = v___y_804_;
v___y_772_ = v___y_803_;
v___y_773_ = v___y_805_;
v___y_774_ = v___y_806_;
v___y_775_ = v___y_807_;
v___y_776_ = v___y_808_;
v___y_777_ = v___y_802_;
goto v___jp_766_;
}
}
v___jp_811_:
{
if (v___y_824_ == 0)
{
uint32_t v___x_825_; uint8_t v___x_826_; 
v___x_825_ = 95;
v___x_826_ = lean_uint32_dec_eq(v___y_815_, v___x_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_isLetterLike(v___y_815_);
v___y_797_ = v___y_812_;
v___y_798_ = v___y_813_;
v___y_799_ = v___y_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___y_816_;
v___y_802_ = v___y_819_;
v___y_803_ = v___y_818_;
v___y_804_ = v___y_817_;
v___y_805_ = v___y_820_;
v___y_806_ = v___y_821_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_823_;
v___y_809_ = v___x_827_;
goto v___jp_796_;
}
else
{
v___y_797_ = v___y_812_;
v___y_798_ = v___y_813_;
v___y_799_ = v___y_814_;
v___y_800_ = v___y_815_;
v___y_801_ = v___y_816_;
v___y_802_ = v___y_819_;
v___y_803_ = v___y_818_;
v___y_804_ = v___y_817_;
v___y_805_ = v___y_820_;
v___y_806_ = v___y_821_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_823_;
v___y_809_ = v___x_826_;
goto v___jp_796_;
}
}
else
{
v___y_767_ = v___y_812_;
v___y_768_ = v___y_813_;
v___y_769_ = v___y_814_;
v___y_770_ = v___y_816_;
v___y_771_ = v___y_817_;
v___y_772_ = v___y_818_;
v___y_773_ = v___y_820_;
v___y_774_ = v___y_821_;
v___y_775_ = v___y_822_;
v___y_776_ = v___y_823_;
v___y_777_ = v___y_819_;
goto v___jp_766_;
}
}
v___jp_828_:
{
uint32_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 97;
v___x_842_ = lean_uint32_dec_le(v___x_841_, v___y_832_);
if (v___x_842_ == 0)
{
v___y_812_ = v___y_829_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_831_;
v___y_815_ = v___y_832_;
v___y_816_ = v___y_833_;
v___y_817_ = v___y_836_;
v___y_818_ = v___y_835_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v___y_839_;
v___y_823_ = v___y_840_;
v___y_824_ = v___x_842_;
goto v___jp_811_;
}
else
{
uint32_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 122;
v___x_844_ = lean_uint32_dec_le(v___y_832_, v___x_843_);
v___y_812_ = v___y_829_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_831_;
v___y_815_ = v___y_832_;
v___y_816_ = v___y_833_;
v___y_817_ = v___y_836_;
v___y_818_ = v___y_835_;
v___y_819_ = v___y_834_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v___y_839_;
v___y_823_ = v___y_840_;
v___y_824_ = v___x_844_;
goto v___jp_811_;
}
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_string_utf8_next_fast(v_input_762_, v_pos_783_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_848_);
v___x_850_ = v___x_792_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_imports_782_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_error_x3f_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3, v_badModifier_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3 + 1, v_isModule_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3 + 2, v_isMeta_787_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3 + 3, v_isExported_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3 + 4, v_importAll_789_);
v___x_850_ = v_reuseFailAlloc_872_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v_s_851_; lean_object* v_imports_852_; lean_object* v_pos_853_; uint8_t v_badModifier_854_; lean_object* v_error_x3f_855_; uint8_t v_isModule_856_; uint8_t v_isMeta_857_; uint8_t v_isExported_858_; uint8_t v_importAll_859_; lean_object* v___x_860_; lean_object* v_module_861_; uint32_t v_curr_862_; uint32_t v___x_863_; uint8_t v___x_864_; 
v_s_851_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_847_, v_curr_794_, v_input_762_, v___x_850_);
v_imports_852_ = lean_ctor_get(v_s_851_, 0);
lean_inc_ref(v_imports_852_);
v_pos_853_ = lean_ctor_get(v_s_851_, 1);
lean_inc(v_pos_853_);
v_badModifier_854_ = lean_ctor_get_uint8(v_s_851_, sizeof(void*)*3);
v_error_x3f_855_ = lean_ctor_get(v_s_851_, 2);
lean_inc(v_error_x3f_855_);
v_isModule_856_ = lean_ctor_get_uint8(v_s_851_, sizeof(void*)*3 + 1);
v_isMeta_857_ = lean_ctor_get_uint8(v_s_851_, sizeof(void*)*3 + 2);
v_isExported_858_ = lean_ctor_get_uint8(v_s_851_, sizeof(void*)*3 + 3);
v_importAll_859_ = lean_ctor_get_uint8(v_s_851_, sizeof(void*)*3 + 4);
v___x_860_ = lean_string_utf8_extract(v_input_762_, v_pos_783_, v_pos_853_);
lean_dec(v_pos_783_);
v_module_861_ = l_Lean_Name_str___override(v_module_764_, v___x_860_);
v_curr_862_ = lean_string_utf8_get(v_input_762_, v_pos_853_);
v___x_863_ = 46;
v___x_864_ = lean_uint32_dec_eq(v_curr_862_, v___x_863_);
if (v___x_864_ == 0)
{
v___y_767_ = v_imports_852_;
v___y_768_ = v_error_x3f_855_;
v___y_769_ = v_s_851_;
v___y_770_ = v_isExported_858_;
v___y_771_ = v_isModule_856_;
v___y_772_ = v_module_861_;
v___y_773_ = v_badModifier_854_;
v___y_774_ = v_pos_853_;
v___y_775_ = v_isMeta_857_;
v___y_776_ = v_importAll_859_;
v___y_777_ = v___x_864_;
goto v___jp_766_;
}
else
{
lean_object* v_i_865_; uint8_t v___x_866_; 
v_i_865_ = lean_string_utf8_next(v_input_762_, v_pos_853_);
v___x_866_ = lean_string_utf8_at_end(v_input_762_, v_i_865_);
if (v___x_866_ == 0)
{
uint32_t v_curr_867_; uint32_t v___x_868_; uint8_t v___x_869_; 
v_curr_867_ = lean_string_utf8_get_fast(v_input_762_, v_i_865_);
lean_dec(v_i_865_);
v___x_868_ = 65;
v___x_869_ = lean_uint32_dec_le(v___x_868_, v_curr_867_);
if (v___x_869_ == 0)
{
v___y_829_ = v_imports_852_;
v___y_830_ = v_error_x3f_855_;
v___y_831_ = v_s_851_;
v___y_832_ = v_curr_867_;
v___y_833_ = v_isExported_858_;
v___y_834_ = v___x_864_;
v___y_835_ = v_module_861_;
v___y_836_ = v_isModule_856_;
v___y_837_ = v_badModifier_854_;
v___y_838_ = v_pos_853_;
v___y_839_ = v_isMeta_857_;
v___y_840_ = v_importAll_859_;
goto v___jp_828_;
}
else
{
uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 90;
v___x_871_ = lean_uint32_dec_le(v_curr_867_, v___x_870_);
if (v___x_871_ == 0)
{
v___y_829_ = v_imports_852_;
v___y_830_ = v_error_x3f_855_;
v___y_831_ = v_s_851_;
v___y_832_ = v_curr_867_;
v___y_833_ = v_isExported_858_;
v___y_834_ = v___x_864_;
v___y_835_ = v_module_861_;
v___y_836_ = v_isModule_856_;
v___y_837_ = v_badModifier_854_;
v___y_838_ = v_pos_853_;
v___y_839_ = v_isMeta_857_;
v___y_840_ = v_importAll_859_;
goto v___jp_828_;
}
else
{
v___y_767_ = v_imports_852_;
v___y_768_ = v_error_x3f_855_;
v___y_769_ = v_s_851_;
v___y_770_ = v_isExported_858_;
v___y_771_ = v_isModule_856_;
v___y_772_ = v_module_861_;
v___y_773_ = v_badModifier_854_;
v___y_774_ = v_pos_853_;
v___y_775_ = v_isMeta_857_;
v___y_776_ = v_importAll_859_;
v___y_777_ = v___x_864_;
goto v___jp_766_;
}
}
}
else
{
lean_dec(v_i_865_);
v___y_767_ = v_imports_852_;
v___y_768_ = v_error_x3f_855_;
v___y_769_ = v_s_851_;
v___y_770_ = v_isExported_858_;
v___y_771_ = v_isModule_856_;
v___y_772_ = v_module_861_;
v___y_773_ = v_badModifier_854_;
v___y_774_ = v_pos_853_;
v___y_775_ = v_isMeta_857_;
v___y_776_ = v_importAll_859_;
v___y_777_ = v___x_845_;
goto v___jp_766_;
}
}
}
}
v___jp_873_:
{
if (v___y_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_792_);
lean_dec(v_error_x3f_785_);
lean_dec(v_module_764_);
lean_dec_ref(v_finalize_763_);
lean_dec_ref(v_input_762_);
v___x_875_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_876_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_876_, 0, v_imports_782_);
lean_ctor_set(v___x_876_, 1, v_pos_783_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3, v_badModifier_784_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 1, v_isModule_786_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 2, v_isMeta_787_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 3, v_isExported_788_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3 + 4, v_importAll_789_);
return v___x_876_;
}
else
{
v___y_847_ = v___y_874_;
goto v___jp_846_;
}
}
v___jp_877_:
{
if (v___y_878_ == 0)
{
uint32_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = 95;
v___x_880_ = lean_uint32_dec_eq(v_curr_794_, v___x_879_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; 
v___x_881_ = l_Lean_isLetterLike(v_curr_794_);
v___y_874_ = v___x_881_;
goto v___jp_873_;
}
else
{
v___y_874_ = v___x_880_;
goto v___jp_873_;
}
}
else
{
v___y_847_ = v___y_878_;
goto v___jp_846_;
}
}
v___jp_882_:
{
uint32_t v___x_883_; uint8_t v___x_884_; 
v___x_883_ = 97;
v___x_884_ = lean_uint32_dec_le(v___x_883_, v_curr_794_);
if (v___x_884_ == 0)
{
v___y_878_ = v___x_884_;
goto v___jp_877_;
}
else
{
uint32_t v___x_885_; uint8_t v___x_886_; 
v___x_885_ = 122;
v___x_886_ = lean_uint32_dec_le(v_curr_794_, v___x_885_);
v___y_878_ = v___x_886_;
goto v___jp_877_;
}
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec(v_module_764_);
lean_dec_ref(v_finalize_763_);
lean_dec_ref(v_input_762_);
v___x_950_ = l_Lean_ParseImports_State_mkEOIError(v_s_765_);
return v___x_950_;
}
v___jp_766_:
{
if (v___y_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v___y_774_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
v___x_778_ = lean_apply_3(v_finalize_763_, v___y_772_, v_input_762_, v___y_769_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v_s_780_; 
lean_dec_ref(v___y_769_);
v___x_779_ = lean_string_utf8_next(v_input_762_, v___y_774_);
lean_dec(v___y_774_);
v_s_780_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_780_, 0, v___y_767_);
lean_ctor_set(v_s_780_, 1, v___x_779_);
lean_ctor_set(v_s_780_, 2, v___y_768_);
lean_ctor_set_uint8(v_s_780_, sizeof(void*)*3, v___y_773_);
lean_ctor_set_uint8(v_s_780_, sizeof(void*)*3 + 1, v___y_771_);
lean_ctor_set_uint8(v_s_780_, sizeof(void*)*3 + 2, v___y_775_);
lean_ctor_set_uint8(v_s_780_, sizeof(void*)*3 + 3, v___y_770_);
lean_ctor_set_uint8(v_s_780_, sizeof(void*)*3 + 4, v___y_776_);
v_module_764_ = v___y_772_;
v_s_765_ = v_s_780_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_951_, lean_object* v_input_952_, lean_object* v_s_953_){
_start:
{
uint8_t v_isMeta_954_; uint8_t v_isExported_955_; uint8_t v_importAll_956_; lean_object* v_imp_957_; lean_object* v___x_958_; lean_object* v_s_959_; lean_object* v_imports_960_; lean_object* v_pos_961_; uint8_t v_badModifier_962_; lean_object* v_error_x3f_963_; uint8_t v_isModule_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_976_; 
v_isMeta_954_ = lean_ctor_get_uint8(v_s_953_, sizeof(void*)*3 + 2);
v_isExported_955_ = lean_ctor_get_uint8(v_s_953_, sizeof(void*)*3 + 3);
v_importAll_956_ = lean_ctor_get_uint8(v_s_953_, sizeof(void*)*3 + 4);
v_imp_957_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_957_, 0, v_module_951_);
lean_ctor_set_uint8(v_imp_957_, sizeof(void*)*1, v_importAll_956_);
lean_ctor_set_uint8(v_imp_957_, sizeof(void*)*1 + 1, v_isExported_955_);
lean_ctor_set_uint8(v_imp_957_, sizeof(void*)*1 + 2, v_isMeta_954_);
v___x_958_ = l_Lean_ParseImports_State_pushImport(v_imp_957_, v_s_953_);
v_s_959_ = l_Lean_ParseImports_whitespace(v_input_952_, v___x_958_);
v_imports_960_ = lean_ctor_get(v_s_959_, 0);
v_pos_961_ = lean_ctor_get(v_s_959_, 1);
v_badModifier_962_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3);
v_error_x3f_963_ = lean_ctor_get(v_s_959_, 2);
v_isModule_964_ = lean_ctor_get_uint8(v_s_959_, sizeof(void*)*3 + 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_s_959_);
if (v_isSharedCheck_976_ == 0)
{
v___x_966_ = v_s_959_;
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_error_x3f_963_);
lean_inc(v_pos_961_);
lean_inc(v_imports_960_);
lean_dec(v_s_959_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
v___x_968_ = 0;
if (v_isModule_964_ == 0)
{
uint8_t v___x_969_; lean_object* v___x_971_; 
v___x_969_ = 1;
if (v_isShared_967_ == 0)
{
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_imports_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_pos_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_error_x3f_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_badModifier_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_isModule_964_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*3 + 2, v___x_968_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*3 + 3, v___x_969_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*3 + 4, v___x_968_);
return v___x_971_;
}
}
else
{
lean_object* v___x_974_; 
if (v_isShared_967_ == 0)
{
v___x_974_ = v___x_966_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_imports_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_pos_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_error_x3f_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*3, v_badModifier_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*3 + 1, v_isModule_964_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3 + 2, v___x_968_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3 + 3, v___x_968_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3 + 4, v___x_968_);
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_977_, lean_object* v_input_978_, lean_object* v_s_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_977_, v_input_978_, v_s_979_);
lean_dec_ref(v_input_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_982_, lean_object* v_s_983_){
_start:
{
lean_object* v_finalize_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_finalize_984_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_985_ = lean_box(0);
v___x_986_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_982_, v_finalize_984_, v___x_985_, v_s_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_987_, lean_object* v_input_988_, lean_object* v_s_989_){
_start:
{
lean_object* v_pos_990_; lean_object* v_s_991_; lean_object* v_error_x3f_992_; 
v_pos_990_ = lean_ctor_get(v_s_989_, 1);
lean_inc(v_pos_990_);
v_s_991_ = lean_apply_2(v_p_987_, v_input_988_, v_s_989_);
v_error_x3f_992_ = lean_ctor_get(v_s_991_, 2);
lean_inc(v_error_x3f_992_);
if (lean_obj_tag(v_error_x3f_992_) == 1)
{
lean_object* v_imports_993_; uint8_t v_badModifier_994_; uint8_t v_isModule_995_; uint8_t v_isMeta_996_; uint8_t v_isExported_997_; uint8_t v_importAll_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_imports_993_ = lean_ctor_get(v_s_991_, 0);
v_badModifier_994_ = lean_ctor_get_uint8(v_s_991_, sizeof(void*)*3);
v_isModule_995_ = lean_ctor_get_uint8(v_s_991_, sizeof(void*)*3 + 1);
v_isMeta_996_ = lean_ctor_get_uint8(v_s_991_, sizeof(void*)*3 + 2);
v_isExported_997_ = lean_ctor_get_uint8(v_s_991_, sizeof(void*)*3 + 3);
v_importAll_998_ = lean_ctor_get_uint8(v_s_991_, sizeof(void*)*3 + 4);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_s_991_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; lean_object* v_unused_1007_; 
v_unused_1006_ = lean_ctor_get(v_s_991_, 2);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_s_991_, 1);
lean_dec(v_unused_1007_);
v___x_1000_ = v_s_991_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_imports_993_);
lean_dec(v_s_991_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v_pos_990_);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_imports_993_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_pos_990_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_error_x3f_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3, v_badModifier_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 1, v_isModule_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 2, v_isMeta_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 3, v_isExported_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 4, v_importAll_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_dec(v_error_x3f_992_);
lean_dec(v_pos_990_);
return v_s_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_1011_, lean_object* v_input_1012_, lean_object* v_s_1013_){
_start:
{
lean_object* v_pos_1014_; lean_object* v_s_1015_; lean_object* v_error_x3f_1016_; 
v_pos_1014_ = lean_ctor_get(v_s_1013_, 1);
lean_inc(v_pos_1014_);
lean_inc_ref(v_p_1011_);
lean_inc_ref(v_input_1012_);
v_s_1015_ = lean_apply_2(v_p_1011_, v_input_1012_, v_s_1013_);
v_error_x3f_1016_ = lean_ctor_get(v_s_1015_, 2);
lean_inc(v_error_x3f_1016_);
if (lean_obj_tag(v_error_x3f_1016_) == 1)
{
lean_object* v_imports_1017_; lean_object* v_pos_1018_; uint8_t v_isModule_1019_; uint8_t v_isMeta_1020_; uint8_t v_isExported_1021_; uint8_t v_importAll_1022_; uint8_t v___x_1023_; 
lean_dec_ref_known(v_error_x3f_1016_, 1);
lean_dec_ref(v_input_1012_);
lean_dec_ref(v_p_1011_);
v_imports_1017_ = lean_ctor_get(v_s_1015_, 0);
lean_inc_ref(v_imports_1017_);
v_pos_1018_ = lean_ctor_get(v_s_1015_, 1);
lean_inc(v_pos_1018_);
v_isModule_1019_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 1);
v_isMeta_1020_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 2);
v_isExported_1021_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 3);
v_importAll_1022_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 4);
v___x_1023_ = lean_nat_dec_eq(v_pos_1018_, v_pos_1014_);
lean_dec(v_pos_1014_);
if (v___x_1023_ == 0)
{
lean_dec(v_pos_1018_);
lean_dec_ref(v_imports_1017_);
return v_s_1015_;
}
else
{
lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v_isSharedCheck_1032_ = !lean_is_exclusive(v_s_1015_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; 
v_unused_1033_ = lean_ctor_get(v_s_1015_, 2);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_s_1015_, 1);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_s_1015_, 0);
lean_dec(v_unused_1035_);
v___x_1025_ = v_s_1015_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v_s_1015_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = 0;
v___x_1028_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 2, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_imports_1017_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_pos_1018_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___x_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 1, v_isModule_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 2, v_isMeta_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 3, v_isExported_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 4, v_importAll_1022_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3, v___x_1027_);
return v___x_1030_;
}
}
}
}
else
{
uint8_t v_badModifier_1036_; 
lean_dec(v_error_x3f_1016_);
v_badModifier_1036_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3);
if (v_badModifier_1036_ == 0)
{
lean_dec(v_pos_1014_);
v_s_1013_ = v_s_1015_;
goto _start;
}
else
{
lean_object* v_imports_1038_; uint8_t v_isModule_1039_; uint8_t v_isMeta_1040_; uint8_t v_isExported_1041_; uint8_t v_importAll_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v_input_1012_);
lean_dec_ref(v_p_1011_);
v_imports_1038_ = lean_ctor_get(v_s_1015_, 0);
v_isModule_1039_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 1);
v_isMeta_1040_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 2);
v_isExported_1041_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 3);
v_importAll_1042_ = lean_ctor_get_uint8(v_s_1015_, sizeof(void*)*3 + 4);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1015_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; lean_object* v_unused_1053_; 
v_unused_1052_ = lean_ctor_get(v_s_1015_, 2);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_s_1015_, 1);
lean_dec(v_unused_1053_);
v___x_1044_ = v_s_1015_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_imports_1038_);
lean_dec(v_s_1015_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1046_ = 0;
v___x_1047_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 2, v___x_1047_);
lean_ctor_set(v___x_1044_, 1, v_pos_1014_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_imports_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_pos_1014_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v___x_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 1, v_isModule_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 2, v_isMeta_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 3, v_isExported_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*3 + 4, v_importAll_1042_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*3, v___x_1046_);
return v___x_1049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1054_, lean_object* v_s_1055_){
_start:
{
if (v_isModule_1054_ == 0)
{
lean_object* v_imports_1056_; lean_object* v_pos_1057_; uint8_t v_badModifier_1058_; lean_object* v_error_x3f_1059_; uint8_t v_isMeta_1060_; uint8_t v_importAll_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_imports_1056_ = lean_ctor_get(v_s_1055_, 0);
v_pos_1057_ = lean_ctor_get(v_s_1055_, 1);
v_badModifier_1058_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3);
v_error_x3f_1059_ = lean_ctor_get(v_s_1055_, 2);
v_isMeta_1060_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3 + 2);
v_importAll_1061_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3 + 4);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_s_1055_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_s_1055_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_error_x3f_1059_);
lean_inc(v_pos_1057_);
lean_inc(v_imports_1056_);
lean_dec(v_s_1055_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
uint8_t v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = 1;
if (v_isShared_1064_ == 0)
{
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_imports_1056_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_pos_1057_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_error_x3f_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1068_, sizeof(void*)*3, v_badModifier_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1068_, sizeof(void*)*3 + 2, v_isMeta_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1068_, sizeof(void*)*3 + 4, v_importAll_1061_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*3 + 1, v_isModule_1054_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*3 + 3, v___x_1065_);
return v___x_1067_;
}
}
}
else
{
lean_object* v_imports_1070_; lean_object* v_pos_1071_; uint8_t v_badModifier_1072_; lean_object* v_error_x3f_1073_; uint8_t v_isMeta_1074_; uint8_t v_importAll_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_imports_1070_ = lean_ctor_get(v_s_1055_, 0);
v_pos_1071_ = lean_ctor_get(v_s_1055_, 1);
v_badModifier_1072_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3);
v_error_x3f_1073_ = lean_ctor_get(v_s_1055_, 2);
v_isMeta_1074_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3 + 2);
v_importAll_1075_ = lean_ctor_get_uint8(v_s_1055_, sizeof(void*)*3 + 4);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_s_1055_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_s_1055_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_error_x3f_1073_);
lean_inc(v_pos_1071_);
lean_inc(v_imports_1070_);
lean_dec(v_s_1055_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint8_t v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = 0;
if (v_isShared_1078_ == 0)
{
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_imports_1070_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_pos_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_error_x3f_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3, v_badModifier_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 2, v_isMeta_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*3 + 4, v_importAll_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3 + 1, v_isModule_1054_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3 + 3, v___x_1079_);
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* v_isModule_1084_, lean_object* v_s_1085_){
_start:
{
uint8_t v_isModule_boxed_1086_; lean_object* v_res_1087_; 
v_isModule_boxed_1086_ = lean_unbox(v_isModule_1084_);
v_res_1087_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_1086_, v_s_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1088_, lean_object* v_x_1089_, lean_object* v_s_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1088_, v_s_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1092_, lean_object* v_x_1093_, lean_object* v_s_1094_){
_start:
{
uint8_t v_isModule_boxed_1095_; lean_object* v_res_1096_; 
v_isModule_boxed_1095_ = lean_unbox(v_isModule_1092_);
v_res_1096_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1095_, v_x_1093_, v_s_1094_);
lean_dec_ref(v_x_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1097_){
_start:
{
lean_object* v_imports_1098_; lean_object* v_pos_1099_; uint8_t v_badModifier_1100_; lean_object* v_error_x3f_1101_; uint8_t v_isModule_1102_; uint8_t v_isMeta_1103_; uint8_t v_isExported_1104_; uint8_t v_importAll_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1116_; 
v_imports_1098_ = lean_ctor_get(v_s_1097_, 0);
v_pos_1099_ = lean_ctor_get(v_s_1097_, 1);
v_badModifier_1100_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*3);
v_error_x3f_1101_ = lean_ctor_get(v_s_1097_, 2);
v_isModule_1102_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*3 + 1);
v_isMeta_1103_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*3 + 2);
v_isExported_1104_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*3 + 3);
v_importAll_1105_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*3 + 4);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_s_1097_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1107_ = v_s_1097_;
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_error_x3f_1101_);
lean_inc(v_pos_1099_);
lean_inc(v_imports_1098_);
lean_dec(v_s_1097_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1116_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
uint8_t v___x_1109_; 
v___x_1109_ = 1;
if (v_isModule_1102_ == 0)
{
lean_object* v___x_1111_; 
if (v_isShared_1108_ == 0)
{
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_imports_1098_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_pos_1099_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_error_x3f_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 1, v_isModule_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 2, v_isMeta_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 3, v_isExported_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 4, v_importAll_1105_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3, v___x_1109_);
return v___x_1111_;
}
}
else
{
lean_object* v___x_1114_; 
if (v_isShared_1108_ == 0)
{
v___x_1114_ = v___x_1107_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_imports_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_pos_1099_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_error_x3f_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3, v_badModifier_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3 + 1, v_isModule_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3 + 3, v_isExported_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3 + 4, v_importAll_1105_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*3 + 2, v___x_1109_);
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1117_, lean_object* v_s_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_ParseImports_setMeta___redArg(v_s_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1120_, lean_object* v_s_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_ParseImports_setMeta(v_x_1120_, v_s_1121_);
lean_dec_ref(v_x_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1123_){
_start:
{
lean_object* v_imports_1124_; lean_object* v_pos_1125_; uint8_t v_badModifier_1126_; lean_object* v_error_x3f_1127_; uint8_t v_isModule_1128_; uint8_t v_isMeta_1129_; uint8_t v_isExported_1130_; uint8_t v_importAll_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1142_; 
v_imports_1124_ = lean_ctor_get(v_s_1123_, 0);
v_pos_1125_ = lean_ctor_get(v_s_1123_, 1);
v_badModifier_1126_ = lean_ctor_get_uint8(v_s_1123_, sizeof(void*)*3);
v_error_x3f_1127_ = lean_ctor_get(v_s_1123_, 2);
v_isModule_1128_ = lean_ctor_get_uint8(v_s_1123_, sizeof(void*)*3 + 1);
v_isMeta_1129_ = lean_ctor_get_uint8(v_s_1123_, sizeof(void*)*3 + 2);
v_isExported_1130_ = lean_ctor_get_uint8(v_s_1123_, sizeof(void*)*3 + 3);
v_importAll_1131_ = lean_ctor_get_uint8(v_s_1123_, sizeof(void*)*3 + 4);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_s_1123_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1133_ = v_s_1123_;
v_isShared_1134_ = v_isSharedCheck_1142_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_error_x3f_1127_);
lean_inc(v_pos_1125_);
lean_inc(v_imports_1124_);
lean_dec(v_s_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1142_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; 
v___x_1135_ = 1;
if (v_isModule_1128_ == 0)
{
lean_object* v___x_1137_; 
if (v_isShared_1134_ == 0)
{
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_imports_1124_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_pos_1125_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_error_x3f_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 1, v_isModule_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 2, v_isMeta_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 3, v_isExported_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1138_, sizeof(void*)*3 + 4, v_importAll_1131_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*3, v___x_1135_);
return v___x_1137_;
}
}
else
{
lean_object* v___x_1140_; 
if (v_isShared_1134_ == 0)
{
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_imports_1124_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_pos_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_error_x3f_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3, v_badModifier_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3 + 1, v_isModule_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3 + 2, v_isMeta_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3 + 4, v_importAll_1131_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*3 + 3, v___x_1135_);
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1143_, lean_object* v_s_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_ParseImports_setExported___redArg(v_s_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1146_, lean_object* v_s_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_ParseImports_setExported(v_x_1146_, v_s_1147_);
lean_dec_ref(v_x_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1149_){
_start:
{
lean_object* v_imports_1150_; lean_object* v_pos_1151_; uint8_t v_badModifier_1152_; lean_object* v_error_x3f_1153_; uint8_t v_isModule_1154_; uint8_t v_isMeta_1155_; uint8_t v_isExported_1156_; uint8_t v_importAll_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1168_; 
v_imports_1150_ = lean_ctor_get(v_s_1149_, 0);
v_pos_1151_ = lean_ctor_get(v_s_1149_, 1);
v_badModifier_1152_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3);
v_error_x3f_1153_ = lean_ctor_get(v_s_1149_, 2);
v_isModule_1154_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 1);
v_isMeta_1155_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 2);
v_isExported_1156_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 3);
v_importAll_1157_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 4);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_s_1149_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1159_ = v_s_1149_;
v_isShared_1160_ = v_isSharedCheck_1168_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_error_x3f_1153_);
lean_inc(v_pos_1151_);
lean_inc(v_imports_1150_);
lean_dec(v_s_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1168_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___x_1161_; 
v___x_1161_ = 1;
if (v_isModule_1154_ == 0)
{
lean_object* v___x_1163_; 
if (v_isShared_1160_ == 0)
{
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_imports_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_pos_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_error_x3f_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 1, v_isModule_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 2, v_isMeta_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 3, v_isExported_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*3 + 4, v_importAll_1157_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3, v___x_1161_);
return v___x_1163_;
}
}
else
{
lean_object* v___x_1166_; 
if (v_isShared_1160_ == 0)
{
v___x_1166_ = v___x_1159_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_imports_1150_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_pos_1151_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_error_x3f_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3, v_badModifier_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3 + 1, v_isModule_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3 + 2, v_isMeta_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3 + 3, v_isExported_1156_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*3 + 4, v___x_1161_);
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1169_, lean_object* v_s_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1172_, lean_object* v_s_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_ParseImports_setImportAll(v_x_1172_, v_s_1173_);
lean_dec_ref(v_x_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1178_, lean_object* v_input_1179_, lean_object* v_s_1180_, lean_object* v_i_1181_, lean_object* v_j_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_string_utf8_at_end(v_k_1178_, v_i_1181_);
if (v___x_1183_ == 0)
{
uint8_t v___x_1184_; lean_object* v_s_1186_; uint8_t v___x_1192_; 
v___x_1184_ = 1;
v___x_1192_ = lean_string_utf8_at_end(v_input_1179_, v_j_1182_);
if (v___x_1192_ == 0)
{
uint32_t v_curr_u2081_1193_; uint32_t v_curr_u2082_1194_; uint8_t v___x_1195_; 
v_curr_u2081_1193_ = lean_string_utf8_get_fast(v_k_1178_, v_i_1181_);
v_curr_u2082_1194_ = lean_string_utf8_get_fast(v_input_1179_, v_j_1182_);
v___x_1195_ = lean_uint32_dec_eq(v_curr_u2081_1193_, v_curr_u2082_1194_);
if (v___x_1195_ == 0)
{
lean_dec(v_j_1182_);
lean_dec(v_i_1181_);
v_s_1186_ = v_s_1180_;
goto v___jp_1185_;
}
else
{
if (v___x_1192_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_string_utf8_next_fast(v_k_1178_, v_i_1181_);
lean_dec(v_i_1181_);
v___x_1197_ = lean_string_utf8_next_fast(v_input_1179_, v_j_1182_);
lean_dec(v_j_1182_);
v_i_1181_ = v___x_1196_;
v_j_1182_ = v___x_1197_;
goto _start;
}
else
{
lean_dec(v_j_1182_);
lean_dec(v_i_1181_);
v_s_1186_ = v_s_1180_;
goto v___jp_1185_;
}
}
}
else
{
lean_dec(v_j_1182_);
lean_dec(v_i_1181_);
v_s_1186_ = v_s_1180_;
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1188_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*1, v___x_1183_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*1 + 1, v___x_1184_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*1 + 2, v___x_1184_);
v___x_1189_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1, v___x_1183_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1 + 1, v___x_1184_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1 + 2, v___x_1183_);
v___x_1190_ = l_Lean_ParseImports_State_pushImport(v___x_1189_, v_s_1186_);
v___x_1191_ = l_Lean_ParseImports_State_pushImport(v___x_1188_, v___x_1190_);
return v___x_1191_;
}
}
else
{
lean_object* v_imports_1199_; uint8_t v_badModifier_1200_; lean_object* v_error_x3f_1201_; uint8_t v_isModule_1202_; uint8_t v_isMeta_1203_; uint8_t v_isExported_1204_; uint8_t v_importAll_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_i_1181_);
v_imports_1199_ = lean_ctor_get(v_s_1180_, 0);
v_badModifier_1200_ = lean_ctor_get_uint8(v_s_1180_, sizeof(void*)*3);
v_error_x3f_1201_ = lean_ctor_get(v_s_1180_, 2);
v_isModule_1202_ = lean_ctor_get_uint8(v_s_1180_, sizeof(void*)*3 + 1);
v_isMeta_1203_ = lean_ctor_get_uint8(v_s_1180_, sizeof(void*)*3 + 2);
v_isExported_1204_ = lean_ctor_get_uint8(v_s_1180_, sizeof(void*)*3 + 3);
v_importAll_1205_ = lean_ctor_get_uint8(v_s_1180_, sizeof(void*)*3 + 4);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_s_1180_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_s_1180_, 1);
lean_dec(v_unused_1214_);
v___x_1207_ = v_s_1180_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_error_x3f_1201_);
lean_inc(v_imports_1199_);
lean_dec(v_s_1180_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v_j_1182_);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_imports_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_j_1182_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_error_x3f_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3, v_badModifier_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3 + 1, v_isModule_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3 + 2, v_isMeta_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3 + 3, v_isExported_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3 + 4, v_importAll_1205_);
v___x_1210_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_ParseImports_whitespace(v_input_1179_, v___x_1210_);
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1215_, lean_object* v_input_1216_, lean_object* v_s_1217_, lean_object* v_i_1218_, lean_object* v_j_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1215_, v_input_1216_, v_s_1217_, v_i_1218_, v_j_1219_);
lean_dec_ref(v_input_1216_);
lean_dec_ref(v_k_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1224_, lean_object* v_input_1225_, lean_object* v_s_1226_, lean_object* v_i_1227_, lean_object* v_j_1228_){
_start:
{
lean_object* v_s_1230_; uint8_t v___x_1247_; 
v___x_1247_ = lean_string_utf8_at_end(v_k_1224_, v_i_1227_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_string_utf8_at_end(v_input_1225_, v_j_1228_);
if (v___x_1248_ == 0)
{
uint32_t v_curr_u2081_1249_; uint32_t v_curr_u2082_1250_; uint8_t v___x_1251_; 
v_curr_u2081_1249_ = lean_string_utf8_get_fast(v_k_1224_, v_i_1227_);
v_curr_u2082_1250_ = lean_string_utf8_get_fast(v_input_1225_, v_j_1228_);
v___x_1251_ = lean_uint32_dec_eq(v_curr_u2081_1249_, v_curr_u2082_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_j_1228_);
lean_dec(v_i_1227_);
v_s_1230_ = v_s_1226_;
goto v___jp_1229_;
}
else
{
if (v___x_1248_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_string_utf8_next_fast(v_k_1224_, v_i_1227_);
lean_dec(v_i_1227_);
v___x_1253_ = lean_string_utf8_next_fast(v_input_1225_, v_j_1228_);
lean_dec(v_j_1228_);
v_i_1227_ = v___x_1252_;
v_j_1228_ = v___x_1253_;
goto _start;
}
else
{
lean_dec(v_j_1228_);
lean_dec(v_i_1227_);
v_s_1230_ = v_s_1226_;
goto v___jp_1229_;
}
}
}
else
{
lean_dec(v_j_1228_);
lean_dec(v_i_1227_);
v_s_1230_ = v_s_1226_;
goto v___jp_1229_;
}
}
else
{
lean_object* v_imports_1255_; uint8_t v_badModifier_1256_; lean_object* v_error_x3f_1257_; uint8_t v_isModule_1258_; uint8_t v_isMeta_1259_; uint8_t v_isExported_1260_; uint8_t v_importAll_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_i_1227_);
v_imports_1255_ = lean_ctor_get(v_s_1226_, 0);
v_badModifier_1256_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*3);
v_error_x3f_1257_ = lean_ctor_get(v_s_1226_, 2);
v_isModule_1258_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*3 + 1);
v_isMeta_1259_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*3 + 2);
v_isExported_1260_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*3 + 3);
v_importAll_1261_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*3 + 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_s_1226_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v_s_1226_, 1);
lean_dec(v_unused_1270_);
v___x_1263_ = v_s_1226_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_error_x3f_1257_);
lean_inc(v_imports_1255_);
lean_dec(v_s_1226_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_j_1228_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_imports_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_j_1228_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_error_x3f_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*3, v_badModifier_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*3 + 1, v_isModule_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*3 + 2, v_isMeta_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*3 + 3, v_isExported_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*3 + 4, v_importAll_1261_);
v___x_1266_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_ParseImports_whitespace(v_input_1225_, v___x_1266_);
return v___x_1267_;
}
}
}
v___jp_1229_:
{
lean_object* v_imports_1231_; lean_object* v_pos_1232_; uint8_t v_badModifier_1233_; uint8_t v_isModule_1234_; uint8_t v_isMeta_1235_; uint8_t v_isExported_1236_; uint8_t v_importAll_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_imports_1231_ = lean_ctor_get(v_s_1230_, 0);
v_pos_1232_ = lean_ctor_get(v_s_1230_, 1);
v_badModifier_1233_ = lean_ctor_get_uint8(v_s_1230_, sizeof(void*)*3);
v_isModule_1234_ = lean_ctor_get_uint8(v_s_1230_, sizeof(void*)*3 + 1);
v_isMeta_1235_ = lean_ctor_get_uint8(v_s_1230_, sizeof(void*)*3 + 2);
v_isExported_1236_ = lean_ctor_get_uint8(v_s_1230_, sizeof(void*)*3 + 3);
v_importAll_1237_ = lean_ctor_get_uint8(v_s_1230_, sizeof(void*)*3 + 4);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_s_1230_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_s_1230_, 2);
lean_dec(v_unused_1246_);
v___x_1239_ = v_s_1230_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_pos_1232_);
lean_inc(v_imports_1231_);
lean_dec(v_s_1230_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_imports_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_pos_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v___x_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, sizeof(void*)*3, v_badModifier_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, sizeof(void*)*3 + 1, v_isModule_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, sizeof(void*)*3 + 2, v_isMeta_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, sizeof(void*)*3 + 3, v_isExported_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1244_, sizeof(void*)*3 + 4, v_importAll_1237_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1271_, lean_object* v_input_1272_, lean_object* v_s_1273_, lean_object* v_i_1274_, lean_object* v_j_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1271_, v_input_1272_, v_s_1273_, v_i_1274_, v_j_1275_);
lean_dec_ref(v_input_1272_);
lean_dec_ref(v_k_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1277_, lean_object* v_input_1278_, lean_object* v_s_1279_, lean_object* v_i_1280_, lean_object* v_j_1281_){
_start:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_string_utf8_at_end(v_k_1277_, v_i_1280_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_string_utf8_at_end(v_input_1278_, v_j_1281_);
if (v___x_1283_ == 0)
{
uint32_t v_curr_u2081_1284_; uint32_t v_curr_u2082_1285_; uint8_t v___x_1286_; 
v_curr_u2081_1284_ = lean_string_utf8_get_fast(v_k_1277_, v_i_1280_);
v_curr_u2082_1285_ = lean_string_utf8_get_fast(v_input_1278_, v_j_1281_);
v___x_1286_ = lean_uint32_dec_eq(v_curr_u2081_1284_, v_curr_u2082_1285_);
if (v___x_1286_ == 0)
{
lean_dec(v_j_1281_);
lean_dec(v_i_1280_);
return v_s_1279_;
}
else
{
if (v___x_1283_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_string_utf8_next_fast(v_k_1277_, v_i_1280_);
lean_dec(v_i_1280_);
v___x_1288_ = lean_string_utf8_next_fast(v_input_1278_, v_j_1281_);
lean_dec(v_j_1281_);
v_i_1280_ = v___x_1287_;
v_j_1281_ = v___x_1288_;
goto _start;
}
else
{
lean_dec(v_j_1281_);
lean_dec(v_i_1280_);
return v_s_1279_;
}
}
}
else
{
lean_dec(v_j_1281_);
lean_dec(v_i_1280_);
return v_s_1279_;
}
}
else
{
lean_object* v_imports_1290_; uint8_t v_badModifier_1291_; lean_object* v_error_x3f_1292_; uint8_t v_isModule_1293_; uint8_t v_isMeta_1294_; uint8_t v_isExported_1295_; uint8_t v_importAll_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_i_1280_);
v_imports_1290_ = lean_ctor_get(v_s_1279_, 0);
v_badModifier_1291_ = lean_ctor_get_uint8(v_s_1279_, sizeof(void*)*3);
v_error_x3f_1292_ = lean_ctor_get(v_s_1279_, 2);
v_isModule_1293_ = lean_ctor_get_uint8(v_s_1279_, sizeof(void*)*3 + 1);
v_isMeta_1294_ = lean_ctor_get_uint8(v_s_1279_, sizeof(void*)*3 + 2);
v_isExported_1295_ = lean_ctor_get_uint8(v_s_1279_, sizeof(void*)*3 + 3);
v_importAll_1296_ = lean_ctor_get_uint8(v_s_1279_, sizeof(void*)*3 + 4);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_s_1279_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_s_1279_, 1);
lean_dec(v_unused_1306_);
v___x_1298_ = v_s_1279_;
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_error_x3f_1292_);
lean_inc(v_imports_1290_);
lean_dec(v_s_1279_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v_j_1281_);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_imports_1290_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_j_1281_);
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
v___x_1302_ = l_Lean_ParseImports_whitespace(v_input_1278_, v___x_1301_);
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
uint32_t v_curr_u2081_1320_; uint32_t v_curr_u2082_1321_; uint8_t v___x_1322_; 
v_curr_u2081_1320_ = lean_string_utf8_get_fast(v_k_1313_, v_i_1316_);
v_curr_u2082_1321_ = lean_string_utf8_get_fast(v_input_1314_, v_j_1317_);
v___x_1322_ = lean_uint32_dec_eq(v_curr_u2081_1320_, v_curr_u2082_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_j_1317_);
lean_dec(v_i_1316_);
return v_s_1315_;
}
else
{
if (v___x_1319_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_string_utf8_next_fast(v_k_1313_, v_i_1316_);
lean_dec(v_i_1316_);
v___x_1324_ = lean_string_utf8_next_fast(v_input_1314_, v_j_1317_);
lean_dec(v_j_1317_);
v_i_1316_ = v___x_1323_;
v_j_1317_ = v___x_1324_;
goto _start;
}
else
{
lean_dec(v_j_1317_);
lean_dec(v_i_1316_);
return v_s_1315_;
}
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
lean_object* v_imports_1326_; uint8_t v_badModifier_1327_; lean_object* v_error_x3f_1328_; uint8_t v_isModule_1329_; uint8_t v_isMeta_1330_; uint8_t v_isExported_1331_; uint8_t v_importAll_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_i_1316_);
v_imports_1326_ = lean_ctor_get(v_s_1315_, 0);
v_badModifier_1327_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3);
v_error_x3f_1328_ = lean_ctor_get(v_s_1315_, 2);
v_isModule_1329_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 1);
v_isMeta_1330_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 2);
v_isExported_1331_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 3);
v_importAll_1332_ = lean_ctor_get_uint8(v_s_1315_, sizeof(void*)*3 + 4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_s_1315_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_s_1315_, 1);
lean_dec(v_unused_1342_);
v___x_1334_ = v_s_1315_;
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_error_x3f_1328_);
lean_inc(v_imports_1326_);
lean_dec(v_s_1315_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v_j_1317_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_imports_1326_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_j_1317_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_error_x3f_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3, v_badModifier_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3 + 1, v_isModule_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3 + 2, v_isMeta_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3 + 3, v_isExported_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3 + 4, v_importAll_1332_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = l_Lean_ParseImports_whitespace(v_input_1314_, v___x_1337_);
v___x_1339_ = l_Lean_ParseImports_setExported___redArg(v___x_1338_);
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1343_, lean_object* v_input_1344_, lean_object* v_s_1345_, lean_object* v_i_1346_, lean_object* v_j_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1343_, v_input_1344_, v_s_1345_, v_i_1346_, v_j_1347_);
lean_dec_ref(v_input_1344_);
lean_dec_ref(v_k_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1349_, lean_object* v_input_1350_, lean_object* v_s_1351_, lean_object* v_i_1352_, lean_object* v_j_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_string_utf8_at_end(v_k_1349_, v_i_1352_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_string_utf8_at_end(v_input_1350_, v_j_1353_);
if (v___x_1355_ == 0)
{
uint32_t v_curr_u2081_1356_; uint32_t v_curr_u2082_1357_; uint8_t v___x_1358_; 
v_curr_u2081_1356_ = lean_string_utf8_get_fast(v_k_1349_, v_i_1352_);
v_curr_u2082_1357_ = lean_string_utf8_get_fast(v_input_1350_, v_j_1353_);
v___x_1358_ = lean_uint32_dec_eq(v_curr_u2081_1356_, v_curr_u2082_1357_);
if (v___x_1358_ == 0)
{
lean_dec(v_j_1353_);
lean_dec(v_i_1352_);
return v_s_1351_;
}
else
{
if (v___x_1355_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_string_utf8_next_fast(v_k_1349_, v_i_1352_);
lean_dec(v_i_1352_);
v___x_1360_ = lean_string_utf8_next_fast(v_input_1350_, v_j_1353_);
lean_dec(v_j_1353_);
v_i_1352_ = v___x_1359_;
v_j_1353_ = v___x_1360_;
goto _start;
}
else
{
lean_dec(v_j_1353_);
lean_dec(v_i_1352_);
return v_s_1351_;
}
}
}
else
{
lean_dec(v_j_1353_);
lean_dec(v_i_1352_);
return v_s_1351_;
}
}
else
{
lean_object* v_imports_1362_; uint8_t v_badModifier_1363_; lean_object* v_error_x3f_1364_; uint8_t v_isModule_1365_; uint8_t v_isMeta_1366_; uint8_t v_isExported_1367_; uint8_t v_importAll_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_i_1352_);
v_imports_1362_ = lean_ctor_get(v_s_1351_, 0);
v_badModifier_1363_ = lean_ctor_get_uint8(v_s_1351_, sizeof(void*)*3);
v_error_x3f_1364_ = lean_ctor_get(v_s_1351_, 2);
v_isModule_1365_ = lean_ctor_get_uint8(v_s_1351_, sizeof(void*)*3 + 1);
v_isMeta_1366_ = lean_ctor_get_uint8(v_s_1351_, sizeof(void*)*3 + 2);
v_isExported_1367_ = lean_ctor_get_uint8(v_s_1351_, sizeof(void*)*3 + 3);
v_importAll_1368_ = lean_ctor_get_uint8(v_s_1351_, sizeof(void*)*3 + 4);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_s_1351_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v_s_1351_, 1);
lean_dec(v_unused_1378_);
v___x_1370_ = v_s_1351_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_error_x3f_1364_);
lean_inc(v_imports_1362_);
lean_dec(v_s_1351_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_j_1353_);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_imports_1362_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_j_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_error_x3f_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*3, v_badModifier_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*3 + 1, v_isModule_1365_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*3 + 2, v_isMeta_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*3 + 3, v_isExported_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*3 + 4, v_importAll_1368_);
v___x_1373_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = l_Lean_ParseImports_whitespace(v_input_1350_, v___x_1373_);
v___x_1375_ = l_Lean_ParseImports_setMeta___redArg(v___x_1374_);
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1379_, lean_object* v_input_1380_, lean_object* v_s_1381_, lean_object* v_i_1382_, lean_object* v_j_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1379_, v_input_1380_, v_s_1381_, v_i_1382_, v_j_1383_);
lean_dec_ref(v_input_1380_);
lean_dec_ref(v_k_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1389_, lean_object* v_s_1390_){
_start:
{
lean_object* v_pos_1391_; lean_object* v___y_1393_; lean_object* v_imports_1394_; lean_object* v_pos_1395_; uint8_t v_isModule_1396_; uint8_t v_isMeta_1397_; uint8_t v_isExported_1398_; uint8_t v_importAll_1399_; lean_object* v___y_1405_; lean_object* v___y_1432_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_error_x3f_1464_; 
v_pos_1391_ = lean_ctor_get(v_s_1390_, 1);
lean_inc_n(v_pos_1391_, 2);
v___x_1461_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1461_, v_input_1389_, v_s_1390_, v___x_1462_, v_pos_1391_);
v_error_x3f_1464_ = lean_ctor_get(v___x_1463_, 2);
lean_inc(v_error_x3f_1464_);
if (lean_obj_tag(v_error_x3f_1464_) == 1)
{
lean_dec_ref_known(v_error_x3f_1464_, 1);
v___y_1432_ = v___x_1463_;
goto v___jp_1431_;
}
else
{
lean_object* v_pos_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_error_x3f_1468_; 
lean_dec(v_error_x3f_1464_);
v_pos_1465_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_pos_1465_);
v___x_1466_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1467_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1466_, v_input_1389_, v___x_1463_, v___x_1462_, v_pos_1465_);
v_error_x3f_1468_ = lean_ctor_get(v___x_1467_, 2);
lean_inc(v_error_x3f_1468_);
if (lean_obj_tag(v_error_x3f_1468_) == 1)
{
lean_dec_ref_known(v_error_x3f_1468_, 1);
v___y_1432_ = v___x_1467_;
goto v___jp_1431_;
}
else
{
lean_object* v_pos_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_error_x3f_1468_);
v_pos_1469_ = lean_ctor_get(v___x_1467_, 1);
lean_inc(v_pos_1469_);
v___x_1470_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1471_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1470_, v_input_1389_, v___x_1467_, v___x_1462_, v_pos_1469_);
v___y_1432_ = v___x_1471_;
goto v___jp_1431_;
}
}
v___jp_1392_:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_eq(v_pos_1395_, v_pos_1391_);
lean_dec(v_pos_1391_);
if (v___x_1400_ == 0)
{
lean_dec(v_pos_1395_);
lean_dec_ref(v_imports_1394_);
return v___y_1393_;
}
else
{
uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec_ref(v___y_1393_);
v___x_1401_ = 0;
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1403_, 0, v_imports_1394_);
lean_ctor_set(v___x_1403_, 1, v_pos_1395_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3, v___x_1401_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3 + 1, v_isModule_1396_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3 + 2, v_isMeta_1397_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3 + 3, v_isExported_1398_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3 + 4, v_importAll_1399_);
return v___x_1403_;
}
}
v___jp_1404_:
{
lean_object* v_error_x3f_1406_; 
v_error_x3f_1406_ = lean_ctor_get(v___y_1405_, 2);
if (lean_obj_tag(v_error_x3f_1406_) == 1)
{
lean_object* v_imports_1407_; lean_object* v_pos_1408_; uint8_t v_isModule_1409_; uint8_t v_isMeta_1410_; uint8_t v_isExported_1411_; uint8_t v_importAll_1412_; 
lean_dec_ref(v_input_1389_);
v_imports_1407_ = lean_ctor_get(v___y_1405_, 0);
lean_inc_ref(v_imports_1407_);
v_pos_1408_ = lean_ctor_get(v___y_1405_, 1);
lean_inc(v_pos_1408_);
v_isModule_1409_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 1);
v_isMeta_1410_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 2);
v_isExported_1411_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 3);
v_importAll_1412_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 4);
v___y_1393_ = v___y_1405_;
v_imports_1394_ = v_imports_1407_;
v_pos_1395_ = v_pos_1408_;
v_isModule_1396_ = v_isModule_1409_;
v_isMeta_1397_ = v_isMeta_1410_;
v_isExported_1398_ = v_isExported_1411_;
v_importAll_1399_ = v_importAll_1412_;
goto v___jp_1392_;
}
else
{
uint8_t v_badModifier_1413_; 
v_badModifier_1413_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3);
if (v_badModifier_1413_ == 0)
{
lean_dec(v_pos_1391_);
v_s_1390_ = v___y_1405_;
goto _start;
}
else
{
lean_object* v_imports_1415_; uint8_t v_isModule_1416_; uint8_t v_isMeta_1417_; uint8_t v_isExported_1418_; uint8_t v_importAll_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v_input_1389_);
v_imports_1415_ = lean_ctor_get(v___y_1405_, 0);
v_isModule_1416_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 1);
v_isMeta_1417_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 2);
v_isExported_1418_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 3);
v_importAll_1419_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 4);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___y_1405_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1429_ = lean_ctor_get(v___y_1405_, 2);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v___y_1405_, 1);
lean_dec(v_unused_1430_);
v___x_1421_ = v___y_1405_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_imports_1415_);
lean_dec(v___y_1405_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = 0;
v___x_1424_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 2, v___x_1424_);
lean_ctor_set(v___x_1421_, 1, v_pos_1391_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_imports_1415_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_pos_1391_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v___x_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*3 + 1, v_isModule_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*3 + 2, v_isMeta_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*3 + 3, v_isExported_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*3 + 4, v_importAll_1419_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*3, v___x_1423_);
return v___x_1426_;
}
}
}
}
}
v___jp_1431_:
{
lean_object* v_error_x3f_1433_; 
v_error_x3f_1433_ = lean_ctor_get(v___y_1432_, 2);
if (lean_obj_tag(v_error_x3f_1433_) == 1)
{
lean_object* v_imports_1434_; uint8_t v_badModifier_1435_; uint8_t v_isModule_1436_; uint8_t v_isMeta_1437_; uint8_t v_isExported_1438_; uint8_t v_importAll_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_inc_ref(v_error_x3f_1433_);
lean_dec_ref(v_input_1389_);
v_imports_1434_ = lean_ctor_get(v___y_1432_, 0);
v_badModifier_1435_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3);
v_isModule_1436_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 1);
v_isMeta_1437_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 2);
v_isExported_1438_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 3);
v_importAll_1439_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 4);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___y_1432_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; 
v_unused_1447_ = lean_ctor_get(v___y_1432_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v___y_1432_, 1);
lean_dec(v_unused_1448_);
v___x_1441_ = v___y_1432_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_imports_1434_);
lean_dec(v___y_1432_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
lean_inc(v_pos_1391_);
lean_inc_ref(v_imports_1434_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v_pos_1391_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_imports_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_pos_1391_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_error_x3f_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3, v_badModifier_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3 + 1, v_isModule_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3 + 2, v_isMeta_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3 + 3, v_isExported_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3 + 4, v_importAll_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_inc(v_pos_1391_);
v___y_1393_ = v___x_1444_;
v_imports_1394_ = v_imports_1434_;
v_pos_1395_ = v_pos_1391_;
v_isModule_1396_ = v_isModule_1436_;
v_isMeta_1397_ = v_isMeta_1437_;
v_isExported_1398_ = v_isExported_1438_;
v_importAll_1399_ = v_importAll_1439_;
goto v___jp_1392_;
}
}
}
else
{
if (lean_obj_tag(v_error_x3f_1433_) == 1)
{
lean_object* v_imports_1449_; lean_object* v_pos_1450_; uint8_t v_isModule_1451_; uint8_t v_isMeta_1452_; uint8_t v_isExported_1453_; uint8_t v_importAll_1454_; 
lean_dec_ref(v_input_1389_);
v_imports_1449_ = lean_ctor_get(v___y_1432_, 0);
lean_inc_ref(v_imports_1449_);
v_pos_1450_ = lean_ctor_get(v___y_1432_, 1);
lean_inc(v_pos_1450_);
v_isModule_1451_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 1);
v_isMeta_1452_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 2);
v_isExported_1453_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 3);
v_importAll_1454_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 4);
v___y_1393_ = v___y_1432_;
v_imports_1394_ = v_imports_1449_;
v_pos_1395_ = v_pos_1450_;
v_isModule_1396_ = v_isModule_1451_;
v_isMeta_1397_ = v_isMeta_1452_;
v_isExported_1398_ = v_isExported_1453_;
v_importAll_1399_ = v_importAll_1454_;
goto v___jp_1392_;
}
else
{
lean_object* v_pos_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_error_x3f_1459_; 
v_pos_1455_ = lean_ctor_get(v___y_1432_, 1);
lean_inc(v_pos_1455_);
v___x_1456_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1456_, v_input_1389_, v___y_1432_, v___x_1457_, v_pos_1455_);
v_error_x3f_1459_ = lean_ctor_get(v___x_1458_, 2);
lean_inc(v_error_x3f_1459_);
if (lean_obj_tag(v_error_x3f_1459_) == 1)
{
lean_dec_ref_known(v_error_x3f_1459_, 1);
v___y_1405_ = v___x_1458_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_error_x3f_1459_);
lean_inc_ref(v_input_1389_);
v___x_1460_ = l_Lean_ParseImports_moduleIdent(v_input_1389_, v___x_1458_);
v___y_1405_ = v___x_1460_;
goto v___jp_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1472_, lean_object* v_input_1473_, lean_object* v_s_1474_, lean_object* v_i_1475_, lean_object* v_j_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_string_utf8_at_end(v_k_1472_, v_i_1475_);
if (v___x_1477_ == 0)
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_string_utf8_at_end(v_input_1473_, v_j_1476_);
if (v___x_1478_ == 0)
{
uint32_t v_curr_u2081_1479_; uint32_t v_curr_u2082_1480_; uint8_t v___x_1481_; 
v_curr_u2081_1479_ = lean_string_utf8_get_fast(v_k_1472_, v_i_1475_);
v_curr_u2082_1480_ = lean_string_utf8_get_fast(v_input_1473_, v_j_1476_);
v___x_1481_ = lean_uint32_dec_eq(v_curr_u2081_1479_, v_curr_u2082_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec(v_j_1476_);
lean_dec(v_i_1475_);
v___x_1482_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1477_, v_s_1474_);
return v___x_1482_;
}
else
{
if (v___x_1478_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_string_utf8_next_fast(v_k_1472_, v_i_1475_);
lean_dec(v_i_1475_);
v___x_1484_ = lean_string_utf8_next_fast(v_input_1473_, v_j_1476_);
lean_dec(v_j_1476_);
v_i_1475_ = v___x_1483_;
v_j_1476_ = v___x_1484_;
goto _start;
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_j_1476_);
lean_dec(v_i_1475_);
v___x_1486_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1477_, v_s_1474_);
return v___x_1486_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec(v_j_1476_);
lean_dec(v_i_1475_);
v___x_1487_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1477_, v_s_1474_);
return v___x_1487_;
}
}
else
{
lean_object* v_imports_1488_; uint8_t v_badModifier_1489_; lean_object* v_error_x3f_1490_; uint8_t v_isModule_1491_; uint8_t v_isMeta_1492_; uint8_t v_isExported_1493_; uint8_t v_importAll_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_i_1475_);
v_imports_1488_ = lean_ctor_get(v_s_1474_, 0);
v_badModifier_1489_ = lean_ctor_get_uint8(v_s_1474_, sizeof(void*)*3);
v_error_x3f_1490_ = lean_ctor_get(v_s_1474_, 2);
v_isModule_1491_ = lean_ctor_get_uint8(v_s_1474_, sizeof(void*)*3 + 1);
v_isMeta_1492_ = lean_ctor_get_uint8(v_s_1474_, sizeof(void*)*3 + 2);
v_isExported_1493_ = lean_ctor_get_uint8(v_s_1474_, sizeof(void*)*3 + 3);
v_importAll_1494_ = lean_ctor_get_uint8(v_s_1474_, sizeof(void*)*3 + 4);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_s_1474_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_s_1474_, 1);
lean_dec(v_unused_1504_);
v___x_1496_ = v_s_1474_;
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_error_x3f_1490_);
lean_inc(v_imports_1488_);
lean_dec(v_s_1474_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_j_1476_);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_imports_1488_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_j_1476_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_error_x3f_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*3, v_badModifier_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*3 + 1, v_isModule_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*3 + 2, v_isMeta_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*3 + 3, v_isExported_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*3 + 4, v_importAll_1494_);
v___x_1499_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = l_Lean_ParseImports_whitespace(v_input_1473_, v___x_1499_);
v___x_1501_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1477_, v___x_1500_);
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1505_, lean_object* v_input_1506_, lean_object* v_s_1507_, lean_object* v_i_1508_, lean_object* v_j_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1505_, v_input_1506_, v_s_1507_, v_i_1508_, v_j_1509_);
lean_dec_ref(v_input_1506_);
lean_dec_ref(v_k_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_pos_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_s_1518_; lean_object* v_error_x3f_1519_; 
v_pos_1515_ = lean_ctor_get(v_a_1514_, 1);
lean_inc(v_pos_1515_);
v___x_1516_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1517_ = lean_unsigned_to_nat(0u);
v_s_1518_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1516_, v_a_1513_, v_a_1514_, v___x_1517_, v_pos_1515_);
v_error_x3f_1519_ = lean_ctor_get(v_s_1518_, 2);
lean_inc(v_error_x3f_1519_);
if (lean_obj_tag(v_error_x3f_1519_) == 1)
{
lean_dec_ref_known(v_error_x3f_1519_, 1);
lean_dec_ref(v_a_1513_);
return v_s_1518_;
}
else
{
lean_object* v_pos_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_error_x3f_1523_; 
lean_dec(v_error_x3f_1519_);
v_pos_1520_ = lean_ctor_get(v_s_1518_, 1);
lean_inc(v_pos_1520_);
v___x_1521_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1522_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1521_, v_a_1513_, v_s_1518_, v___x_1517_, v_pos_1520_);
v_error_x3f_1523_ = lean_ctor_get(v___x_1522_, 2);
lean_inc(v_error_x3f_1523_);
if (lean_obj_tag(v_error_x3f_1523_) == 1)
{
lean_dec_ref_known(v_error_x3f_1523_, 1);
lean_dec_ref(v_a_1513_);
return v___x_1522_;
}
else
{
lean_object* v___x_1524_; 
lean_dec(v_error_x3f_1523_);
v___x_1524_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1513_, v___x_1522_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* v_input_1527_, lean_object* v_fileName_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_s_1532_; lean_object* v_error_x3f_1533_; 
v___x_1530_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1531_ = l_Lean_ParseImports_whitespace(v_input_1527_, v___x_1530_);
lean_inc_ref(v_input_1527_);
v_s_1532_ = l_Lean_ParseImports_main(v_input_1527_, v___x_1531_);
v_error_x3f_1533_ = lean_ctor_get(v_s_1532_, 2);
lean_inc(v_error_x3f_1533_);
if (lean_obj_tag(v_error_x3f_1533_) == 1)
{
lean_object* v_pos_1534_; lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1557_; 
v_pos_1534_ = lean_ctor_get(v_s_1532_, 1);
lean_inc(v_pos_1534_);
lean_dec_ref(v_s_1532_);
v_val_1535_ = lean_ctor_get(v_error_x3f_1533_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_error_x3f_1533_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1537_ = v_error_x3f_1533_;
v_isShared_1538_ = v_isSharedCheck_1557_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_dec(v_error_x3f_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1557_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_fileMap_1539_; lean_object* v_pos_1540_; lean_object* v_line_1541_; lean_object* v_column_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v_fileMap_1539_ = l_String_toFileMap(v_input_1527_);
v_pos_1540_ = l_Lean_FileMap_toPosition(v_fileMap_1539_, v_pos_1534_);
lean_dec(v_pos_1534_);
v_line_1541_ = lean_ctor_get(v_pos_1540_, 0);
lean_inc(v_line_1541_);
v_column_1542_ = lean_ctor_get(v_pos_1540_, 1);
lean_inc(v_column_1542_);
lean_dec_ref(v_pos_1540_);
v___x_1543_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1544_ = lean_string_append(v_fileName_1528_, v___x_1543_);
v___x_1545_ = l_Nat_reprFast(v_line_1541_);
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = lean_string_append(v___x_1546_, v___x_1543_);
v___x_1548_ = l_Nat_reprFast(v_column_1542_);
v___x_1549_ = lean_string_append(v___x_1547_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1551_ = lean_string_append(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_string_append(v___x_1551_, v_val_1535_);
lean_dec(v_val_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 18);
lean_ctor_set(v___x_1537_, 0, v___x_1552_);
v___x_1554_ = v___x_1537_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
}
else
{
lean_object* v_imports_1558_; uint8_t v_isModule_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_error_x3f_1533_);
lean_dec_ref(v_fileName_1528_);
lean_dec_ref(v_input_1527_);
v_imports_1558_ = lean_ctor_get(v_s_1532_, 0);
lean_inc_ref(v_imports_1558_);
v_isModule_1559_ = lean_ctor_get_uint8(v_s_1532_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1532_);
v___x_1560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1560_, 0, v_imports_1558_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*1, v_isModule_1559_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1562_, lean_object* v_fileName_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_parseImports_x27(v_input_1562_, v_fileName_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1566_, lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v_k_1566_);
v___x_1568_ = lean_box(0);
return v___x_1568_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_val_1569_ = lean_ctor_get(v_x_1567_, 0);
lean_inc(v_val_1569_);
lean_dec_ref_known(v_x_1567_, 1);
v___x_1570_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_k_1566_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
if (lean_obj_tag(v_a_1574_) == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_array_to_list(v_a_1575_);
return v___x_1576_;
}
else
{
lean_object* v_head_1577_; lean_object* v_tail_1578_; lean_object* v___x_1579_; 
v_head_1577_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_head_1577_);
v_tail_1578_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_tail_1578_);
lean_dec_ref_known(v_a_1574_, 2);
v___x_1579_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1575_, v_head_1577_);
v_a_1574_ = v_tail_1578_;
v_a_1575_ = v___x_1579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_bs_1583_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1584_ == 0)
{
return v_bs_1583_;
}
else
{
lean_object* v_v_1585_; lean_object* v___x_1586_; lean_object* v_bs_x27_1587_; lean_object* v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v_v_1585_ = lean_array_uget(v_bs_1583_, v_i_1582_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_bs_x27_1587_ = lean_array_uset(v_bs_1583_, v_i_1582_, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_v_1585_);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1582_, v___x_1589_);
v___x_1591_ = lean_array_uset(v_bs_x27_1587_, v_i_1582_, v___x_1588_);
v_i_1582_ = v___x_1590_;
v_bs_1583_ = v___x_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1593_, lean_object* v_i_1594_, lean_object* v_bs_1595_){
_start:
{
size_t v_sz_boxed_1596_; size_t v_i_boxed_1597_; lean_object* v_res_1598_; 
v_sz_boxed_1596_ = lean_unbox_usize(v_sz_1593_);
lean_dec(v_sz_1593_);
v_i_boxed_1597_ = lean_unbox_usize(v_i_1594_);
lean_dec(v_i_1594_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1596_, v_i_boxed_1597_, v_bs_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1599_){
_start:
{
size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_sz_1600_ = lean_array_size(v_a_1599_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1600_, v___x_1601_, v_a_1599_);
v___x_1603_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1608_){
_start:
{
lean_object* v_result_x3f_1609_; lean_object* v_errors_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1628_; 
v_result_x3f_1609_ = lean_ctor_get(v_x_1608_, 0);
v_errors_1610_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1612_ = v_x_1608_;
v_isShared_1613_ = v_isSharedCheck_1628_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_errors_1610_);
lean_inc(v_result_x3f_1609_);
lean_dec(v_x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1628_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1615_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1614_, v_result_x3f_1609_);
v___x_1616_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1617_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1610_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___x_1617_);
lean_ctor_set(v___x_1612_, 0, v___x_1616_);
v___x_1619_ = v___x_1612_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v___x_1620_);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1615_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1625_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1623_, v___x_1624_);
v___x_1626_ = l_Lean_Json_mkObj(v___x_1625_);
lean_dec(v___x_1625_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_bs_1633_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1634_ == 0)
{
return v_bs_1633_;
}
else
{
lean_object* v_v_1635_; lean_object* v___x_1636_; lean_object* v_bs_x27_1637_; lean_object* v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v_v_1635_ = lean_array_uget(v_bs_1633_, v_i_1632_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v_bs_x27_1637_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1636_);
v___x_1638_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1635_);
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_add(v_i_1632_, v___x_1639_);
v___x_1641_ = lean_array_uset(v_bs_x27_1637_, v_i_1632_, v___x_1638_);
v_i_1632_ = v___x_1640_;
v_bs_1633_ = v___x_1641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1643_, lean_object* v_i_1644_, lean_object* v_bs_1645_){
_start:
{
size_t v_sz_boxed_1646_; size_t v_i_boxed_1647_; lean_object* v_res_1648_; 
v_sz_boxed_1646_ = lean_unbox_usize(v_sz_1643_);
lean_dec(v_sz_1643_);
v_i_boxed_1647_ = lean_unbox_usize(v_i_1644_);
lean_dec(v_i_1644_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_1646_, v_i_boxed_1647_, v_bs_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* v_a_1649_){
_start:
{
size_t v_sz_1650_; size_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_sz_1650_ = lean_array_size(v_a_1649_);
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1650_, v___x_1651_, v_a_1649_);
v___x_1653_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* v_x_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1656_ = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
v___x_1657_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_1655_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1659_);
v___x_1662_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1663_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1661_, v___x_1662_);
v___x_1664_ = l_Lean_Json_mkObj(v___x_1663_);
lean_dec(v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1669_, size_t v_i_1670_, lean_object* v_bs_1671_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_bs_1671_);
return v___x_1674_;
}
else
{
lean_object* v_v_1675_; lean_object* v___x_1676_; lean_object* v_bs_x27_1677_; lean_object* v_a_1679_; lean_object* v_a_1685_; lean_object* v___x_1692_; 
v_v_1675_ = lean_array_uget(v_bs_1671_, v_i_1670_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v_bs_x27_1677_ = lean_array_uset(v_bs_1671_, v_i_1670_, v___x_1676_);
v___x_1692_ = l_IO_FS_readFile(v_v_1675_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = l_Lean_parseImports_x27(v_a_1693_, v_v_1675_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1704_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1704_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1704_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 1);
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v_a_1679_ = v___x_1702_;
goto v___jp_1678_;
}
}
}
else
{
lean_object* v_a_1705_; 
v_a_1705_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1694_, 1);
v_a_1685_ = v_a_1705_;
goto v___jp_1684_;
}
}
else
{
lean_object* v_a_1706_; 
lean_dec(v_v_1675_);
v_a_1706_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1692_, 1);
v_a_1685_ = v_a_1706_;
goto v___jp_1684_;
}
v___jp_1678_:
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1670_, v___x_1680_);
v___x_1682_ = lean_array_uset(v_bs_x27_1677_, v_i_1670_, v_a_1679_);
v_i_1670_ = v___x_1681_;
v_bs_1671_ = v___x_1682_;
goto _start;
}
v___jp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_io_error_to_string(v_a_1685_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
v___x_1690_ = lean_array_push(v___x_1689_, v___x_1687_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1686_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v_a_1679_ = v___x_1691_;
goto v___jp_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1707_, lean_object* v_i_1708_, lean_object* v_bs_1709_, lean_object* v___y_1710_){
_start:
{
size_t v_sz_boxed_1711_; size_t v_i_boxed_1712_; lean_object* v_res_1713_; 
v_sz_boxed_1711_ = lean_unbox_usize(v_sz_1707_);
lean_dec(v_sz_1707_);
v_i_boxed_1712_ = lean_unbox_usize(v_i_1708_);
lean_dec(v_i_1708_);
v_res_1713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1711_, v_i_boxed_1712_, v_bs_1709_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_putStr_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_get_stdout();
v_putStr_1717_ = lean_ctor_get(v___x_1716_, 4);
lean_inc_ref(v_putStr_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lean_apply_2(v_putStr_1717_, v_s_1714_, lean_box(0));
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1722_){
_start:
{
uint32_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = 10;
v___x_1725_ = lean_string_push(v_s_1722_, v___x_1724_);
v___x_1726_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1730_){
_start:
{
size_t v_sz_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v_sz_1732_ = lean_array_size(v_fileNames_1730_);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1732_, v___x_1733_, v_fileNames_1730_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1735_);
v___x_1737_ = l_Lean_Json_compress(v___x_1736_);
v___x_1738_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1734_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1734_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_printImportsJson(v_fileNames_1747_);
return v_res_1749_;
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
