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
uint32_t v_curr_383_; uint32_t v___x_384_; uint8_t v___x_385_; 
v_curr_383_ = lean_string_utf8_get_fast(v_input_368_, v_pos_371_);
v___x_384_ = 9;
v___x_385_ = lean_uint32_dec_eq(v_curr_383_, v___x_384_);
if (v___x_385_ == 0)
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 32;
v___x_387_ = lean_uint32_dec_eq(v_curr_383_, v___x_386_);
if (v___x_387_ == 0)
{
if (v___x_385_ == 0)
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 13;
v___x_389_ = lean_uint32_dec_eq(v_curr_383_, v___x_388_);
if (v___x_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 10;
v___x_391_ = lean_uint32_dec_eq(v_curr_383_, v___x_390_);
if (v___x_391_ == 0)
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 45;
v___x_393_ = lean_uint32_dec_eq(v_curr_383_, v___x_392_);
if (v___x_393_ == 0)
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 47;
v___x_395_ = lean_uint32_dec_eq(v_curr_383_, v___x_394_);
if (v___x_395_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v_i_396_; uint32_t v_curr_397_; uint8_t v___x_398_; 
v_i_396_ = lean_string_utf8_next_fast(v_input_368_, v_pos_371_);
v_curr_397_ = lean_string_utf8_get(v_input_368_, v_i_396_);
v___x_398_ = lean_uint32_dec_eq(v_curr_397_, v___x_392_);
if (v___x_398_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v_i_399_; uint32_t v_curr_400_; uint8_t v___x_401_; 
v_i_399_ = lean_string_utf8_next(v_input_368_, v_i_396_);
v_curr_400_ = lean_string_utf8_get(v_input_368_, v_i_399_);
v___x_401_ = lean_uint32_dec_eq(v_curr_400_, v___x_392_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 33;
v___x_403_ = lean_uint32_dec_eq(v_curr_400_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_415_; 
lean_inc(v_error_x3f_373_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; lean_object* v_unused_418_; 
v_unused_416_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_418_);
v___x_405_ = v_s_369_;
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
else
{
lean_dec(v_s_369_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_string_utf8_next(v_input_368_, v_i_399_);
lean_dec(v_i_399_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_error_x3f_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_414_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_414_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_414_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_414_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_414_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v_s_411_; lean_object* v_error_x3f_412_; 
v_s_411_ = l_Lean_ParseImports_finishCommentBlock(v___x_407_, v_input_368_, v___x_410_);
v_error_x3f_412_ = lean_ctor_get(v_s_411_, 2);
lean_inc(v_error_x3f_412_);
if (lean_obj_tag(v_error_x3f_412_) == 1)
{
lean_dec_ref_known(v_error_x3f_412_, 1);
return v_s_411_;
}
else
{
lean_dec(v_error_x3f_412_);
v_s_369_ = v_s_411_;
goto _start;
}
}
}
}
else
{
lean_dec(v_i_399_);
return v_s_369_;
}
}
else
{
lean_dec(v_i_399_);
return v_s_369_;
}
}
}
}
else
{
lean_object* v_i_419_; uint32_t v_curr_420_; uint8_t v___x_421_; 
v_i_419_ = lean_string_utf8_next_fast(v_input_368_, v_pos_371_);
v_curr_420_ = lean_string_utf8_get(v_input_368_, v_i_419_);
v___x_421_ = lean_uint32_dec_eq(v_curr_420_, v___x_392_);
if (v___x_421_ == 0)
{
return v_s_369_;
}
else
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
lean_inc(v_error_x3f_373_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_433_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_435_);
v___x_423_ = v_s_369_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_s_369_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_string_utf8_next(v_input_368_, v_i_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_error_x3f_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v_s_428_; lean_object* v_error_x3f_429_; 
v_s_428_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(v_input_368_, v___x_427_);
v_error_x3f_429_ = lean_ctor_get(v_s_428_, 2);
lean_inc(v_error_x3f_429_);
if (lean_obj_tag(v_error_x3f_429_) == 1)
{
lean_dec_ref_known(v_error_x3f_429_, 1);
return v_s_428_;
}
else
{
lean_dec(v_error_x3f_429_);
v_s_369_ = v_s_428_;
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
else
{
lean_inc(v_error_x3f_373_);
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
lean_dec_ref(v_s_369_);
goto v___jp_378_;
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
else
{
lean_inc(v_error_x3f_373_);
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
lean_dec_ref(v_s_369_);
goto v___jp_378_;
}
}
else
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
lean_inc(v_pos_371_);
lean_inc_ref(v_imports_370_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_s_369_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_444_ = lean_ctor_get(v_s_369_, 2);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_s_369_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_s_369_, 0);
lean_dec(v_unused_446_);
v___x_437_ = v_s_369_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_s_369_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = ((lean_object*)(l_Lean_ParseImports_whitespace___closed__1));
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 2, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_imports_370_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_pos_371_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v___x_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3, v_badModifier_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3 + 1, v_isModule_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3 + 2, v_isMeta_375_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3 + 3, v_isExported_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3 + 4, v_importAll_377_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* v_input_447_, lean_object* v_s_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_ParseImports_whitespace(v_input_447_, v_s_448_);
lean_dec_ref(v_input_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object* v_k_450_, lean_object* v_failure_451_, lean_object* v_success_452_, lean_object* v_input_453_, lean_object* v_s_454_, lean_object* v_i_455_, lean_object* v_j_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = lean_string_utf8_at_end(v_k_450_, v_i_455_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = lean_string_utf8_at_end(v_input_453_, v_j_456_);
if (v___x_458_ == 0)
{
uint32_t v_curr_u2081_459_; uint32_t v_curr_u2082_460_; uint8_t v___x_461_; 
v_curr_u2081_459_ = lean_string_utf8_get_fast(v_k_450_, v_i_455_);
v_curr_u2082_460_ = lean_string_utf8_get_fast(v_input_453_, v_j_456_);
v___x_461_ = lean_uint32_dec_eq(v_curr_u2081_459_, v_curr_u2082_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_j_456_);
lean_dec(v_i_455_);
lean_dec_ref(v_success_452_);
v___x_462_ = lean_apply_2(v_failure_451_, v_input_453_, v_s_454_);
return v___x_462_;
}
else
{
if (v___x_458_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_string_utf8_next_fast(v_k_450_, v_i_455_);
lean_dec(v_i_455_);
v___x_464_ = lean_string_utf8_next_fast(v_input_453_, v_j_456_);
lean_dec(v_j_456_);
v_i_455_ = v___x_463_;
v_j_456_ = v___x_464_;
goto _start;
}
else
{
lean_object* v___x_466_; 
lean_dec(v_j_456_);
lean_dec(v_i_455_);
lean_dec_ref(v_success_452_);
v___x_466_ = lean_apply_2(v_failure_451_, v_input_453_, v_s_454_);
return v___x_466_;
}
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v_j_456_);
lean_dec(v_i_455_);
lean_dec_ref(v_success_452_);
v___x_467_ = lean_apply_2(v_failure_451_, v_input_453_, v_s_454_);
return v___x_467_;
}
}
else
{
lean_object* v_imports_468_; uint8_t v_badModifier_469_; lean_object* v_error_x3f_470_; uint8_t v_isModule_471_; uint8_t v_isMeta_472_; uint8_t v_isExported_473_; uint8_t v_importAll_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_i_455_);
lean_dec_ref(v_failure_451_);
v_imports_468_ = lean_ctor_get(v_s_454_, 0);
v_badModifier_469_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3);
v_error_x3f_470_ = lean_ctor_get(v_s_454_, 2);
v_isModule_471_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 1);
v_isMeta_472_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 2);
v_isExported_473_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 3);
v_importAll_474_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 4);
v_isSharedCheck_483_ = !lean_is_exclusive(v_s_454_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_s_454_, 1);
lean_dec(v_unused_484_);
v___x_476_ = v_s_454_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_error_x3f_470_);
lean_inc(v_imports_468_);
lean_dec(v_s_454_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_j_456_);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_imports_468_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_j_456_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_error_x3f_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3, v_badModifier_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 1, v_isModule_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 2, v_isMeta_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 3, v_isExported_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 4, v_importAll_474_);
v___x_479_ = v_reuseFailAlloc_482_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l_Lean_ParseImports_whitespace(v_input_453_, v___x_479_);
v___x_481_ = lean_apply_2(v_success_452_, v_input_453_, v___x_480_);
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* v_k_485_, lean_object* v_failure_486_, lean_object* v_success_487_, lean_object* v_input_488_, lean_object* v_s_489_, lean_object* v_i_490_, lean_object* v_j_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_485_, v_failure_486_, v_success_487_, v_input_488_, v_s_489_, v_i_490_, v_j_491_);
lean_dec_ref(v_k_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* v_k_493_, lean_object* v_failure_494_, lean_object* v_success_495_, lean_object* v_input_496_, lean_object* v_s_497_){
_start:
{
lean_object* v_pos_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_pos_498_ = lean_ctor_get(v_s_497_, 1);
lean_inc(v_pos_498_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_493_, v_failure_494_, v_success_495_, v_input_496_, v_s_497_, v___x_499_, v_pos_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* v_k_501_, lean_object* v_failure_502_, lean_object* v_success_503_, lean_object* v_input_504_, lean_object* v_s_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_ParseImports_keywordCore(v_k_501_, v_failure_502_, v_success_503_, v_input_504_, v_s_505_);
lean_dec_ref(v_k_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* v_k_509_, lean_object* v_x_510_, lean_object* v_s_511_){
_start:
{
lean_object* v_imports_512_; lean_object* v_pos_513_; uint8_t v_badModifier_514_; uint8_t v_isModule_515_; uint8_t v_isMeta_516_; uint8_t v_isExported_517_; uint8_t v_importAll_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_imports_512_ = lean_ctor_get(v_s_511_, 0);
v_pos_513_ = lean_ctor_get(v_s_511_, 1);
v_badModifier_514_ = lean_ctor_get_uint8(v_s_511_, sizeof(void*)*3);
v_isModule_515_ = lean_ctor_get_uint8(v_s_511_, sizeof(void*)*3 + 1);
v_isMeta_516_ = lean_ctor_get_uint8(v_s_511_, sizeof(void*)*3 + 2);
v_isExported_517_ = lean_ctor_get_uint8(v_s_511_, sizeof(void*)*3 + 3);
v_importAll_518_ = lean_ctor_get_uint8(v_s_511_, sizeof(void*)*3 + 4);
v_isSharedCheck_530_ = !lean_is_exclusive(v_s_511_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_s_511_, 2);
lean_dec(v_unused_531_);
v___x_520_ = v_s_511_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_pos_513_);
lean_inc(v_imports_512_);
lean_dec(v_s_511_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_522_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
v___x_523_ = lean_string_append(v___x_522_, v_k_509_);
v___x_524_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
v___x_525_ = lean_string_append(v___x_523_, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 2, v___x_526_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_imports_512_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_pos_513_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v___x_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3, v_badModifier_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 1, v_isModule_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 2, v_isMeta_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 3, v_isExported_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 4, v_importAll_518_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* v_k_532_, lean_object* v_x_533_, lean_object* v_s_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_ParseImports_keyword___lam__0(v_k_532_, v_x_533_, v_s_534_);
lean_dec_ref(v_x_533_);
lean_dec_ref(v_k_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* v_k_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_pos_539_; lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_pos_539_ = lean_ctor_get(v_a_538_, 1);
lean_inc(v_pos_539_);
lean_inc_ref(v_k_536_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(v___f_540_, 0, v_k_536_);
v___x_541_ = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_536_, v___f_540_, v___x_541_, v_a_537_, v_a_538_, v___x_542_, v_pos_539_);
lean_dec_ref(v_k_536_);
return v___x_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* v_input_544_, lean_object* v_s_545_){
_start:
{
lean_object* v_pos_546_; uint32_t v_curr_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v_pos_546_ = lean_ctor_get(v_s_545_, 1);
v_curr_547_ = lean_string_utf8_get(v_input_544_, v_pos_546_);
v___x_548_ = 46;
v___x_549_ = lean_uint32_dec_eq(v_curr_547_, v___x_548_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
lean_object* v_i_550_; uint8_t v___x_551_; 
v_i_550_ = lean_string_utf8_next(v_input_544_, v_pos_546_);
v___x_551_ = lean_string_utf8_at_end(v_input_544_, v_i_550_);
if (v___x_551_ == 0)
{
uint32_t v_curr_552_; uint8_t v___y_560_; uint32_t v___x_565_; uint8_t v___x_566_; 
v_curr_552_ = lean_string_utf8_get_fast(v_input_544_, v_i_550_);
lean_dec(v_i_550_);
v___x_565_ = 65;
v___x_566_ = lean_uint32_dec_le(v___x_565_, v_curr_552_);
if (v___x_566_ == 0)
{
v___y_560_ = v___x_566_;
goto v___jp_559_;
}
else
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 90;
v___x_568_ = lean_uint32_dec_le(v_curr_552_, v___x_567_);
v___y_560_ = v___x_568_;
goto v___jp_559_;
}
v___jp_553_:
{
uint32_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 95;
v___x_555_ = lean_uint32_dec_eq(v_curr_552_, v___x_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_isLetterLike(v_curr_552_);
if (v___x_556_ == 0)
{
uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 171;
v___x_558_ = lean_uint32_dec_eq(v_curr_552_, v___x_557_);
return v___x_558_;
}
else
{
return v___x_549_;
}
}
else
{
return v___x_549_;
}
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 97;
v___x_562_ = lean_uint32_dec_le(v___x_561_, v_curr_552_);
if (v___x_562_ == 0)
{
goto v___jp_553_;
}
else
{
uint32_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 122;
v___x_564_ = lean_uint32_dec_le(v_curr_552_, v___x_563_);
if (v___x_564_ == 0)
{
goto v___jp_553_;
}
else
{
return v___x_549_;
}
}
}
else
{
return v___x_549_;
}
}
}
else
{
uint8_t v___x_569_; 
lean_dec(v_i_550_);
v___x_569_ = 0;
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_570_, lean_object* v_s_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_ParseImports_isIdCont(v_input_570_, v_s_571_);
lean_dec_ref(v_s_571_);
lean_dec_ref(v_input_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_574_, lean_object* v_s_575_){
_start:
{
lean_object* v_imports_576_; lean_object* v_pos_577_; uint8_t v_badModifier_578_; lean_object* v_error_x3f_579_; uint8_t v_isModule_580_; uint8_t v_isMeta_581_; uint8_t v_isExported_582_; uint8_t v_importAll_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_imports_576_ = lean_ctor_get(v_s_575_, 0);
v_pos_577_ = lean_ctor_get(v_s_575_, 1);
v_badModifier_578_ = lean_ctor_get_uint8(v_s_575_, sizeof(void*)*3);
v_error_x3f_579_ = lean_ctor_get(v_s_575_, 2);
v_isModule_580_ = lean_ctor_get_uint8(v_s_575_, sizeof(void*)*3 + 1);
v_isMeta_581_ = lean_ctor_get_uint8(v_s_575_, sizeof(void*)*3 + 2);
v_isExported_582_ = lean_ctor_get_uint8(v_s_575_, sizeof(void*)*3 + 3);
v_importAll_583_ = lean_ctor_get_uint8(v_s_575_, sizeof(void*)*3 + 4);
v_isSharedCheck_591_ = !lean_is_exclusive(v_s_575_);
if (v_isSharedCheck_591_ == 0)
{
v___x_585_ = v_s_575_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_error_x3f_579_);
lean_inc(v_pos_577_);
lean_inc(v_imports_576_);
lean_dec(v_s_575_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_array_push(v_imports_576_, v_i_574_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_pos_577_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_error_x3f_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*3, v_badModifier_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*3 + 1, v_isModule_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*3 + 2, v_isMeta_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*3 + 3, v_isExported_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*3 + 4, v_importAll_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_592_){
_start:
{
uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 95;
v___x_594_ = lean_uint32_dec_eq(v_c_592_, v___x_593_);
if (v___x_594_ == 0)
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 39;
v___x_596_ = lean_uint32_dec_eq(v_c_592_, v___x_595_);
if (v___x_596_ == 0)
{
uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 33;
v___x_598_ = lean_uint32_dec_eq(v_c_592_, v___x_597_);
if (v___x_598_ == 0)
{
uint32_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 63;
v___x_600_ = lean_uint32_dec_eq(v_c_592_, v___x_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_isLetterLike(v_c_592_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_isSubScriptAlnum(v_c_592_);
return v___x_602_;
}
else
{
return v___x_601_;
}
}
else
{
return v___x_600_;
}
}
else
{
return v___x_598_;
}
}
else
{
return v___x_596_;
}
}
else
{
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_603_){
_start:
{
uint32_t v_c_boxed_604_; uint8_t v_res_605_; lean_object* v_r_606_; 
v_c_boxed_604_ = lean_unbox_uint32(v_c_603_);
lean_dec(v_c_603_);
v_res_605_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_607_){
_start:
{
uint8_t v___y_632_; uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 65;
v___x_638_ = lean_uint32_dec_le(v___x_637_, v_c_607_);
if (v___x_638_ == 0)
{
v___y_632_ = v___x_638_;
goto v___jp_631_;
}
else
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 90;
v___x_640_ = lean_uint32_dec_le(v_c_607_, v___x_639_);
v___y_632_ = v___x_640_;
goto v___jp_631_;
}
v___jp_608_:
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 46;
v___x_610_ = lean_uint32_dec_eq(v_c_607_, v___x_609_);
if (v___x_610_ == 0)
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 10;
v___x_612_ = lean_uint32_dec_eq(v_c_607_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 32;
v___x_614_ = lean_uint32_dec_eq(v_c_607_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 95;
v___x_616_ = lean_uint32_dec_eq(v_c_607_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 39;
v___x_618_ = lean_uint32_dec_eq(v_c_607_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 33;
v___x_620_ = lean_uint32_dec_eq(v_c_607_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 63;
v___x_622_ = lean_uint32_dec_eq(v_c_607_, v___x_621_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_isLetterLike(v_c_607_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
v___x_624_ = l_Lean_isSubScriptAlnum(v_c_607_);
return v___x_624_;
}
else
{
return v___x_623_;
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
return v___x_616_;
}
}
else
{
return v___x_612_;
}
}
else
{
return v___x_610_;
}
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
v___jp_626_:
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 48;
v___x_628_ = lean_uint32_dec_le(v___x_627_, v_c_607_);
if (v___x_628_ == 0)
{
goto v___jp_608_;
}
else
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 57;
v___x_630_ = lean_uint32_dec_le(v_c_607_, v___x_629_);
if (v___x_630_ == 0)
{
goto v___jp_608_;
}
else
{
return v___x_630_;
}
}
}
v___jp_631_:
{
if (v___y_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 97;
v___x_634_ = lean_uint32_dec_le(v___x_633_, v_c_607_);
if (v___x_634_ == 0)
{
goto v___jp_626_;
}
else
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 122;
v___x_636_ = lean_uint32_dec_le(v_c_607_, v___x_635_);
if (v___x_636_ == 0)
{
goto v___jp_626_;
}
else
{
return v___x_636_;
}
}
}
else
{
return v___y_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_641_){
_start:
{
uint32_t v_c_boxed_642_; uint8_t v_res_643_; lean_object* v_r_644_; 
v_c_boxed_642_ = lean_unbox_uint32(v_c_641_);
lean_dec(v_c_641_);
v_res_643_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_642_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_645_, lean_object* v_s_646_){
_start:
{
lean_object* v_imports_647_; lean_object* v_pos_648_; uint8_t v_badModifier_649_; lean_object* v_error_x3f_650_; uint8_t v_isModule_651_; uint8_t v_isMeta_652_; uint8_t v_isExported_653_; uint8_t v_importAll_654_; uint8_t v___x_655_; 
v_imports_647_ = lean_ctor_get(v_s_646_, 0);
v_pos_648_ = lean_ctor_get(v_s_646_, 1);
v_badModifier_649_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*3);
v_error_x3f_650_ = lean_ctor_get(v_s_646_, 2);
v_isModule_651_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*3 + 1);
v_isMeta_652_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*3 + 2);
v_isExported_653_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*3 + 3);
v_importAll_654_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*3 + 4);
v___x_655_ = lean_string_utf8_at_end(v_input_645_, v_pos_648_);
if (v___x_655_ == 0)
{
uint32_t v___x_656_; uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_string_utf8_get_fast(v_input_645_, v_pos_648_);
v___x_657_ = 187;
v___x_658_ = lean_uint32_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_error_x3f_650_);
lean_inc(v_pos_648_);
lean_inc_ref(v_imports_647_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_s_646_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_668_ = lean_ctor_get(v_s_646_, 2);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_s_646_, 1);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_s_646_, 0);
lean_dec(v_unused_670_);
v___x_660_ = v_s_646_;
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_s_646_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_string_utf8_next_fast(v_input_645_, v_pos_648_);
lean_dec(v_pos_648_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_imports_647_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_error_x3f_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3, v_badModifier_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3 + 1, v_isModule_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3 + 2, v_isMeta_652_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3 + 3, v_isExported_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3 + 4, v_importAll_654_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v_s_646_ = v___x_664_;
goto _start;
}
}
}
else
{
return v_s_646_;
}
}
else
{
return v_s_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_671_, lean_object* v_s_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_671_, v_s_672_);
lean_dec_ref(v_input_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_674_, uint32_t v___x_675_, lean_object* v_input_676_, lean_object* v_s_677_){
_start:
{
lean_object* v_imports_678_; lean_object* v_pos_679_; uint8_t v_badModifier_680_; lean_object* v_error_x3f_681_; uint8_t v_isModule_682_; uint8_t v_isMeta_683_; uint8_t v_isExported_684_; uint8_t v_importAll_685_; uint8_t v___y_687_; uint8_t v___x_700_; 
v_imports_678_ = lean_ctor_get(v_s_677_, 0);
v_pos_679_ = lean_ctor_get(v_s_677_, 1);
v_badModifier_680_ = lean_ctor_get_uint8(v_s_677_, sizeof(void*)*3);
v_error_x3f_681_ = lean_ctor_get(v_s_677_, 2);
v_isModule_682_ = lean_ctor_get_uint8(v_s_677_, sizeof(void*)*3 + 1);
v_isMeta_683_ = lean_ctor_get_uint8(v_s_677_, sizeof(void*)*3 + 2);
v_isExported_684_ = lean_ctor_get_uint8(v_s_677_, sizeof(void*)*3 + 3);
v_importAll_685_ = lean_ctor_get_uint8(v_s_677_, sizeof(void*)*3 + 4);
v___x_700_ = lean_string_utf8_at_end(v_input_676_, v_pos_679_);
if (v___x_700_ == 0)
{
uint32_t v___x_701_; uint8_t v___x_702_; uint32_t v___x_703_; uint8_t v___y_727_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_701_ = 171;
v___x_702_ = lean_uint32_dec_eq(v___x_675_, v___x_701_);
v___x_703_ = lean_string_utf8_get_fast(v_input_676_, v_pos_679_);
v___x_732_ = 65;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___x_703_);
if (v___x_733_ == 0)
{
v___y_727_ = v___x_733_;
goto v___jp_726_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 90;
v___x_735_ = lean_uint32_dec_le(v___x_703_, v___x_734_);
v___y_727_ = v___x_735_;
goto v___jp_726_;
}
v___jp_704_:
{
uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 46;
v___x_706_ = lean_uint32_dec_eq(v___x_703_, v___x_705_);
if (v___x_706_ == 0)
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 10;
v___x_708_ = lean_uint32_dec_eq(v___x_703_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 32;
v___x_710_ = lean_uint32_dec_eq(v___x_703_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 95;
v___x_712_ = lean_uint32_dec_eq(v___x_703_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 39;
v___x_714_ = lean_uint32_dec_eq(v___x_703_, v___x_713_);
if (v___x_714_ == 0)
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 33;
v___x_716_ = lean_uint32_dec_eq(v___x_703_, v___x_715_);
if (v___x_716_ == 0)
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 63;
v___x_718_ = lean_uint32_dec_eq(v___x_703_, v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_isLetterLike(v___x_703_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_isSubScriptAlnum(v___x_703_);
if (v___x_720_ == 0)
{
v___y_687_ = v___y_674_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
if (v___x_719_ == 0)
{
v___y_687_ = v___y_674_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___y_674_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___y_674_;
goto v___jp_686_;
}
}
else
{
v___y_687_ = v___y_674_;
goto v___jp_686_;
}
}
v___jp_721_:
{
uint32_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 48;
v___x_723_ = lean_uint32_dec_le(v___x_722_, v___x_703_);
if (v___x_723_ == 0)
{
goto v___jp_704_;
}
else
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 57;
v___x_725_ = lean_uint32_dec_le(v___x_703_, v___x_724_);
if (v___x_725_ == 0)
{
goto v___jp_704_;
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
}
v___jp_726_:
{
if (v___y_727_ == 0)
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 97;
v___x_729_ = lean_uint32_dec_le(v___x_728_, v___x_703_);
if (v___x_729_ == 0)
{
goto v___jp_721_;
}
else
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 122;
v___x_731_ = lean_uint32_dec_le(v___x_703_, v___x_730_);
if (v___x_731_ == 0)
{
goto v___jp_721_;
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
}
else
{
v___y_687_ = v___x_702_;
goto v___jp_686_;
}
}
}
else
{
return v_s_677_;
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_696_; 
lean_inc(v_error_x3f_681_);
lean_inc(v_pos_679_);
lean_inc_ref(v_imports_678_);
v_isSharedCheck_696_ = !lean_is_exclusive(v_s_677_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_697_ = lean_ctor_get(v_s_677_, 2);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_s_677_, 1);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_s_677_, 0);
lean_dec(v_unused_699_);
v___x_689_ = v_s_677_;
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
else
{
lean_dec(v_s_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_string_utf8_next_fast(v_input_676_, v_pos_679_);
lean_dec(v_pos_679_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_imports_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_error_x3f_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3, v_badModifier_680_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 1, v_isModule_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 2, v_isMeta_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 3, v_isExported_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 4, v_importAll_685_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_s_677_ = v___x_693_;
goto _start;
}
}
}
else
{
return v_s_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_736_, lean_object* v___x_737_, lean_object* v_input_738_, lean_object* v_s_739_){
_start:
{
uint8_t v___y_1069__boxed_740_; uint32_t v___x_1070__boxed_741_; lean_object* v_res_742_; 
v___y_1069__boxed_740_ = lean_unbox(v___y_736_);
v___x_1070__boxed_741_ = lean_unbox_uint32(v___x_737_);
lean_dec(v___x_737_);
v_res_742_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_1069__boxed_740_, v___x_1070__boxed_741_, v_input_738_, v_s_739_);
lean_dec_ref(v_input_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_749_, lean_object* v_finalize_750_, lean_object* v_module_751_, lean_object* v_s_752_){
_start:
{
uint8_t v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; lean_object* v_imports_766_; lean_object* v_pos_767_; uint8_t v_badModifier_768_; lean_object* v_error_x3f_769_; uint8_t v_isModule_770_; uint8_t v_isMeta_771_; uint8_t v_isExported_772_; uint8_t v_importAll_773_; uint8_t v___x_774_; 
v_imports_766_ = lean_ctor_get(v_s_752_, 0);
v_pos_767_ = lean_ctor_get(v_s_752_, 1);
v_badModifier_768_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*3);
v_error_x3f_769_ = lean_ctor_get(v_s_752_, 2);
v_isModule_770_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*3 + 1);
v_isMeta_771_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*3 + 2);
v_isExported_772_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*3 + 3);
v_importAll_773_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*3 + 4);
v___x_774_ = lean_string_utf8_at_end(v_input_749_, v_pos_767_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_915_; 
lean_inc(v_error_x3f_769_);
lean_inc(v_pos_767_);
lean_inc_ref(v_imports_766_);
v_isSharedCheck_915_ = !lean_is_exclusive(v_s_752_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_916_ = lean_ctor_get(v_s_752_, 2);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_s_752_, 1);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_s_752_, 0);
lean_dec(v_unused_918_);
v___x_776_ = v_s_752_;
v_isShared_777_ = v_isSharedCheck_915_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_s_752_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_915_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
uint32_t v_curr_778_; uint32_t v___x_779_; lean_object* v___y_781_; uint8_t v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; uint32_t v___y_786_; uint8_t v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; uint8_t v___y_798_; uint8_t v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint32_t v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; uint8_t v___y_809_; uint8_t v___y_815_; uint8_t v___y_850_; uint8_t v___x_855_; 
v_curr_778_ = lean_string_utf8_get_fast(v_input_749_, v_pos_767_);
v___x_779_ = 171;
v___x_855_ = lean_uint32_dec_eq(v_curr_778_, v___x_779_);
if (v___x_855_ == 0)
{
uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_856_ = 65;
v___x_857_ = lean_uint32_dec_le(v___x_856_, v_curr_778_);
if (v___x_857_ == 0)
{
v___y_850_ = v___x_857_;
goto v___jp_849_;
}
else
{
uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_858_ = 90;
v___x_859_ = lean_uint32_dec_le(v_curr_778_, v___x_858_);
v___y_850_ = v___x_859_;
goto v___jp_849_;
}
}
else
{
lean_object* v_startPart_860_; lean_object* v___x_861_; lean_object* v_s_862_; lean_object* v_imports_863_; lean_object* v_pos_864_; uint8_t v_badModifier_865_; lean_object* v_error_x3f_866_; uint8_t v_isModule_867_; uint8_t v_isMeta_868_; uint8_t v_isExported_869_; uint8_t v_importAll_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_776_);
v_startPart_860_ = lean_string_utf8_next_fast(v_input_749_, v_pos_767_);
lean_dec(v_pos_767_);
v___x_861_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_861_, 0, v_imports_766_);
lean_ctor_set(v___x_861_, 1, v_startPart_860_);
lean_ctor_set(v___x_861_, 2, v_error_x3f_769_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3, v_badModifier_768_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 1, v_isModule_770_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 2, v_isMeta_771_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 3, v_isExported_772_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 4, v_importAll_773_);
v_s_862_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_749_, v___x_861_);
v_imports_863_ = lean_ctor_get(v_s_862_, 0);
v_pos_864_ = lean_ctor_get(v_s_862_, 1);
v_badModifier_865_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3);
v_error_x3f_866_ = lean_ctor_get(v_s_862_, 2);
v_isModule_867_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 1);
v_isMeta_868_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 2);
v_isExported_869_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 3);
v_importAll_870_ = lean_ctor_get_uint8(v_s_862_, sizeof(void*)*3 + 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v_s_862_);
if (v_isSharedCheck_914_ == 0)
{
v___x_872_ = v_s_862_;
v_isShared_873_ = v_isSharedCheck_914_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_error_x3f_866_);
lean_inc(v_pos_864_);
lean_inc(v_imports_863_);
lean_dec(v_s_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_914_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_string_utf8_at_end(v_input_749_, v_pos_864_);
if (v___x_874_ == 0)
{
lean_object* v_i_875_; lean_object* v_s_877_; 
v_i_875_ = lean_string_utf8_next_fast(v_input_749_, v_pos_864_);
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
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_imports_863_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_i_875_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_error_x3f_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*3 + 4, v_importAll_870_);
v_s_877_ = v_reuseFailAlloc_909_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v_module_879_; uint8_t v___y_885_; uint32_t v_curr_887_; uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_878_ = lean_string_utf8_extract(v_input_749_, v_startPart_860_, v_pos_864_);
lean_dec(v_pos_864_);
v_module_879_ = l_Lean_Name_str___override(v_module_751_, v___x_878_);
v_curr_887_ = lean_string_utf8_get(v_input_749_, v_i_875_);
v___x_888_ = 46;
v___x_889_ = lean_uint32_dec_eq(v_curr_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_error_x3f_866_);
lean_dec_ref(v_imports_863_);
v___x_890_ = lean_apply_3(v_finalize_750_, v_module_879_, v_input_749_, v_s_877_);
return v___x_890_;
}
else
{
lean_object* v_i_891_; uint8_t v___x_892_; 
v_i_891_ = lean_string_utf8_next(v_input_749_, v_i_875_);
v___x_892_ = lean_string_utf8_at_end(v_input_749_, v_i_891_);
if (v___x_892_ == 0)
{
uint32_t v_curr_893_; uint8_t v___y_900_; uint32_t v___x_905_; uint8_t v___x_906_; 
v_curr_893_ = lean_string_utf8_get_fast(v_input_749_, v_i_891_);
lean_dec(v_i_891_);
v___x_905_ = 65;
v___x_906_ = lean_uint32_dec_le(v___x_905_, v_curr_893_);
if (v___x_906_ == 0)
{
v___y_900_ = v___x_906_;
goto v___jp_899_;
}
else
{
uint32_t v___x_907_; uint8_t v___x_908_; 
v___x_907_ = 90;
v___x_908_ = lean_uint32_dec_le(v_curr_893_, v___x_907_);
v___y_900_ = v___x_908_;
goto v___jp_899_;
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
v___x_898_ = lean_uint32_dec_eq(v_curr_893_, v___x_779_);
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
if (v___y_900_ == 0)
{
uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = 97;
v___x_902_ = lean_uint32_dec_le(v___x_901_, v_curr_893_);
if (v___x_902_ == 0)
{
goto v___jp_894_;
}
else
{
uint32_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = 122;
v___x_904_ = lean_uint32_dec_le(v_curr_893_, v___x_903_);
if (v___x_904_ == 0)
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
else
{
lean_dec_ref(v_s_877_);
goto v___jp_880_;
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
v___x_881_ = lean_string_utf8_next(v_input_749_, v_i_875_);
v_s_882_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_882_, 0, v_imports_863_);
lean_ctor_set(v_s_882_, 1, v___x_881_);
lean_ctor_set(v_s_882_, 2, v_error_x3f_866_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_s_882_, sizeof(void*)*3 + 4, v_importAll_870_);
v_module_751_ = v_module_879_;
v_s_752_ = v_s_882_;
goto _start;
}
v___jp_884_:
{
if (v___y_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_error_x3f_866_);
lean_dec_ref(v_imports_863_);
v___x_886_ = lean_apply_3(v_finalize_750_, v_module_879_, v_input_749_, v_s_877_);
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
lean_object* v___x_910_; lean_object* v___x_912_; 
lean_dec(v_error_x3f_866_);
lean_dec(v_module_751_);
lean_dec_ref(v_finalize_750_);
lean_dec_ref(v_input_749_);
v___x_910_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 2, v___x_910_);
v___x_912_ = v___x_872_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_imports_863_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_pos_864_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3, v_badModifier_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 1, v_isModule_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 2, v_isMeta_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 3, v_isExported_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*3 + 4, v_importAll_870_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
v___jp_780_:
{
uint32_t v___x_792_; uint8_t v___x_793_; 
v___x_792_ = 95;
v___x_793_ = lean_uint32_dec_eq(v___y_786_, v___x_792_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_isLetterLike(v___y_786_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = lean_uint32_dec_eq(v___y_786_, v___x_779_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v___y_788_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_781_);
v___x_796_ = lean_apply_3(v_finalize_750_, v___y_790_, v_input_749_, v___y_789_);
return v___x_796_;
}
else
{
lean_dec_ref(v___y_789_);
v___y_754_ = v___y_784_;
v___y_755_ = v___y_783_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
goto v___jp_753_;
}
}
else
{
lean_dec_ref(v___y_789_);
v___y_754_ = v___y_784_;
v___y_755_ = v___y_783_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
goto v___jp_753_;
}
}
else
{
lean_dec_ref(v___y_789_);
v___y_754_ = v___y_784_;
v___y_755_ = v___y_783_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_785_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
goto v___jp_753_;
}
}
v___jp_797_:
{
if (v___y_809_ == 0)
{
uint32_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 97;
v___x_811_ = lean_uint32_dec_le(v___x_810_, v___y_803_);
if (v___x_811_ == 0)
{
v___y_781_ = v___y_801_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
goto v___jp_780_;
}
else
{
uint32_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = 122;
v___x_813_ = lean_uint32_dec_le(v___y_803_, v___x_812_);
if (v___x_813_ == 0)
{
v___y_781_ = v___y_801_;
v___y_782_ = v___y_800_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
v___y_789_ = v___y_806_;
v___y_790_ = v___y_807_;
v___y_791_ = v___y_808_;
goto v___jp_780_;
}
else
{
lean_dec_ref(v___y_806_);
v___y_754_ = v___y_798_;
v___y_755_ = v___y_799_;
v___y_756_ = v___y_800_;
v___y_757_ = v___y_801_;
v___y_758_ = v___y_802_;
v___y_759_ = v___y_804_;
v___y_760_ = v___y_805_;
v___y_761_ = v___y_807_;
v___y_762_ = v___y_808_;
goto v___jp_753_;
}
}
}
else
{
lean_dec_ref(v___y_806_);
v___y_754_ = v___y_798_;
v___y_755_ = v___y_799_;
v___y_756_ = v___y_800_;
v___y_757_ = v___y_801_;
v___y_758_ = v___y_802_;
v___y_759_ = v___y_804_;
v___y_760_ = v___y_805_;
v___y_761_ = v___y_807_;
v___y_762_ = v___y_808_;
goto v___jp_753_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_string_utf8_next_fast(v_input_749_, v_pos_767_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_816_);
v___x_818_ = v___x_776_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_imports_766_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_error_x3f_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3, v_badModifier_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3 + 1, v_isModule_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3 + 2, v_isMeta_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3 + 3, v_isExported_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3 + 4, v_importAll_773_);
v___x_818_ = v_reuseFailAlloc_842_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v_s_819_; lean_object* v_imports_820_; lean_object* v_pos_821_; uint8_t v_badModifier_822_; lean_object* v_error_x3f_823_; uint8_t v_isModule_824_; uint8_t v_isMeta_825_; uint8_t v_isExported_826_; uint8_t v_importAll_827_; lean_object* v___x_828_; lean_object* v_module_829_; uint32_t v_curr_830_; uint32_t v___x_831_; uint8_t v___x_832_; 
v_s_819_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_815_, v_curr_778_, v_input_749_, v___x_818_);
v_imports_820_ = lean_ctor_get(v_s_819_, 0);
lean_inc_ref(v_imports_820_);
v_pos_821_ = lean_ctor_get(v_s_819_, 1);
lean_inc(v_pos_821_);
v_badModifier_822_ = lean_ctor_get_uint8(v_s_819_, sizeof(void*)*3);
v_error_x3f_823_ = lean_ctor_get(v_s_819_, 2);
lean_inc(v_error_x3f_823_);
v_isModule_824_ = lean_ctor_get_uint8(v_s_819_, sizeof(void*)*3 + 1);
v_isMeta_825_ = lean_ctor_get_uint8(v_s_819_, sizeof(void*)*3 + 2);
v_isExported_826_ = lean_ctor_get_uint8(v_s_819_, sizeof(void*)*3 + 3);
v_importAll_827_ = lean_ctor_get_uint8(v_s_819_, sizeof(void*)*3 + 4);
v___x_828_ = lean_string_utf8_extract(v_input_749_, v_pos_767_, v_pos_821_);
lean_dec(v_pos_767_);
v_module_829_ = l_Lean_Name_str___override(v_module_751_, v___x_828_);
v_curr_830_ = lean_string_utf8_get(v_input_749_, v_pos_821_);
v___x_831_ = 46;
v___x_832_ = lean_uint32_dec_eq(v_curr_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_error_x3f_823_);
lean_dec(v_pos_821_);
lean_dec_ref(v_imports_820_);
v___x_833_ = lean_apply_3(v_finalize_750_, v_module_829_, v_input_749_, v_s_819_);
return v___x_833_;
}
else
{
lean_object* v_i_834_; uint8_t v___x_835_; 
v_i_834_ = lean_string_utf8_next(v_input_749_, v_pos_821_);
v___x_835_ = lean_string_utf8_at_end(v_input_749_, v_i_834_);
if (v___x_835_ == 0)
{
uint32_t v_curr_836_; uint32_t v___x_837_; uint8_t v___x_838_; 
v_curr_836_ = lean_string_utf8_get_fast(v_input_749_, v_i_834_);
lean_dec(v_i_834_);
v___x_837_ = 65;
v___x_838_ = lean_uint32_dec_le(v___x_837_, v_curr_836_);
if (v___x_838_ == 0)
{
v___y_798_ = v_isMeta_825_;
v___y_799_ = v_isModule_824_;
v___y_800_ = v_badModifier_822_;
v___y_801_ = v_imports_820_;
v___y_802_ = v_pos_821_;
v___y_803_ = v_curr_836_;
v___y_804_ = v_importAll_827_;
v___y_805_ = v_error_x3f_823_;
v___y_806_ = v_s_819_;
v___y_807_ = v_module_829_;
v___y_808_ = v_isExported_826_;
v___y_809_ = v___x_838_;
goto v___jp_797_;
}
else
{
uint32_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 90;
v___x_840_ = lean_uint32_dec_le(v_curr_836_, v___x_839_);
v___y_798_ = v_isMeta_825_;
v___y_799_ = v_isModule_824_;
v___y_800_ = v_badModifier_822_;
v___y_801_ = v_imports_820_;
v___y_802_ = v_pos_821_;
v___y_803_ = v_curr_836_;
v___y_804_ = v_importAll_827_;
v___y_805_ = v_error_x3f_823_;
v___y_806_ = v_s_819_;
v___y_807_ = v_module_829_;
v___y_808_ = v_isExported_826_;
v___y_809_ = v___x_840_;
goto v___jp_797_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v_i_834_);
lean_dec(v_error_x3f_823_);
lean_dec(v_pos_821_);
lean_dec_ref(v_imports_820_);
v___x_841_ = lean_apply_3(v_finalize_750_, v_module_829_, v_input_749_, v_s_819_);
return v___x_841_;
}
}
}
}
v___jp_843_:
{
uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_844_ = 95;
v___x_845_ = lean_uint32_dec_eq(v_curr_778_, v___x_844_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_isLetterLike(v_curr_778_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_del_object(v___x_776_);
lean_dec(v_error_x3f_769_);
lean_dec(v_module_751_);
lean_dec_ref(v_finalize_750_);
lean_dec_ref(v_input_749_);
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_848_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_848_, 0, v_imports_766_);
lean_ctor_set(v___x_848_, 1, v_pos_767_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*3, v_badModifier_768_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*3 + 1, v_isModule_770_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*3 + 2, v_isMeta_771_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*3 + 3, v_isExported_772_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*3 + 4, v_importAll_773_);
return v___x_848_;
}
else
{
v___y_815_ = v___x_846_;
goto v___jp_814_;
}
}
else
{
v___y_815_ = v___x_845_;
goto v___jp_814_;
}
}
v___jp_849_:
{
if (v___y_850_ == 0)
{
uint32_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 97;
v___x_852_ = lean_uint32_dec_le(v___x_851_, v_curr_778_);
if (v___x_852_ == 0)
{
goto v___jp_843_;
}
else
{
uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 122;
v___x_854_ = lean_uint32_dec_le(v_curr_778_, v___x_853_);
if (v___x_854_ == 0)
{
goto v___jp_843_;
}
else
{
v___y_815_ = v___x_854_;
goto v___jp_814_;
}
}
}
else
{
v___y_815_ = v___y_850_;
goto v___jp_814_;
}
}
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v_module_751_);
lean_dec_ref(v_finalize_750_);
lean_dec_ref(v_input_749_);
v___x_919_ = l_Lean_ParseImports_State_mkEOIError(v_s_752_);
return v___x_919_;
}
v___jp_753_:
{
lean_object* v___x_763_; lean_object* v_s_764_; 
v___x_763_ = lean_string_utf8_next(v_input_749_, v___y_758_);
lean_dec(v___y_758_);
v_s_764_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_764_, 0, v___y_757_);
lean_ctor_set(v_s_764_, 1, v___x_763_);
lean_ctor_set(v_s_764_, 2, v___y_760_);
lean_ctor_set_uint8(v_s_764_, sizeof(void*)*3, v___y_756_);
lean_ctor_set_uint8(v_s_764_, sizeof(void*)*3 + 1, v___y_755_);
lean_ctor_set_uint8(v_s_764_, sizeof(void*)*3 + 2, v___y_754_);
lean_ctor_set_uint8(v_s_764_, sizeof(void*)*3 + 3, v___y_762_);
lean_ctor_set_uint8(v_s_764_, sizeof(void*)*3 + 4, v___y_759_);
v_module_751_ = v___y_761_;
v_s_752_ = v_s_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_920_, lean_object* v_input_921_, lean_object* v_s_922_){
_start:
{
uint8_t v_isMeta_923_; uint8_t v_isExported_924_; uint8_t v_importAll_925_; lean_object* v_imp_926_; lean_object* v___x_927_; lean_object* v_s_928_; lean_object* v_imports_929_; lean_object* v_pos_930_; uint8_t v_badModifier_931_; lean_object* v_error_x3f_932_; uint8_t v_isModule_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_945_; 
v_isMeta_923_ = lean_ctor_get_uint8(v_s_922_, sizeof(void*)*3 + 2);
v_isExported_924_ = lean_ctor_get_uint8(v_s_922_, sizeof(void*)*3 + 3);
v_importAll_925_ = lean_ctor_get_uint8(v_s_922_, sizeof(void*)*3 + 4);
v_imp_926_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_926_, 0, v_module_920_);
lean_ctor_set_uint8(v_imp_926_, sizeof(void*)*1, v_importAll_925_);
lean_ctor_set_uint8(v_imp_926_, sizeof(void*)*1 + 1, v_isExported_924_);
lean_ctor_set_uint8(v_imp_926_, sizeof(void*)*1 + 2, v_isMeta_923_);
v___x_927_ = l_Lean_ParseImports_State_pushImport(v_imp_926_, v_s_922_);
v_s_928_ = l_Lean_ParseImports_whitespace(v_input_921_, v___x_927_);
v_imports_929_ = lean_ctor_get(v_s_928_, 0);
v_pos_930_ = lean_ctor_get(v_s_928_, 1);
v_badModifier_931_ = lean_ctor_get_uint8(v_s_928_, sizeof(void*)*3);
v_error_x3f_932_ = lean_ctor_get(v_s_928_, 2);
v_isModule_933_ = lean_ctor_get_uint8(v_s_928_, sizeof(void*)*3 + 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_s_928_);
if (v_isSharedCheck_945_ == 0)
{
v___x_935_ = v_s_928_;
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_error_x3f_932_);
lean_inc(v_pos_930_);
lean_inc(v_imports_929_);
lean_dec(v_s_928_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_945_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
uint8_t v___x_937_; 
v___x_937_ = 0;
if (v_isModule_933_ == 0)
{
uint8_t v___x_938_; lean_object* v___x_940_; 
v___x_938_ = 1;
if (v_isShared_936_ == 0)
{
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_imports_929_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_pos_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_error_x3f_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*3, v_badModifier_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*3 + 1, v_isModule_933_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 2, v___x_937_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 3, v___x_938_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 4, v___x_937_);
return v___x_940_;
}
}
else
{
lean_object* v___x_943_; 
if (v_isShared_936_ == 0)
{
v___x_943_ = v___x_935_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_imports_929_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_pos_930_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_error_x3f_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3, v_badModifier_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*3 + 1, v_isModule_933_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3 + 2, v___x_937_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3 + 3, v___x_937_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3 + 4, v___x_937_);
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_946_, lean_object* v_input_947_, lean_object* v_s_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_946_, v_input_947_, v_s_948_);
lean_dec_ref(v_input_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_951_, lean_object* v_s_952_){
_start:
{
lean_object* v_finalize_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_finalize_953_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_954_ = lean_box(0);
v___x_955_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_951_, v_finalize_953_, v___x_954_, v_s_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_956_, lean_object* v_input_957_, lean_object* v_s_958_){
_start:
{
lean_object* v_pos_959_; lean_object* v_s_960_; lean_object* v_error_x3f_961_; 
v_pos_959_ = lean_ctor_get(v_s_958_, 1);
lean_inc(v_pos_959_);
v_s_960_ = lean_apply_2(v_p_956_, v_input_957_, v_s_958_);
v_error_x3f_961_ = lean_ctor_get(v_s_960_, 2);
lean_inc(v_error_x3f_961_);
if (lean_obj_tag(v_error_x3f_961_) == 1)
{
lean_object* v_imports_962_; uint8_t v_badModifier_963_; uint8_t v_isModule_964_; uint8_t v_isMeta_965_; uint8_t v_isExported_966_; uint8_t v_importAll_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_imports_962_ = lean_ctor_get(v_s_960_, 0);
v_badModifier_963_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*3);
v_isModule_964_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*3 + 1);
v_isMeta_965_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*3 + 2);
v_isExported_966_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*3 + 3);
v_importAll_967_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*3 + 4);
v_isSharedCheck_974_ = !lean_is_exclusive(v_s_960_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; lean_object* v_unused_976_; 
v_unused_975_ = lean_ctor_get(v_s_960_, 2);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_s_960_, 1);
lean_dec(v_unused_976_);
v___x_969_ = v_s_960_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_imports_962_);
lean_dec(v_s_960_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_pos_959_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_imports_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_pos_959_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_error_x3f_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3, v_badModifier_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 1, v_isModule_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 2, v_isMeta_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 3, v_isExported_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 4, v_importAll_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_dec(v_error_x3f_961_);
lean_dec(v_pos_959_);
return v_s_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_980_, lean_object* v_input_981_, lean_object* v_s_982_){
_start:
{
lean_object* v_pos_983_; lean_object* v_s_984_; lean_object* v_error_x3f_985_; 
v_pos_983_ = lean_ctor_get(v_s_982_, 1);
lean_inc(v_pos_983_);
lean_inc_ref(v_p_980_);
lean_inc_ref(v_input_981_);
v_s_984_ = lean_apply_2(v_p_980_, v_input_981_, v_s_982_);
v_error_x3f_985_ = lean_ctor_get(v_s_984_, 2);
lean_inc(v_error_x3f_985_);
if (lean_obj_tag(v_error_x3f_985_) == 1)
{
lean_object* v_imports_986_; lean_object* v_pos_987_; uint8_t v_isModule_988_; uint8_t v_isMeta_989_; uint8_t v_isExported_990_; uint8_t v_importAll_991_; uint8_t v_decide_992_; 
lean_dec_ref_known(v_error_x3f_985_, 1);
lean_dec_ref(v_input_981_);
lean_dec_ref(v_p_980_);
v_imports_986_ = lean_ctor_get(v_s_984_, 0);
lean_inc_ref(v_imports_986_);
v_pos_987_ = lean_ctor_get(v_s_984_, 1);
lean_inc(v_pos_987_);
v_isModule_988_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 1);
v_isMeta_989_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 2);
v_isExported_990_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 3);
v_importAll_991_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 4);
v_decide_992_ = lean_nat_dec_eq(v_pos_987_, v_pos_983_);
lean_dec(v_pos_983_);
if (v_decide_992_ == 0)
{
lean_dec(v_pos_987_);
lean_dec_ref(v_imports_986_);
return v_s_984_;
}
else
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1001_; 
v_isSharedCheck_1001_ = !lean_is_exclusive(v_s_984_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; lean_object* v_unused_1003_; lean_object* v_unused_1004_; 
v_unused_1002_ = lean_ctor_get(v_s_984_, 2);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_s_984_, 1);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_s_984_, 0);
lean_dec(v_unused_1004_);
v___x_994_ = v_s_984_;
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
else
{
lean_dec(v_s_984_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = 0;
v___x_997_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 2, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_imports_986_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_pos_987_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v___x_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3 + 1, v_isModule_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3 + 2, v_isMeta_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3 + 3, v_isExported_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3 + 4, v_importAll_991_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*3, v___x_996_);
return v___x_999_;
}
}
}
}
else
{
uint8_t v_badModifier_1005_; 
lean_dec(v_error_x3f_985_);
v_badModifier_1005_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3);
if (v_badModifier_1005_ == 0)
{
lean_dec(v_pos_983_);
v_s_982_ = v_s_984_;
goto _start;
}
else
{
lean_object* v_imports_1007_; uint8_t v_isModule_1008_; uint8_t v_isMeta_1009_; uint8_t v_isExported_1010_; uint8_t v_importAll_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_input_981_);
lean_dec_ref(v_p_980_);
v_imports_1007_ = lean_ctor_get(v_s_984_, 0);
v_isModule_1008_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 1);
v_isMeta_1009_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 2);
v_isExported_1010_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 3);
v_importAll_1011_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*3 + 4);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_s_984_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1021_ = lean_ctor_get(v_s_984_, 2);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_s_984_, 1);
lean_dec(v_unused_1022_);
v___x_1013_ = v_s_984_;
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_imports_1007_);
lean_dec(v_s_984_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = 0;
v___x_1016_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 2, v___x_1016_);
lean_ctor_set(v___x_1013_, 1, v_pos_983_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_imports_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_pos_983_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v___x_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*3 + 1, v_isModule_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*3 + 2, v_isMeta_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*3 + 3, v_isExported_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*3 + 4, v_importAll_1011_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*3, v___x_1015_);
return v___x_1018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1023_, lean_object* v_s_1024_){
_start:
{
if (v_isModule_1023_ == 0)
{
lean_object* v_imports_1025_; lean_object* v_pos_1026_; uint8_t v_badModifier_1027_; lean_object* v_error_x3f_1028_; uint8_t v_isMeta_1029_; uint8_t v_importAll_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_imports_1025_ = lean_ctor_get(v_s_1024_, 0);
v_pos_1026_ = lean_ctor_get(v_s_1024_, 1);
v_badModifier_1027_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3);
v_error_x3f_1028_ = lean_ctor_get(v_s_1024_, 2);
v_isMeta_1029_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3 + 2);
v_importAll_1030_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3 + 4);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_s_1024_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v_s_1024_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_error_x3f_1028_);
lean_inc(v_pos_1026_);
lean_inc(v_imports_1025_);
lean_dec(v_s_1024_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
uint8_t v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = 1;
if (v_isShared_1033_ == 0)
{
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_imports_1025_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_pos_1026_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_error_x3f_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3, v_badModifier_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3 + 2, v_isMeta_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*3 + 4, v_importAll_1030_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*3 + 1, v_isModule_1023_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*3 + 3, v___x_1034_);
return v___x_1036_;
}
}
}
else
{
lean_object* v_imports_1039_; lean_object* v_pos_1040_; uint8_t v_badModifier_1041_; lean_object* v_error_x3f_1042_; uint8_t v_isMeta_1043_; uint8_t v_importAll_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_imports_1039_ = lean_ctor_get(v_s_1024_, 0);
v_pos_1040_ = lean_ctor_get(v_s_1024_, 1);
v_badModifier_1041_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3);
v_error_x3f_1042_ = lean_ctor_get(v_s_1024_, 2);
v_isMeta_1043_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3 + 2);
v_importAll_1044_ = lean_ctor_get_uint8(v_s_1024_, sizeof(void*)*3 + 4);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_s_1024_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v_s_1024_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_error_x3f_1042_);
lean_inc(v_pos_1040_);
lean_inc(v_imports_1039_);
lean_dec(v_s_1024_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
uint8_t v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = 0;
if (v_isShared_1047_ == 0)
{
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_imports_1039_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_pos_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_error_x3f_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, sizeof(void*)*3, v_badModifier_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, sizeof(void*)*3 + 2, v_isMeta_1043_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, sizeof(void*)*3 + 4, v_importAll_1044_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*3 + 1, v_isModule_1023_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*3 + 3, v___x_1048_);
return v___x_1050_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1057_, lean_object* v_x_1058_, lean_object* v_s_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1057_, v_s_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1061_, lean_object* v_x_1062_, lean_object* v_s_1063_){
_start:
{
uint8_t v_isModule_boxed_1064_; lean_object* v_res_1065_; 
v_isModule_boxed_1064_ = lean_unbox(v_isModule_1061_);
v_res_1065_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1064_, v_x_1062_, v_s_1063_);
lean_dec_ref(v_x_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1066_){
_start:
{
lean_object* v_imports_1067_; lean_object* v_pos_1068_; uint8_t v_badModifier_1069_; lean_object* v_error_x3f_1070_; uint8_t v_isModule_1071_; uint8_t v_isMeta_1072_; uint8_t v_isExported_1073_; uint8_t v_importAll_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
v_imports_1067_ = lean_ctor_get(v_s_1066_, 0);
v_pos_1068_ = lean_ctor_get(v_s_1066_, 1);
v_badModifier_1069_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3);
v_error_x3f_1070_ = lean_ctor_get(v_s_1066_, 2);
v_isModule_1071_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 1);
v_isMeta_1072_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 2);
v_isExported_1073_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 3);
v_importAll_1074_ = lean_ctor_get_uint8(v_s_1066_, sizeof(void*)*3 + 4);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_s_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1076_ = v_s_1066_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_error_x3f_1070_);
lean_inc(v_pos_1068_);
lean_inc(v_imports_1067_);
lean_dec(v_s_1066_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
uint8_t v___x_1078_; 
v___x_1078_ = 1;
if (v_isModule_1071_ == 0)
{
lean_object* v___x_1080_; 
if (v_isShared_1077_ == 0)
{
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_imports_1067_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_pos_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_error_x3f_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 1, v_isModule_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 2, v_isMeta_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 3, v_isExported_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 4, v_importAll_1074_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*3, v___x_1078_);
return v___x_1080_;
}
}
else
{
lean_object* v___x_1083_; 
if (v_isShared_1077_ == 0)
{
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_imports_1067_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_pos_1068_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_error_x3f_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*3, v_badModifier_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*3 + 1, v_isModule_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*3 + 3, v_isExported_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*3 + 4, v_importAll_1074_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*3 + 2, v___x_1078_);
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1086_, lean_object* v_s_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_ParseImports_setMeta___redArg(v_s_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1089_, lean_object* v_s_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_ParseImports_setMeta(v_x_1089_, v_s_1090_);
lean_dec_ref(v_x_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1092_){
_start:
{
lean_object* v_imports_1093_; lean_object* v_pos_1094_; uint8_t v_badModifier_1095_; lean_object* v_error_x3f_1096_; uint8_t v_isModule_1097_; uint8_t v_isMeta_1098_; uint8_t v_isExported_1099_; uint8_t v_importAll_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
v_imports_1093_ = lean_ctor_get(v_s_1092_, 0);
v_pos_1094_ = lean_ctor_get(v_s_1092_, 1);
v_badModifier_1095_ = lean_ctor_get_uint8(v_s_1092_, sizeof(void*)*3);
v_error_x3f_1096_ = lean_ctor_get(v_s_1092_, 2);
v_isModule_1097_ = lean_ctor_get_uint8(v_s_1092_, sizeof(void*)*3 + 1);
v_isMeta_1098_ = lean_ctor_get_uint8(v_s_1092_, sizeof(void*)*3 + 2);
v_isExported_1099_ = lean_ctor_get_uint8(v_s_1092_, sizeof(void*)*3 + 3);
v_importAll_1100_ = lean_ctor_get_uint8(v_s_1092_, sizeof(void*)*3 + 4);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_s_1092_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1102_ = v_s_1092_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_error_x3f_1096_);
lean_inc(v_pos_1094_);
lean_inc(v_imports_1093_);
lean_dec(v_s_1092_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___x_1104_; 
v___x_1104_ = 1;
if (v_isModule_1097_ == 0)
{
lean_object* v___x_1106_; 
if (v_isShared_1103_ == 0)
{
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_imports_1093_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_pos_1094_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_error_x3f_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 1, v_isModule_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 2, v_isMeta_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 3, v_isExported_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 4, v_importAll_1100_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_ctor_set_uint8(v___x_1106_, sizeof(void*)*3, v___x_1104_);
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; 
if (v_isShared_1103_ == 0)
{
v___x_1109_ = v___x_1102_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_imports_1093_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_pos_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_error_x3f_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3, v_badModifier_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3 + 1, v_isModule_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3 + 2, v_isMeta_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3 + 4, v_importAll_1100_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*3 + 3, v___x_1104_);
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1112_, lean_object* v_s_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_ParseImports_setExported___redArg(v_s_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1115_, lean_object* v_s_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_ParseImports_setExported(v_x_1115_, v_s_1116_);
lean_dec_ref(v_x_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1118_){
_start:
{
lean_object* v_imports_1119_; lean_object* v_pos_1120_; uint8_t v_badModifier_1121_; lean_object* v_error_x3f_1122_; uint8_t v_isModule_1123_; uint8_t v_isMeta_1124_; uint8_t v_isExported_1125_; uint8_t v_importAll_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1137_; 
v_imports_1119_ = lean_ctor_get(v_s_1118_, 0);
v_pos_1120_ = lean_ctor_get(v_s_1118_, 1);
v_badModifier_1121_ = lean_ctor_get_uint8(v_s_1118_, sizeof(void*)*3);
v_error_x3f_1122_ = lean_ctor_get(v_s_1118_, 2);
v_isModule_1123_ = lean_ctor_get_uint8(v_s_1118_, sizeof(void*)*3 + 1);
v_isMeta_1124_ = lean_ctor_get_uint8(v_s_1118_, sizeof(void*)*3 + 2);
v_isExported_1125_ = lean_ctor_get_uint8(v_s_1118_, sizeof(void*)*3 + 3);
v_importAll_1126_ = lean_ctor_get_uint8(v_s_1118_, sizeof(void*)*3 + 4);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_s_1118_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1128_ = v_s_1118_;
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_error_x3f_1122_);
lean_inc(v_pos_1120_);
lean_inc(v_imports_1119_);
lean_dec(v_s_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = 1;
if (v_isModule_1123_ == 0)
{
lean_object* v___x_1132_; 
if (v_isShared_1129_ == 0)
{
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_imports_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_pos_1120_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_error_x3f_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3 + 1, v_isModule_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3 + 2, v_isMeta_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3 + 3, v_isExported_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3 + 4, v_importAll_1126_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*3, v___x_1130_);
return v___x_1132_;
}
}
else
{
lean_object* v___x_1135_; 
if (v_isShared_1129_ == 0)
{
v___x_1135_ = v___x_1128_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_imports_1119_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_pos_1120_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_error_x3f_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*3, v_badModifier_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*3 + 1, v_isModule_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*3 + 2, v_isMeta_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1136_, sizeof(void*)*3 + 3, v_isExported_1125_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*3 + 4, v___x_1130_);
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1138_, lean_object* v_s_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1141_, lean_object* v_s_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_ParseImports_setImportAll(v_x_1141_, v_s_1142_);
lean_dec_ref(v_x_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1147_, lean_object* v_input_1148_, lean_object* v_s_1149_, lean_object* v_i_1150_, lean_object* v_j_1151_){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_string_utf8_at_end(v_k_1147_, v_i_1150_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; lean_object* v_s_1155_; uint8_t v___x_1161_; 
v___x_1153_ = 1;
v___x_1161_ = lean_string_utf8_at_end(v_input_1148_, v_j_1151_);
if (v___x_1161_ == 0)
{
uint32_t v_curr_u2081_1162_; uint32_t v_curr_u2082_1163_; uint8_t v___x_1164_; 
v_curr_u2081_1162_ = lean_string_utf8_get_fast(v_k_1147_, v_i_1150_);
v_curr_u2082_1163_ = lean_string_utf8_get_fast(v_input_1148_, v_j_1151_);
v___x_1164_ = lean_uint32_dec_eq(v_curr_u2081_1162_, v_curr_u2082_1163_);
if (v___x_1164_ == 0)
{
lean_dec(v_j_1151_);
lean_dec(v_i_1150_);
v_s_1155_ = v_s_1149_;
goto v___jp_1154_;
}
else
{
if (v___x_1161_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_string_utf8_next_fast(v_k_1147_, v_i_1150_);
lean_dec(v_i_1150_);
v___x_1166_ = lean_string_utf8_next_fast(v_input_1148_, v_j_1151_);
lean_dec(v_j_1151_);
v_i_1150_ = v___x_1165_;
v_j_1151_ = v___x_1166_;
goto _start;
}
else
{
lean_dec(v_j_1151_);
lean_dec(v_i_1150_);
v_s_1155_ = v_s_1149_;
goto v___jp_1154_;
}
}
}
else
{
lean_dec(v_j_1151_);
lean_dec(v_i_1150_);
v_s_1155_ = v_s_1149_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1157_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1, v___x_1152_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1 + 1, v___x_1153_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1 + 2, v___x_1153_);
v___x_1158_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1, v___x_1152_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1 + 1, v___x_1153_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*1 + 2, v___x_1152_);
v___x_1159_ = l_Lean_ParseImports_State_pushImport(v___x_1158_, v_s_1155_);
v___x_1160_ = l_Lean_ParseImports_State_pushImport(v___x_1157_, v___x_1159_);
return v___x_1160_;
}
}
else
{
lean_object* v_imports_1168_; uint8_t v_badModifier_1169_; lean_object* v_error_x3f_1170_; uint8_t v_isModule_1171_; uint8_t v_isMeta_1172_; uint8_t v_isExported_1173_; uint8_t v_importAll_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_i_1150_);
v_imports_1168_ = lean_ctor_get(v_s_1149_, 0);
v_badModifier_1169_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3);
v_error_x3f_1170_ = lean_ctor_get(v_s_1149_, 2);
v_isModule_1171_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 1);
v_isMeta_1172_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 2);
v_isExported_1173_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 3);
v_importAll_1174_ = lean_ctor_get_uint8(v_s_1149_, sizeof(void*)*3 + 4);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_s_1149_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_s_1149_, 1);
lean_dec(v_unused_1183_);
v___x_1176_ = v_s_1149_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_error_x3f_1170_);
lean_inc(v_imports_1168_);
lean_dec(v_s_1149_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_j_1151_);
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_imports_1168_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_j_1151_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_error_x3f_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1181_, sizeof(void*)*3, v_badModifier_1169_);
lean_ctor_set_uint8(v_reuseFailAlloc_1181_, sizeof(void*)*3 + 1, v_isModule_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1181_, sizeof(void*)*3 + 2, v_isMeta_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1181_, sizeof(void*)*3 + 3, v_isExported_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1181_, sizeof(void*)*3 + 4, v_importAll_1174_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_ParseImports_whitespace(v_input_1148_, v___x_1179_);
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1184_, lean_object* v_input_1185_, lean_object* v_s_1186_, lean_object* v_i_1187_, lean_object* v_j_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1184_, v_input_1185_, v_s_1186_, v_i_1187_, v_j_1188_);
lean_dec_ref(v_input_1185_);
lean_dec_ref(v_k_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1193_, lean_object* v_input_1194_, lean_object* v_s_1195_, lean_object* v_i_1196_, lean_object* v_j_1197_){
_start:
{
lean_object* v_s_1199_; uint8_t v___x_1216_; 
v___x_1216_ = lean_string_utf8_at_end(v_k_1193_, v_i_1196_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_string_utf8_at_end(v_input_1194_, v_j_1197_);
if (v___x_1217_ == 0)
{
uint32_t v_curr_u2081_1218_; uint32_t v_curr_u2082_1219_; uint8_t v___x_1220_; 
v_curr_u2081_1218_ = lean_string_utf8_get_fast(v_k_1193_, v_i_1196_);
v_curr_u2082_1219_ = lean_string_utf8_get_fast(v_input_1194_, v_j_1197_);
v___x_1220_ = lean_uint32_dec_eq(v_curr_u2081_1218_, v_curr_u2082_1219_);
if (v___x_1220_ == 0)
{
lean_dec(v_j_1197_);
lean_dec(v_i_1196_);
v_s_1199_ = v_s_1195_;
goto v___jp_1198_;
}
else
{
if (v___x_1217_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_string_utf8_next_fast(v_k_1193_, v_i_1196_);
lean_dec(v_i_1196_);
v___x_1222_ = lean_string_utf8_next_fast(v_input_1194_, v_j_1197_);
lean_dec(v_j_1197_);
v_i_1196_ = v___x_1221_;
v_j_1197_ = v___x_1222_;
goto _start;
}
else
{
lean_dec(v_j_1197_);
lean_dec(v_i_1196_);
v_s_1199_ = v_s_1195_;
goto v___jp_1198_;
}
}
}
else
{
lean_dec(v_j_1197_);
lean_dec(v_i_1196_);
v_s_1199_ = v_s_1195_;
goto v___jp_1198_;
}
}
else
{
lean_object* v_imports_1224_; uint8_t v_badModifier_1225_; lean_object* v_error_x3f_1226_; uint8_t v_isModule_1227_; uint8_t v_isMeta_1228_; uint8_t v_isExported_1229_; uint8_t v_importAll_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_i_1196_);
v_imports_1224_ = lean_ctor_get(v_s_1195_, 0);
v_badModifier_1225_ = lean_ctor_get_uint8(v_s_1195_, sizeof(void*)*3);
v_error_x3f_1226_ = lean_ctor_get(v_s_1195_, 2);
v_isModule_1227_ = lean_ctor_get_uint8(v_s_1195_, sizeof(void*)*3 + 1);
v_isMeta_1228_ = lean_ctor_get_uint8(v_s_1195_, sizeof(void*)*3 + 2);
v_isExported_1229_ = lean_ctor_get_uint8(v_s_1195_, sizeof(void*)*3 + 3);
v_importAll_1230_ = lean_ctor_get_uint8(v_s_1195_, sizeof(void*)*3 + 4);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_s_1195_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_s_1195_, 1);
lean_dec(v_unused_1239_);
v___x_1232_ = v_s_1195_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_error_x3f_1226_);
lean_inc(v_imports_1224_);
lean_dec(v_s_1195_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_j_1197_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_imports_1224_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_j_1197_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_error_x3f_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3, v_badModifier_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 1, v_isModule_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 2, v_isMeta_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 3, v_isExported_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 4, v_importAll_1230_);
v___x_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_ParseImports_whitespace(v_input_1194_, v___x_1235_);
return v___x_1236_;
}
}
}
v___jp_1198_:
{
lean_object* v_imports_1200_; lean_object* v_pos_1201_; uint8_t v_badModifier_1202_; uint8_t v_isModule_1203_; uint8_t v_isMeta_1204_; uint8_t v_isExported_1205_; uint8_t v_importAll_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_imports_1200_ = lean_ctor_get(v_s_1199_, 0);
v_pos_1201_ = lean_ctor_get(v_s_1199_, 1);
v_badModifier_1202_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*3);
v_isModule_1203_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*3 + 1);
v_isMeta_1204_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*3 + 2);
v_isExported_1205_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*3 + 3);
v_importAll_1206_ = lean_ctor_get_uint8(v_s_1199_, sizeof(void*)*3 + 4);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_s_1199_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_s_1199_, 2);
lean_dec(v_unused_1215_);
v___x_1208_ = v_s_1199_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_pos_1201_);
lean_inc(v_imports_1200_);
lean_dec(v_s_1199_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 2, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_imports_1200_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_pos_1201_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v___x_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*3, v_badModifier_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*3 + 1, v_isModule_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*3 + 2, v_isMeta_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*3 + 3, v_isExported_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*3 + 4, v_importAll_1206_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1240_, lean_object* v_input_1241_, lean_object* v_s_1242_, lean_object* v_i_1243_, lean_object* v_j_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1240_, v_input_1241_, v_s_1242_, v_i_1243_, v_j_1244_);
lean_dec_ref(v_input_1241_);
lean_dec_ref(v_k_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1246_, lean_object* v_input_1247_, lean_object* v_s_1248_, lean_object* v_i_1249_, lean_object* v_j_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_string_utf8_at_end(v_k_1246_, v_i_1249_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_string_utf8_at_end(v_input_1247_, v_j_1250_);
if (v___x_1252_ == 0)
{
uint32_t v_curr_u2081_1253_; uint32_t v_curr_u2082_1254_; uint8_t v___x_1255_; 
v_curr_u2081_1253_ = lean_string_utf8_get_fast(v_k_1246_, v_i_1249_);
v_curr_u2082_1254_ = lean_string_utf8_get_fast(v_input_1247_, v_j_1250_);
v___x_1255_ = lean_uint32_dec_eq(v_curr_u2081_1253_, v_curr_u2082_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_j_1250_);
lean_dec(v_i_1249_);
return v_s_1248_;
}
else
{
if (v___x_1252_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_string_utf8_next_fast(v_k_1246_, v_i_1249_);
lean_dec(v_i_1249_);
v___x_1257_ = lean_string_utf8_next_fast(v_input_1247_, v_j_1250_);
lean_dec(v_j_1250_);
v_i_1249_ = v___x_1256_;
v_j_1250_ = v___x_1257_;
goto _start;
}
else
{
lean_dec(v_j_1250_);
lean_dec(v_i_1249_);
return v_s_1248_;
}
}
}
else
{
lean_dec(v_j_1250_);
lean_dec(v_i_1249_);
return v_s_1248_;
}
}
else
{
lean_object* v_imports_1259_; uint8_t v_badModifier_1260_; lean_object* v_error_x3f_1261_; uint8_t v_isModule_1262_; uint8_t v_isMeta_1263_; uint8_t v_isExported_1264_; uint8_t v_importAll_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_i_1249_);
v_imports_1259_ = lean_ctor_get(v_s_1248_, 0);
v_badModifier_1260_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*3);
v_error_x3f_1261_ = lean_ctor_get(v_s_1248_, 2);
v_isModule_1262_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*3 + 1);
v_isMeta_1263_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*3 + 2);
v_isExported_1264_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*3 + 3);
v_importAll_1265_ = lean_ctor_get_uint8(v_s_1248_, sizeof(void*)*3 + 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_s_1248_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_s_1248_, 1);
lean_dec(v_unused_1275_);
v___x_1267_ = v_s_1248_;
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_error_x3f_1261_);
lean_inc(v_imports_1259_);
lean_dec(v_s_1248_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_j_1250_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_imports_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_j_1250_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_error_x3f_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3, v_badModifier_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 1, v_isModule_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 2, v_isMeta_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 3, v_isExported_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 4, v_importAll_1265_);
v___x_1270_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Lean_ParseImports_whitespace(v_input_1247_, v___x_1270_);
v___x_1272_ = l_Lean_ParseImports_setImportAll___redArg(v___x_1271_);
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* v_k_1276_, lean_object* v_input_1277_, lean_object* v_s_1278_, lean_object* v_i_1279_, lean_object* v_j_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_1276_, v_input_1277_, v_s_1278_, v_i_1279_, v_j_1280_);
lean_dec_ref(v_input_1277_);
lean_dec_ref(v_k_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* v_k_1282_, lean_object* v_input_1283_, lean_object* v_s_1284_, lean_object* v_i_1285_, lean_object* v_j_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_string_utf8_at_end(v_k_1282_, v_i_1285_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_string_utf8_at_end(v_input_1283_, v_j_1286_);
if (v___x_1288_ == 0)
{
uint32_t v_curr_u2081_1289_; uint32_t v_curr_u2082_1290_; uint8_t v___x_1291_; 
v_curr_u2081_1289_ = lean_string_utf8_get_fast(v_k_1282_, v_i_1285_);
v_curr_u2082_1290_ = lean_string_utf8_get_fast(v_input_1283_, v_j_1286_);
v___x_1291_ = lean_uint32_dec_eq(v_curr_u2081_1289_, v_curr_u2082_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_j_1286_);
lean_dec(v_i_1285_);
return v_s_1284_;
}
else
{
if (v___x_1288_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_string_utf8_next_fast(v_k_1282_, v_i_1285_);
lean_dec(v_i_1285_);
v___x_1293_ = lean_string_utf8_next_fast(v_input_1283_, v_j_1286_);
lean_dec(v_j_1286_);
v_i_1285_ = v___x_1292_;
v_j_1286_ = v___x_1293_;
goto _start;
}
else
{
lean_dec(v_j_1286_);
lean_dec(v_i_1285_);
return v_s_1284_;
}
}
}
else
{
lean_dec(v_j_1286_);
lean_dec(v_i_1285_);
return v_s_1284_;
}
}
else
{
lean_object* v_imports_1295_; uint8_t v_badModifier_1296_; lean_object* v_error_x3f_1297_; uint8_t v_isModule_1298_; uint8_t v_isMeta_1299_; uint8_t v_isExported_1300_; uint8_t v_importAll_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_i_1285_);
v_imports_1295_ = lean_ctor_get(v_s_1284_, 0);
v_badModifier_1296_ = lean_ctor_get_uint8(v_s_1284_, sizeof(void*)*3);
v_error_x3f_1297_ = lean_ctor_get(v_s_1284_, 2);
v_isModule_1298_ = lean_ctor_get_uint8(v_s_1284_, sizeof(void*)*3 + 1);
v_isMeta_1299_ = lean_ctor_get_uint8(v_s_1284_, sizeof(void*)*3 + 2);
v_isExported_1300_ = lean_ctor_get_uint8(v_s_1284_, sizeof(void*)*3 + 3);
v_importAll_1301_ = lean_ctor_get_uint8(v_s_1284_, sizeof(void*)*3 + 4);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_s_1284_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_s_1284_, 1);
lean_dec(v_unused_1311_);
v___x_1303_ = v_s_1284_;
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_error_x3f_1297_);
lean_inc(v_imports_1295_);
lean_dec(v_s_1284_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v_j_1286_);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_imports_1295_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_j_1286_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_error_x3f_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3, v_badModifier_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 1, v_isModule_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 2, v_isMeta_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 3, v_isExported_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 4, v_importAll_1301_);
v___x_1306_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_Lean_ParseImports_whitespace(v_input_1283_, v___x_1306_);
v___x_1308_ = l_Lean_ParseImports_setExported___redArg(v___x_1307_);
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1312_, lean_object* v_input_1313_, lean_object* v_s_1314_, lean_object* v_i_1315_, lean_object* v_j_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1312_, v_input_1313_, v_s_1314_, v_i_1315_, v_j_1316_);
lean_dec_ref(v_input_1313_);
lean_dec_ref(v_k_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1318_, lean_object* v_input_1319_, lean_object* v_s_1320_, lean_object* v_i_1321_, lean_object* v_j_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_string_utf8_at_end(v_k_1318_, v_i_1321_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_string_utf8_at_end(v_input_1319_, v_j_1322_);
if (v___x_1324_ == 0)
{
uint32_t v_curr_u2081_1325_; uint32_t v_curr_u2082_1326_; uint8_t v___x_1327_; 
v_curr_u2081_1325_ = lean_string_utf8_get_fast(v_k_1318_, v_i_1321_);
v_curr_u2082_1326_ = lean_string_utf8_get_fast(v_input_1319_, v_j_1322_);
v___x_1327_ = lean_uint32_dec_eq(v_curr_u2081_1325_, v_curr_u2082_1326_);
if (v___x_1327_ == 0)
{
lean_dec(v_j_1322_);
lean_dec(v_i_1321_);
return v_s_1320_;
}
else
{
if (v___x_1324_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_string_utf8_next_fast(v_k_1318_, v_i_1321_);
lean_dec(v_i_1321_);
v___x_1329_ = lean_string_utf8_next_fast(v_input_1319_, v_j_1322_);
lean_dec(v_j_1322_);
v_i_1321_ = v___x_1328_;
v_j_1322_ = v___x_1329_;
goto _start;
}
else
{
lean_dec(v_j_1322_);
lean_dec(v_i_1321_);
return v_s_1320_;
}
}
}
else
{
lean_dec(v_j_1322_);
lean_dec(v_i_1321_);
return v_s_1320_;
}
}
else
{
lean_object* v_imports_1331_; uint8_t v_badModifier_1332_; lean_object* v_error_x3f_1333_; uint8_t v_isModule_1334_; uint8_t v_isMeta_1335_; uint8_t v_isExported_1336_; uint8_t v_importAll_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_i_1321_);
v_imports_1331_ = lean_ctor_get(v_s_1320_, 0);
v_badModifier_1332_ = lean_ctor_get_uint8(v_s_1320_, sizeof(void*)*3);
v_error_x3f_1333_ = lean_ctor_get(v_s_1320_, 2);
v_isModule_1334_ = lean_ctor_get_uint8(v_s_1320_, sizeof(void*)*3 + 1);
v_isMeta_1335_ = lean_ctor_get_uint8(v_s_1320_, sizeof(void*)*3 + 2);
v_isExported_1336_ = lean_ctor_get_uint8(v_s_1320_, sizeof(void*)*3 + 3);
v_importAll_1337_ = lean_ctor_get_uint8(v_s_1320_, sizeof(void*)*3 + 4);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_s_1320_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_s_1320_, 1);
lean_dec(v_unused_1347_);
v___x_1339_ = v_s_1320_;
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_error_x3f_1333_);
lean_inc(v_imports_1331_);
lean_dec(v_s_1320_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_j_1322_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_imports_1331_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_j_1322_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_error_x3f_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1345_, sizeof(void*)*3, v_badModifier_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1345_, sizeof(void*)*3 + 1, v_isModule_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1345_, sizeof(void*)*3 + 2, v_isMeta_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1345_, sizeof(void*)*3 + 3, v_isExported_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1345_, sizeof(void*)*3 + 4, v_importAll_1337_);
v___x_1342_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = l_Lean_ParseImports_whitespace(v_input_1319_, v___x_1342_);
v___x_1344_ = l_Lean_ParseImports_setMeta___redArg(v___x_1343_);
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1348_, lean_object* v_input_1349_, lean_object* v_s_1350_, lean_object* v_i_1351_, lean_object* v_j_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1348_, v_input_1349_, v_s_1350_, v_i_1351_, v_j_1352_);
lean_dec_ref(v_input_1349_);
lean_dec_ref(v_k_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1358_, lean_object* v_s_1359_){
_start:
{
lean_object* v_pos_1360_; lean_object* v___y_1362_; lean_object* v_imports_1363_; lean_object* v_pos_1364_; uint8_t v_isModule_1365_; uint8_t v_isMeta_1366_; uint8_t v_isExported_1367_; uint8_t v_importAll_1368_; lean_object* v___y_1374_; lean_object* v___y_1401_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_error_x3f_1433_; 
v_pos_1360_ = lean_ctor_get(v_s_1359_, 1);
lean_inc_n(v_pos_1360_, 2);
v___x_1430_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1430_, v_input_1358_, v_s_1359_, v___x_1431_, v_pos_1360_);
v_error_x3f_1433_ = lean_ctor_get(v___x_1432_, 2);
lean_inc(v_error_x3f_1433_);
if (lean_obj_tag(v_error_x3f_1433_) == 1)
{
lean_dec_ref_known(v_error_x3f_1433_, 1);
v___y_1401_ = v___x_1432_;
goto v___jp_1400_;
}
else
{
lean_object* v_pos_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_error_x3f_1437_; 
lean_dec(v_error_x3f_1433_);
v_pos_1434_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_pos_1434_);
v___x_1435_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1436_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1435_, v_input_1358_, v___x_1432_, v___x_1431_, v_pos_1434_);
v_error_x3f_1437_ = lean_ctor_get(v___x_1436_, 2);
lean_inc(v_error_x3f_1437_);
if (lean_obj_tag(v_error_x3f_1437_) == 1)
{
lean_dec_ref_known(v_error_x3f_1437_, 1);
v___y_1401_ = v___x_1436_;
goto v___jp_1400_;
}
else
{
lean_object* v_pos_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v_error_x3f_1437_);
v_pos_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_pos_1438_);
v___x_1439_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1440_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1439_, v_input_1358_, v___x_1436_, v___x_1431_, v_pos_1438_);
v___y_1401_ = v___x_1440_;
goto v___jp_1400_;
}
}
v___jp_1361_:
{
uint8_t v_decide_1369_; 
v_decide_1369_ = lean_nat_dec_eq(v_pos_1364_, v_pos_1360_);
lean_dec(v_pos_1360_);
if (v_decide_1369_ == 0)
{
lean_dec(v_pos_1364_);
lean_dec_ref(v_imports_1363_);
return v___y_1362_;
}
else
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v___y_1362_);
v___x_1370_ = 0;
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1372_, 0, v_imports_1363_);
lean_ctor_set(v___x_1372_, 1, v_pos_1364_);
lean_ctor_set(v___x_1372_, 2, v___x_1371_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3, v___x_1370_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 1, v_isModule_1365_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 2, v_isMeta_1366_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 3, v_isExported_1367_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*3 + 4, v_importAll_1368_);
return v___x_1372_;
}
}
v___jp_1373_:
{
lean_object* v_error_x3f_1375_; 
v_error_x3f_1375_ = lean_ctor_get(v___y_1374_, 2);
if (lean_obj_tag(v_error_x3f_1375_) == 1)
{
lean_object* v_imports_1376_; lean_object* v_pos_1377_; uint8_t v_isModule_1378_; uint8_t v_isMeta_1379_; uint8_t v_isExported_1380_; uint8_t v_importAll_1381_; 
lean_dec_ref(v_input_1358_);
v_imports_1376_ = lean_ctor_get(v___y_1374_, 0);
lean_inc_ref(v_imports_1376_);
v_pos_1377_ = lean_ctor_get(v___y_1374_, 1);
lean_inc(v_pos_1377_);
v_isModule_1378_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 1);
v_isMeta_1379_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 2);
v_isExported_1380_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 3);
v_importAll_1381_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 4);
v___y_1362_ = v___y_1374_;
v_imports_1363_ = v_imports_1376_;
v_pos_1364_ = v_pos_1377_;
v_isModule_1365_ = v_isModule_1378_;
v_isMeta_1366_ = v_isMeta_1379_;
v_isExported_1367_ = v_isExported_1380_;
v_importAll_1368_ = v_importAll_1381_;
goto v___jp_1361_;
}
else
{
uint8_t v_badModifier_1382_; 
v_badModifier_1382_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3);
if (v_badModifier_1382_ == 0)
{
lean_dec(v_pos_1360_);
v_s_1359_ = v___y_1374_;
goto _start;
}
else
{
lean_object* v_imports_1384_; uint8_t v_isModule_1385_; uint8_t v_isMeta_1386_; uint8_t v_isExported_1387_; uint8_t v_importAll_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_input_1358_);
v_imports_1384_ = lean_ctor_get(v___y_1374_, 0);
v_isModule_1385_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 1);
v_isMeta_1386_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 2);
v_isExported_1387_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 3);
v_importAll_1388_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___y_1374_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1398_ = lean_ctor_get(v___y_1374_, 2);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v___y_1374_, 1);
lean_dec(v_unused_1399_);
v___x_1390_ = v___y_1374_;
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_imports_1384_);
lean_dec(v___y_1374_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = 0;
v___x_1393_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 2, v___x_1393_);
lean_ctor_set(v___x_1390_, 1, v_pos_1360_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_imports_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_pos_1360_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v___x_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1396_, sizeof(void*)*3 + 1, v_isModule_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1396_, sizeof(void*)*3 + 2, v_isMeta_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1396_, sizeof(void*)*3 + 3, v_isExported_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1396_, sizeof(void*)*3 + 4, v_importAll_1388_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3, v___x_1392_);
return v___x_1395_;
}
}
}
}
}
v___jp_1400_:
{
lean_object* v_error_x3f_1402_; 
v_error_x3f_1402_ = lean_ctor_get(v___y_1401_, 2);
if (lean_obj_tag(v_error_x3f_1402_) == 1)
{
lean_object* v_imports_1403_; uint8_t v_badModifier_1404_; uint8_t v_isModule_1405_; uint8_t v_isMeta_1406_; uint8_t v_isExported_1407_; uint8_t v_importAll_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_inc_ref(v_error_x3f_1402_);
lean_dec_ref(v_input_1358_);
v_imports_1403_ = lean_ctor_get(v___y_1401_, 0);
v_badModifier_1404_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3);
v_isModule_1405_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 1);
v_isMeta_1406_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 2);
v_isExported_1407_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 3);
v_importAll_1408_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 4);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___y_1401_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; lean_object* v_unused_1417_; 
v_unused_1416_ = lean_ctor_get(v___y_1401_, 2);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v___y_1401_, 1);
lean_dec(v_unused_1417_);
v___x_1410_ = v___y_1401_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_imports_1403_);
lean_dec(v___y_1401_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
lean_inc(v_pos_1360_);
lean_inc_ref(v_imports_1403_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_pos_1360_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_imports_1403_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_pos_1360_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_error_x3f_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3, v_badModifier_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3 + 1, v_isModule_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3 + 2, v_isMeta_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3 + 3, v_isExported_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3 + 4, v_importAll_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_inc(v_pos_1360_);
v___y_1362_ = v___x_1413_;
v_imports_1363_ = v_imports_1403_;
v_pos_1364_ = v_pos_1360_;
v_isModule_1365_ = v_isModule_1405_;
v_isMeta_1366_ = v_isMeta_1406_;
v_isExported_1367_ = v_isExported_1407_;
v_importAll_1368_ = v_importAll_1408_;
goto v___jp_1361_;
}
}
}
else
{
if (lean_obj_tag(v_error_x3f_1402_) == 1)
{
lean_object* v_imports_1418_; lean_object* v_pos_1419_; uint8_t v_isModule_1420_; uint8_t v_isMeta_1421_; uint8_t v_isExported_1422_; uint8_t v_importAll_1423_; 
lean_dec_ref(v_input_1358_);
v_imports_1418_ = lean_ctor_get(v___y_1401_, 0);
lean_inc_ref(v_imports_1418_);
v_pos_1419_ = lean_ctor_get(v___y_1401_, 1);
lean_inc(v_pos_1419_);
v_isModule_1420_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 1);
v_isMeta_1421_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 2);
v_isExported_1422_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 3);
v_importAll_1423_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*3 + 4);
v___y_1362_ = v___y_1401_;
v_imports_1363_ = v_imports_1418_;
v_pos_1364_ = v_pos_1419_;
v_isModule_1365_ = v_isModule_1420_;
v_isMeta_1366_ = v_isMeta_1421_;
v_isExported_1367_ = v_isExported_1422_;
v_importAll_1368_ = v_importAll_1423_;
goto v___jp_1361_;
}
else
{
lean_object* v_pos_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_error_x3f_1428_; 
v_pos_1424_ = lean_ctor_get(v___y_1401_, 1);
lean_inc(v_pos_1424_);
v___x_1425_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1425_, v_input_1358_, v___y_1401_, v___x_1426_, v_pos_1424_);
v_error_x3f_1428_ = lean_ctor_get(v___x_1427_, 2);
lean_inc(v_error_x3f_1428_);
if (lean_obj_tag(v_error_x3f_1428_) == 1)
{
lean_dec_ref_known(v_error_x3f_1428_, 1);
v___y_1374_ = v___x_1427_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1429_; 
lean_dec(v_error_x3f_1428_);
lean_inc_ref(v_input_1358_);
v___x_1429_ = l_Lean_ParseImports_moduleIdent(v_input_1358_, v___x_1427_);
v___y_1374_ = v___x_1429_;
goto v___jp_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1441_, lean_object* v_input_1442_, lean_object* v_s_1443_, lean_object* v_i_1444_, lean_object* v_j_1445_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_string_utf8_at_end(v_k_1441_, v_i_1444_);
if (v___x_1446_ == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_string_utf8_at_end(v_input_1442_, v_j_1445_);
if (v___x_1447_ == 0)
{
uint32_t v_curr_u2081_1448_; uint32_t v_curr_u2082_1449_; uint8_t v___x_1450_; 
v_curr_u2081_1448_ = lean_string_utf8_get_fast(v_k_1441_, v_i_1444_);
v_curr_u2082_1449_ = lean_string_utf8_get_fast(v_input_1442_, v_j_1445_);
v___x_1450_ = lean_uint32_dec_eq(v_curr_u2081_1448_, v_curr_u2082_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_j_1445_);
lean_dec(v_i_1444_);
v___x_1451_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1446_, v_s_1443_);
return v___x_1451_;
}
else
{
if (v___x_1447_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_string_utf8_next_fast(v_k_1441_, v_i_1444_);
lean_dec(v_i_1444_);
v___x_1453_ = lean_string_utf8_next_fast(v_input_1442_, v_j_1445_);
lean_dec(v_j_1445_);
v_i_1444_ = v___x_1452_;
v_j_1445_ = v___x_1453_;
goto _start;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_j_1445_);
lean_dec(v_i_1444_);
v___x_1455_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1446_, v_s_1443_);
return v___x_1455_;
}
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_j_1445_);
lean_dec(v_i_1444_);
v___x_1456_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1446_, v_s_1443_);
return v___x_1456_;
}
}
else
{
lean_object* v_imports_1457_; uint8_t v_badModifier_1458_; lean_object* v_error_x3f_1459_; uint8_t v_isModule_1460_; uint8_t v_isMeta_1461_; uint8_t v_isExported_1462_; uint8_t v_importAll_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_i_1444_);
v_imports_1457_ = lean_ctor_get(v_s_1443_, 0);
v_badModifier_1458_ = lean_ctor_get_uint8(v_s_1443_, sizeof(void*)*3);
v_error_x3f_1459_ = lean_ctor_get(v_s_1443_, 2);
v_isModule_1460_ = lean_ctor_get_uint8(v_s_1443_, sizeof(void*)*3 + 1);
v_isMeta_1461_ = lean_ctor_get_uint8(v_s_1443_, sizeof(void*)*3 + 2);
v_isExported_1462_ = lean_ctor_get_uint8(v_s_1443_, sizeof(void*)*3 + 3);
v_importAll_1463_ = lean_ctor_get_uint8(v_s_1443_, sizeof(void*)*3 + 4);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_s_1443_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_s_1443_, 1);
lean_dec(v_unused_1473_);
v___x_1465_ = v_s_1443_;
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_error_x3f_1459_);
lean_inc(v_imports_1457_);
lean_dec(v_s_1443_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_j_1445_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_imports_1457_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_j_1445_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_error_x3f_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3, v_badModifier_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3 + 1, v_isModule_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3 + 2, v_isMeta_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3 + 3, v_isExported_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3 + 4, v_importAll_1463_);
v___x_1468_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = l_Lean_ParseImports_whitespace(v_input_1442_, v___x_1468_);
v___x_1470_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1446_, v___x_1469_);
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1474_, lean_object* v_input_1475_, lean_object* v_s_1476_, lean_object* v_i_1477_, lean_object* v_j_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1474_, v_input_1475_, v_s_1476_, v_i_1477_, v_j_1478_);
lean_dec_ref(v_input_1475_);
lean_dec_ref(v_k_1474_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_pos_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_s_1487_; lean_object* v_error_x3f_1488_; 
v_pos_1484_ = lean_ctor_get(v_a_1483_, 1);
lean_inc(v_pos_1484_);
v___x_1485_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1486_ = lean_unsigned_to_nat(0u);
v_s_1487_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1485_, v_a_1482_, v_a_1483_, v___x_1486_, v_pos_1484_);
v_error_x3f_1488_ = lean_ctor_get(v_s_1487_, 2);
lean_inc(v_error_x3f_1488_);
if (lean_obj_tag(v_error_x3f_1488_) == 1)
{
lean_dec_ref_known(v_error_x3f_1488_, 1);
lean_dec_ref(v_a_1482_);
return v_s_1487_;
}
else
{
lean_object* v_pos_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_error_x3f_1492_; 
lean_dec(v_error_x3f_1488_);
v_pos_1489_ = lean_ctor_get(v_s_1487_, 1);
lean_inc(v_pos_1489_);
v___x_1490_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1491_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1490_, v_a_1482_, v_s_1487_, v___x_1486_, v_pos_1489_);
v_error_x3f_1492_ = lean_ctor_get(v___x_1491_, 2);
lean_inc(v_error_x3f_1492_);
if (lean_obj_tag(v_error_x3f_1492_) == 1)
{
lean_dec_ref_known(v_error_x3f_1492_, 1);
lean_dec_ref(v_a_1482_);
return v___x_1491_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_error_x3f_1492_);
v___x_1493_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1482_, v___x_1491_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* v_input_1496_, lean_object* v_fileName_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_s_1501_; lean_object* v_error_x3f_1502_; 
v___x_1499_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1500_ = l_Lean_ParseImports_whitespace(v_input_1496_, v___x_1499_);
lean_inc_ref(v_input_1496_);
v_s_1501_ = l_Lean_ParseImports_main(v_input_1496_, v___x_1500_);
v_error_x3f_1502_ = lean_ctor_get(v_s_1501_, 2);
lean_inc(v_error_x3f_1502_);
if (lean_obj_tag(v_error_x3f_1502_) == 1)
{
lean_object* v_pos_1503_; lean_object* v_val_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1526_; 
v_pos_1503_ = lean_ctor_get(v_s_1501_, 1);
lean_inc(v_pos_1503_);
lean_dec_ref(v_s_1501_);
v_val_1504_ = lean_ctor_get(v_error_x3f_1502_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_error_x3f_1502_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1506_ = v_error_x3f_1502_;
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_val_1504_);
lean_dec(v_error_x3f_1502_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1526_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_fileMap_1508_; lean_object* v_pos_1509_; lean_object* v_line_1510_; lean_object* v_column_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v_fileMap_1508_ = l_Lean_String_toFileMap(v_input_1496_);
v_pos_1509_ = l_Lean_FileMap_toPosition(v_fileMap_1508_, v_pos_1503_);
lean_dec(v_pos_1503_);
v_line_1510_ = lean_ctor_get(v_pos_1509_, 0);
lean_inc(v_line_1510_);
v_column_1511_ = lean_ctor_get(v_pos_1509_, 1);
lean_inc(v_column_1511_);
lean_dec_ref(v_pos_1509_);
v___x_1512_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1513_ = lean_string_append(v_fileName_1497_, v___x_1512_);
v___x_1514_ = l_Nat_reprFast(v_line_1510_);
v___x_1515_ = lean_string_append(v___x_1513_, v___x_1514_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = lean_string_append(v___x_1515_, v___x_1512_);
v___x_1517_ = l_Nat_reprFast(v_column_1511_);
v___x_1518_ = lean_string_append(v___x_1516_, v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_string_append(v___x_1520_, v_val_1504_);
lean_dec(v_val_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 18);
lean_ctor_set(v___x_1506_, 0, v___x_1521_);
v___x_1523_ = v___x_1506_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
else
{
lean_object* v_imports_1527_; uint8_t v_isModule_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_error_x3f_1502_);
lean_dec_ref(v_fileName_1497_);
lean_dec_ref(v_input_1496_);
v_imports_1527_ = lean_ctor_get(v_s_1501_, 0);
lean_inc_ref(v_imports_1527_);
v_isModule_1528_ = lean_ctor_get_uint8(v_s_1501_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1501_);
v___x_1529_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1529_, 0, v_imports_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*1, v_isModule_1528_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1531_, lean_object* v_fileName_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_parseImports_x27(v_input_1531_, v_fileName_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1535_, lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 0)
{
lean_object* v___x_1537_; 
lean_dec_ref(v_k_1535_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
else
{
lean_object* v_val_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_val_1538_ = lean_ctor_get(v_x_1536_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v_x_1536_, 1);
v___x_1539_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1538_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_k_1535_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
if (lean_obj_tag(v_a_1543_) == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_array_to_list(v_a_1544_);
return v___x_1545_;
}
else
{
lean_object* v_head_1546_; lean_object* v_tail_1547_; lean_object* v___x_1548_; 
v_head_1546_ = lean_ctor_get(v_a_1543_, 0);
lean_inc(v_head_1546_);
v_tail_1547_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_tail_1547_);
lean_dec_ref_known(v_a_1543_, 2);
v___x_1548_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1544_, v_head_1546_);
v_a_1543_ = v_tail_1547_;
v_a_1544_ = v___x_1548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1550_, size_t v_i_1551_, lean_object* v_bs_1552_){
_start:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_lt(v_i_1551_, v_sz_1550_);
if (v___x_1553_ == 0)
{
return v_bs_1552_;
}
else
{
lean_object* v_v_1554_; lean_object* v___x_1555_; lean_object* v_bs_x27_1556_; lean_object* v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_v_1554_ = lean_array_uget(v_bs_1552_, v_i_1551_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v_bs_x27_1556_ = lean_array_uset(v_bs_1552_, v_i_1551_, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_v_1554_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1551_, v___x_1558_);
v___x_1560_ = lean_array_uset(v_bs_x27_1556_, v_i_1551_, v___x_1557_);
v_i_1551_ = v___x_1559_;
v_bs_1552_ = v___x_1560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_bs_1564_){
_start:
{
size_t v_sz_boxed_1565_; size_t v_i_boxed_1566_; lean_object* v_res_1567_; 
v_sz_boxed_1565_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1566_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1565_, v_i_boxed_1566_, v_bs_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1568_){
_start:
{
size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_sz_1569_ = lean_array_size(v_a_1568_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1569_, v___x_1570_, v_a_1568_);
v___x_1572_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1577_){
_start:
{
lean_object* v_result_x3f_1578_; lean_object* v_errors_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1597_; 
v_result_x3f_1578_ = lean_ctor_get(v_x_1577_, 0);
v_errors_1579_ = lean_ctor_get(v_x_1577_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1577_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1581_ = v_x_1577_;
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_errors_1579_);
lean_inc(v_result_x3f_1578_);
lean_dec(v_x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1583_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1584_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1583_, v_result_x3f_1578_);
v___x_1585_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1586_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1586_);
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1588_ = v___x_1581_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v___x_1589_);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1584_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1594_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1592_, v___x_1593_);
v___x_1595_ = l_Lean_Json_mkObj(v___x_1594_);
lean_dec(v___x_1594_);
return v___x_1595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1603_ == 0)
{
return v_bs_1602_;
}
else
{
lean_object* v_v_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; lean_object* v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v_v_1604_ = lean_array_uget(v_bs_1602_, v_i_1601_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1605_);
v___x_1607_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1604_);
v___x_1608_ = ((size_t)1ULL);
v___x_1609_ = lean_usize_add(v_i_1601_, v___x_1608_);
v___x_1610_ = lean_array_uset(v_bs_x27_1606_, v_i_1601_, v___x_1607_);
v_i_1601_ = v___x_1609_;
v_bs_1602_ = v___x_1610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1612_, lean_object* v_i_1613_, lean_object* v_bs_1614_){
_start:
{
size_t v_sz_boxed_1615_; size_t v_i_boxed_1616_; lean_object* v_res_1617_; 
v_sz_boxed_1615_ = lean_unbox_usize(v_sz_1612_);
lean_dec(v_sz_1612_);
v_i_boxed_1616_ = lean_unbox_usize(v_i_1613_);
lean_dec(v_i_1613_);
v_res_1617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_1615_, v_i_boxed_1616_, v_bs_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* v_a_1618_){
_start:
{
size_t v_sz_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_sz_1619_ = lean_array_size(v_a_1618_);
v___x_1620_ = ((size_t)0ULL);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1619_, v___x_1620_, v_a_1618_);
v___x_1622_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1625_ = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
v___x_1626_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_1624_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
v___x_1631_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1632_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1630_, v___x_1631_);
v___x_1633_ = l_Lean_Json_mkObj(v___x_1632_);
lean_dec(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_bs_1640_);
return v___x_1643_;
}
else
{
lean_object* v_v_1644_; lean_object* v___x_1645_; lean_object* v_bs_x27_1646_; lean_object* v_a_1648_; lean_object* v_a_1654_; lean_object* v___x_1661_; 
v_v_1644_ = lean_array_uget(v_bs_1640_, v_i_1639_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v_bs_x27_1646_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1645_);
v___x_1661_ = l_IO_FS_readFile(v_v_1644_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l_Lean_parseImports_x27(v_a_1662_, v_v_1644_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 1);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v_a_1648_ = v___x_1671_;
goto v___jp_1647_;
}
}
}
else
{
lean_object* v_a_1674_; 
v_a_1674_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1663_, 1);
v_a_1654_ = v_a_1674_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_1675_; 
lean_dec(v_v_1644_);
v_a_1675_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1661_, 1);
v_a_1654_ = v_a_1675_;
goto v___jp_1653_;
}
v___jp_1647_:
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_add(v_i_1639_, v___x_1649_);
v___x_1651_ = lean_array_uset(v_bs_x27_1646_, v_i_1639_, v_a_1648_);
v_i_1639_ = v___x_1650_;
v_bs_1640_ = v___x_1651_;
goto _start;
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_io_error_to_string(v_a_1654_);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_mk_empty_array_with_capacity(v___x_1657_);
v___x_1659_ = lean_array_push(v___x_1658_, v___x_1656_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1655_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v_a_1648_ = v___x_1660_;
goto v___jp_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1676_, lean_object* v_i_1677_, lean_object* v_bs_1678_, lean_object* v___y_1679_){
_start:
{
size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1680_, v_i_boxed_1681_, v_bs_1678_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v_putStr_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_get_stdout();
v_putStr_1686_ = lean_ctor_get(v___x_1685_, 4);
lean_inc_ref(v_putStr_1686_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = lean_apply_2(v_putStr_1686_, v_s_1683_, lean_box(0));
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1691_){
_start:
{
uint32_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = 10;
v___x_1694_ = lean_string_push(v_s_1691_, v___x_1693_);
v___x_1695_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1699_){
_start:
{
size_t v_sz_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v_sz_1701_ = lean_array_size(v_fileNames_1699_);
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1701_, v___x_1702_, v_fileNames_1699_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1704_);
v___x_1706_ = l_Lean_Json_compress(v___x_1705_);
v___x_1707_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1703_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1703_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_printImportsJson(v_fileNames_1716_);
return v_res_1718_;
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
