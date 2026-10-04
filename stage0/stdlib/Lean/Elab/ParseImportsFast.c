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
if (lean_obj_tag(v_error_x3f_412_) == 1)
{
return v_s_411_;
}
else
{
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
if (lean_obj_tag(v_error_x3f_429_) == 1)
{
return v_s_428_;
}
else
{
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
uint32_t v_curr_552_; uint32_t v___x_564_; uint8_t v___x_565_; 
v_curr_552_ = lean_string_utf8_get_fast(v_input_544_, v_i_550_);
lean_dec(v_i_550_);
v___x_564_ = 65;
v___x_565_ = lean_uint32_dec_le(v___x_564_, v_curr_552_);
if (v___x_565_ == 0)
{
goto v___jp_559_;
}
else
{
uint32_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = 90;
v___x_567_ = lean_uint32_dec_le(v_curr_552_, v___x_566_);
if (v___x_567_ == 0)
{
goto v___jp_559_;
}
else
{
return v___x_549_;
}
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
v___x_557_ = l_Lean_idBeginEscape;
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
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 97;
v___x_561_ = lean_uint32_dec_le(v___x_560_, v_curr_552_);
if (v___x_561_ == 0)
{
goto v___jp_553_;
}
else
{
uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 122;
v___x_563_ = lean_uint32_dec_le(v_curr_552_, v___x_562_);
if (v___x_563_ == 0)
{
goto v___jp_553_;
}
else
{
return v___x_549_;
}
}
}
}
else
{
uint8_t v___x_568_; 
lean_dec(v_i_550_);
v___x_568_ = 0;
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_569_, lean_object* v_s_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lean_ParseImports_isIdCont(v_input_569_, v_s_570_);
lean_dec_ref(v_s_570_);
lean_dec_ref(v_input_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_573_, lean_object* v_s_574_){
_start:
{
lean_object* v_imports_575_; lean_object* v_pos_576_; uint8_t v_badModifier_577_; lean_object* v_error_x3f_578_; uint8_t v_isModule_579_; uint8_t v_isMeta_580_; uint8_t v_isExported_581_; uint8_t v_importAll_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_imports_575_ = lean_ctor_get(v_s_574_, 0);
v_pos_576_ = lean_ctor_get(v_s_574_, 1);
v_badModifier_577_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*3);
v_error_x3f_578_ = lean_ctor_get(v_s_574_, 2);
v_isModule_579_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*3 + 1);
v_isMeta_580_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*3 + 2);
v_isExported_581_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*3 + 3);
v_importAll_582_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*3 + 4);
v_isSharedCheck_590_ = !lean_is_exclusive(v_s_574_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_s_574_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_error_x3f_578_);
lean_inc(v_pos_576_);
lean_inc(v_imports_575_);
lean_dec(v_s_574_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_array_push(v_imports_575_, v_i_573_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_pos_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_error_x3f_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*3, v_badModifier_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*3 + 1, v_isModule_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*3 + 2, v_isMeta_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*3 + 3, v_isExported_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*3 + 4, v_importAll_582_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_591_){
_start:
{
uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 95;
v___x_593_ = lean_uint32_dec_eq(v_c_591_, v___x_592_);
if (v___x_593_ == 0)
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 39;
v___x_595_ = lean_uint32_dec_eq(v_c_591_, v___x_594_);
if (v___x_595_ == 0)
{
uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_596_ = 33;
v___x_597_ = lean_uint32_dec_eq(v_c_591_, v___x_596_);
if (v___x_597_ == 0)
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 63;
v___x_599_ = lean_uint32_dec_eq(v_c_591_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_isLetterLike(v_c_591_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_isSubScriptAlnum(v_c_591_);
return v___x_601_;
}
else
{
return v___x_600_;
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
else
{
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_602_){
_start:
{
uint32_t v_c_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v_c_boxed_603_ = lean_unbox_uint32(v_c_602_);
lean_dec(v_c_602_);
v_res_604_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_606_){
_start:
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 65;
v___x_636_ = lean_uint32_dec_le(v___x_635_, v_c_606_);
if (v___x_636_ == 0)
{
goto v___jp_630_;
}
else
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 90;
v___x_638_ = lean_uint32_dec_le(v_c_606_, v___x_637_);
if (v___x_638_ == 0)
{
goto v___jp_630_;
}
else
{
return v___x_638_;
}
}
v___jp_607_:
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 46;
v___x_609_ = lean_uint32_dec_eq(v_c_606_, v___x_608_);
if (v___x_609_ == 0)
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 10;
v___x_611_ = lean_uint32_dec_eq(v_c_606_, v___x_610_);
if (v___x_611_ == 0)
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 32;
v___x_613_ = lean_uint32_dec_eq(v_c_606_, v___x_612_);
if (v___x_613_ == 0)
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 95;
v___x_615_ = lean_uint32_dec_eq(v_c_606_, v___x_614_);
if (v___x_615_ == 0)
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 39;
v___x_617_ = lean_uint32_dec_eq(v_c_606_, v___x_616_);
if (v___x_617_ == 0)
{
uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 33;
v___x_619_ = lean_uint32_dec_eq(v_c_606_, v___x_618_);
if (v___x_619_ == 0)
{
uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 63;
v___x_621_ = lean_uint32_dec_eq(v_c_606_, v___x_620_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_isLetterLike(v_c_606_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_isSubScriptAlnum(v_c_606_);
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
return v___x_617_;
}
}
else
{
return v___x_615_;
}
}
else
{
return v___x_611_;
}
}
else
{
return v___x_609_;
}
}
else
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
v___jp_625_:
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 48;
v___x_627_ = lean_uint32_dec_le(v___x_626_, v_c_606_);
if (v___x_627_ == 0)
{
goto v___jp_607_;
}
else
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 57;
v___x_629_ = lean_uint32_dec_le(v_c_606_, v___x_628_);
if (v___x_629_ == 0)
{
goto v___jp_607_;
}
else
{
return v___x_629_;
}
}
}
v___jp_630_:
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 97;
v___x_632_ = lean_uint32_dec_le(v___x_631_, v_c_606_);
if (v___x_632_ == 0)
{
goto v___jp_625_;
}
else
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 122;
v___x_634_ = lean_uint32_dec_le(v_c_606_, v___x_633_);
if (v___x_634_ == 0)
{
goto v___jp_625_;
}
else
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_639_){
_start:
{
uint32_t v_c_boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v_c_boxed_640_ = lean_unbox_uint32(v_c_639_);
lean_dec(v_c_639_);
v_res_641_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_imports_645_; lean_object* v_pos_646_; uint8_t v_badModifier_647_; lean_object* v_error_x3f_648_; uint8_t v_isModule_649_; uint8_t v_isMeta_650_; uint8_t v_isExported_651_; uint8_t v_importAll_652_; uint8_t v___x_653_; 
v_imports_645_ = lean_ctor_get(v_s_644_, 0);
v_pos_646_ = lean_ctor_get(v_s_644_, 1);
v_badModifier_647_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*3);
v_error_x3f_648_ = lean_ctor_get(v_s_644_, 2);
v_isModule_649_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*3 + 1);
v_isMeta_650_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*3 + 2);
v_isExported_651_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*3 + 3);
v_importAll_652_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*3 + 4);
v___x_653_ = lean_string_utf8_at_end(v_input_643_, v_pos_646_);
if (v___x_653_ == 0)
{
uint32_t v___x_654_; uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_string_utf8_get_fast(v_input_643_, v_pos_646_);
v___x_655_ = l_Lean_idEndEscape;
v___x_656_ = lean_uint32_dec_eq(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
lean_inc(v_error_x3f_648_);
lean_inc(v_pos_646_);
lean_inc_ref(v_imports_645_);
v_isSharedCheck_665_ = !lean_is_exclusive(v_s_644_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_666_ = lean_ctor_get(v_s_644_, 2);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_s_644_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_s_644_, 0);
lean_dec(v_unused_668_);
v___x_658_ = v_s_644_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_dec(v_s_644_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_string_utf8_next_fast(v_input_643_, v_pos_646_);
lean_dec(v_pos_646_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_imports_645_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_error_x3f_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*3, v_badModifier_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*3 + 1, v_isModule_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*3 + 2, v_isMeta_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*3 + 3, v_isExported_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_664_, sizeof(void*)*3 + 4, v_importAll_652_);
v___x_662_ = v_reuseFailAlloc_664_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v_s_644_ = v___x_662_;
goto _start;
}
}
}
else
{
return v_s_644_;
}
}
else
{
return v_s_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_669_, lean_object* v_s_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_669_, v_s_670_);
lean_dec_ref(v_input_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_672_, uint32_t v___x_673_, lean_object* v_input_674_, lean_object* v_s_675_){
_start:
{
lean_object* v_imports_676_; lean_object* v_pos_677_; uint8_t v_badModifier_678_; lean_object* v_error_x3f_679_; uint8_t v_isModule_680_; uint8_t v_isMeta_681_; uint8_t v_isExported_682_; uint8_t v_importAll_683_; uint8_t v___y_685_; uint8_t v___x_698_; 
v_imports_676_ = lean_ctor_get(v_s_675_, 0);
v_pos_677_ = lean_ctor_get(v_s_675_, 1);
v_badModifier_678_ = lean_ctor_get_uint8(v_s_675_, sizeof(void*)*3);
v_error_x3f_679_ = lean_ctor_get(v_s_675_, 2);
v_isModule_680_ = lean_ctor_get_uint8(v_s_675_, sizeof(void*)*3 + 1);
v_isMeta_681_ = lean_ctor_get_uint8(v_s_675_, sizeof(void*)*3 + 2);
v_isExported_682_ = lean_ctor_get_uint8(v_s_675_, sizeof(void*)*3 + 3);
v_importAll_683_ = lean_ctor_get_uint8(v_s_675_, sizeof(void*)*3 + 4);
v___x_698_ = lean_string_utf8_at_end(v_input_674_, v_pos_677_);
if (v___x_698_ == 0)
{
uint32_t v___x_699_; uint8_t v___x_700_; uint32_t v___x_701_; uint32_t v___x_729_; uint8_t v___x_730_; 
v___x_699_ = l_Lean_idBeginEscape;
v___x_700_ = lean_uint32_dec_eq(v___x_673_, v___x_699_);
v___x_701_ = lean_string_utf8_get_fast(v_input_674_, v_pos_677_);
v___x_729_ = 65;
v___x_730_ = lean_uint32_dec_le(v___x_729_, v___x_701_);
if (v___x_730_ == 0)
{
goto v___jp_724_;
}
else
{
uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 90;
v___x_732_ = lean_uint32_dec_le(v___x_701_, v___x_731_);
if (v___x_732_ == 0)
{
goto v___jp_724_;
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
v___jp_702_:
{
uint32_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 46;
v___x_704_ = lean_uint32_dec_eq(v___x_701_, v___x_703_);
if (v___x_704_ == 0)
{
uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 10;
v___x_706_ = lean_uint32_dec_eq(v___x_701_, v___x_705_);
if (v___x_706_ == 0)
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 32;
v___x_708_ = lean_uint32_dec_eq(v___x_701_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 95;
v___x_710_ = lean_uint32_dec_eq(v___x_701_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 39;
v___x_712_ = lean_uint32_dec_eq(v___x_701_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 33;
v___x_714_ = lean_uint32_dec_eq(v___x_701_, v___x_713_);
if (v___x_714_ == 0)
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 63;
v___x_716_ = lean_uint32_dec_eq(v___x_701_, v___x_715_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_isLetterLike(v___x_701_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = l_Lean_isSubScriptAlnum(v___x_701_);
if (v___x_718_ == 0)
{
v___y_685_ = v___y_672_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
if (v___x_717_ == 0)
{
v___y_685_ = v___y_672_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___y_672_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___y_672_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___y_672_;
goto v___jp_684_;
}
}
v___jp_719_:
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 48;
v___x_721_ = lean_uint32_dec_le(v___x_720_, v___x_701_);
if (v___x_721_ == 0)
{
goto v___jp_702_;
}
else
{
uint32_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 57;
v___x_723_ = lean_uint32_dec_le(v___x_701_, v___x_722_);
if (v___x_723_ == 0)
{
goto v___jp_702_;
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
}
v___jp_724_:
{
uint32_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 97;
v___x_726_ = lean_uint32_dec_le(v___x_725_, v___x_701_);
if (v___x_726_ == 0)
{
goto v___jp_719_;
}
else
{
uint32_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 122;
v___x_728_ = lean_uint32_dec_le(v___x_701_, v___x_727_);
if (v___x_728_ == 0)
{
goto v___jp_719_;
}
else
{
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
}
}
else
{
return v_s_675_;
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
lean_inc(v_error_x3f_679_);
lean_inc(v_pos_677_);
lean_inc_ref(v_imports_676_);
v_isSharedCheck_694_ = !lean_is_exclusive(v_s_675_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_695_ = lean_ctor_get(v_s_675_, 2);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_s_675_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_s_675_, 0);
lean_dec(v_unused_697_);
v___x_687_ = v_s_675_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_s_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_string_utf8_next_fast(v_input_674_, v_pos_677_);
lean_dec(v_pos_677_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_imports_676_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_error_x3f_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*3, v_badModifier_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*3 + 1, v_isModule_680_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*3 + 2, v_isMeta_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*3 + 3, v_isExported_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*3 + 4, v_importAll_683_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_s_675_ = v___x_691_;
goto _start;
}
}
}
else
{
return v_s_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_733_, lean_object* v___x_734_, lean_object* v_input_735_, lean_object* v_s_736_){
_start:
{
uint8_t v___y_1012__boxed_737_; uint32_t v___x_1013__boxed_738_; lean_object* v_res_739_; 
v___y_1012__boxed_737_ = lean_unbox(v___y_733_);
v___x_1013__boxed_738_ = lean_unbox_uint32(v___x_734_);
lean_dec(v___x_734_);
v_res_739_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_1012__boxed_737_, v___x_1013__boxed_738_, v_input_735_, v_s_736_);
lean_dec_ref(v_input_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_746_, lean_object* v_finalize_747_, lean_object* v_module_748_, lean_object* v_s_749_){
_start:
{
uint8_t v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; uint8_t v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___y_759_; lean_object* v_imports_763_; lean_object* v_pos_764_; uint8_t v_badModifier_765_; lean_object* v_error_x3f_766_; uint8_t v_isModule_767_; uint8_t v_isMeta_768_; uint8_t v_isExported_769_; uint8_t v_importAll_770_; uint8_t v___x_771_; 
v_imports_763_ = lean_ctor_get(v_s_749_, 0);
v_pos_764_ = lean_ctor_get(v_s_749_, 1);
v_badModifier_765_ = lean_ctor_get_uint8(v_s_749_, sizeof(void*)*3);
v_error_x3f_766_ = lean_ctor_get(v_s_749_, 2);
v_isModule_767_ = lean_ctor_get_uint8(v_s_749_, sizeof(void*)*3 + 1);
v_isMeta_768_ = lean_ctor_get_uint8(v_s_749_, sizeof(void*)*3 + 2);
v_isExported_769_ = lean_ctor_get_uint8(v_s_749_, sizeof(void*)*3 + 3);
v_importAll_770_ = lean_ctor_get_uint8(v_s_749_, sizeof(void*)*3 + 4);
v___x_771_ = lean_string_utf8_at_end(v_input_746_, v_pos_764_);
if (v___x_771_ == 0)
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_909_; 
lean_inc(v_error_x3f_766_);
lean_inc(v_pos_764_);
lean_inc_ref(v_imports_763_);
v_isSharedCheck_909_ = !lean_is_exclusive(v_s_749_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_910_ = lean_ctor_get(v_s_749_, 2);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_s_749_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_s_749_, 0);
lean_dec(v_unused_912_);
v___x_773_ = v_s_749_;
v_isShared_774_ = v_isSharedCheck_909_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_s_749_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_909_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
uint32_t v_curr_775_; uint32_t v___x_776_; uint8_t v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; uint8_t v___y_784_; uint8_t v___y_785_; uint8_t v___y_786_; uint8_t v___y_787_; uint32_t v___y_788_; uint8_t v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; uint8_t v___y_803_; uint8_t v___y_804_; uint32_t v___y_805_; uint8_t v___y_811_; uint8_t v___x_850_; 
v_curr_775_ = lean_string_utf8_get_fast(v_input_746_, v_pos_764_);
v___x_776_ = l_Lean_idBeginEscape;
v___x_850_ = lean_uint32_dec_eq(v_curr_775_, v___x_776_);
if (v___x_850_ == 0)
{
uint32_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 65;
v___x_852_ = lean_uint32_dec_le(v___x_851_, v_curr_775_);
if (v___x_852_ == 0)
{
goto v___jp_845_;
}
else
{
uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 90;
v___x_854_ = lean_uint32_dec_le(v_curr_775_, v___x_853_);
if (v___x_854_ == 0)
{
goto v___jp_845_;
}
else
{
v___y_811_ = v___x_854_;
goto v___jp_810_;
}
}
}
else
{
lean_object* v_startPart_855_; lean_object* v___x_856_; lean_object* v_s_857_; lean_object* v_imports_858_; lean_object* v_pos_859_; uint8_t v_badModifier_860_; lean_object* v_error_x3f_861_; uint8_t v_isModule_862_; uint8_t v_isMeta_863_; uint8_t v_isExported_864_; uint8_t v_importAll_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_773_);
v_startPart_855_ = lean_string_utf8_next_fast(v_input_746_, v_pos_764_);
lean_dec(v_pos_764_);
v___x_856_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_856_, 0, v_imports_763_);
lean_ctor_set(v___x_856_, 1, v_startPart_855_);
lean_ctor_set(v___x_856_, 2, v_error_x3f_766_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*3, v_badModifier_765_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*3 + 1, v_isModule_767_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*3 + 2, v_isMeta_768_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*3 + 3, v_isExported_769_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*3 + 4, v_importAll_770_);
v_s_857_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_746_, v___x_856_);
v_imports_858_ = lean_ctor_get(v_s_857_, 0);
v_pos_859_ = lean_ctor_get(v_s_857_, 1);
v_badModifier_860_ = lean_ctor_get_uint8(v_s_857_, sizeof(void*)*3);
v_error_x3f_861_ = lean_ctor_get(v_s_857_, 2);
v_isModule_862_ = lean_ctor_get_uint8(v_s_857_, sizeof(void*)*3 + 1);
v_isMeta_863_ = lean_ctor_get_uint8(v_s_857_, sizeof(void*)*3 + 2);
v_isExported_864_ = lean_ctor_get_uint8(v_s_857_, sizeof(void*)*3 + 3);
v_importAll_865_ = lean_ctor_get_uint8(v_s_857_, sizeof(void*)*3 + 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v_s_857_);
if (v_isSharedCheck_908_ == 0)
{
v___x_867_ = v_s_857_;
v_isShared_868_ = v_isSharedCheck_908_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_error_x3f_861_);
lean_inc(v_pos_859_);
lean_inc(v_imports_858_);
lean_dec(v_s_857_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_908_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_string_utf8_at_end(v_input_746_, v_pos_859_);
if (v___x_869_ == 0)
{
lean_object* v_i_870_; lean_object* v_s_872_; 
v_i_870_ = lean_string_utf8_next_fast(v_input_746_, v_pos_859_);
lean_inc(v_error_x3f_861_);
lean_inc_ref(v_imports_858_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v_i_870_);
v_s_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_imports_858_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_i_870_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_error_x3f_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*3, v_badModifier_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*3 + 1, v_isModule_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*3 + 2, v_isMeta_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*3 + 3, v_isExported_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*3 + 4, v_importAll_865_);
v_s_872_ = v_reuseFailAlloc_903_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v_module_874_; uint8_t v___y_880_; uint32_t v_curr_882_; uint32_t v___x_883_; uint8_t v___x_884_; 
v___x_873_ = lean_string_utf8_extract(v_input_746_, v_startPart_855_, v_pos_859_);
lean_dec(v_pos_859_);
v_module_874_ = l_Lean_Name_str___override(v_module_748_, v___x_873_);
v_curr_882_ = lean_string_utf8_get(v_input_746_, v_i_870_);
v___x_883_ = 46;
v___x_884_ = lean_uint32_dec_eq(v_curr_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_dec(v_error_x3f_861_);
lean_dec_ref(v_imports_858_);
v___x_885_ = lean_apply_3(v_finalize_747_, v_module_874_, v_input_746_, v_s_872_);
return v___x_885_;
}
else
{
lean_object* v_i_886_; uint8_t v___x_887_; 
v_i_886_ = lean_string_utf8_next(v_input_746_, v_i_870_);
v___x_887_ = lean_string_utf8_at_end(v_input_746_, v_i_886_);
if (v___x_887_ == 0)
{
uint32_t v_curr_888_; uint32_t v___x_899_; uint8_t v___x_900_; 
v_curr_888_ = lean_string_utf8_get_fast(v_input_746_, v_i_886_);
lean_dec(v_i_886_);
v___x_899_ = 65;
v___x_900_ = lean_uint32_dec_le(v___x_899_, v_curr_888_);
if (v___x_900_ == 0)
{
goto v___jp_894_;
}
else
{
uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = 90;
v___x_902_ = lean_uint32_dec_le(v_curr_888_, v___x_901_);
if (v___x_902_ == 0)
{
goto v___jp_894_;
}
else
{
lean_dec_ref(v_s_872_);
goto v___jp_875_;
}
}
v___jp_889_:
{
uint32_t v___x_890_; uint8_t v___x_891_; 
v___x_890_ = 95;
v___x_891_ = lean_uint32_dec_eq(v_curr_888_, v___x_890_);
if (v___x_891_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_isLetterLike(v_curr_888_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = lean_uint32_dec_eq(v_curr_888_, v___x_776_);
v___y_880_ = v___x_893_;
goto v___jp_879_;
}
else
{
lean_dec_ref(v_s_872_);
goto v___jp_875_;
}
}
else
{
lean_dec_ref(v_s_872_);
goto v___jp_875_;
}
}
v___jp_894_:
{
uint32_t v___x_895_; uint8_t v___x_896_; 
v___x_895_ = 97;
v___x_896_ = lean_uint32_dec_le(v___x_895_, v_curr_888_);
if (v___x_896_ == 0)
{
goto v___jp_889_;
}
else
{
uint32_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = 122;
v___x_898_ = lean_uint32_dec_le(v_curr_888_, v___x_897_);
if (v___x_898_ == 0)
{
goto v___jp_889_;
}
else
{
lean_dec_ref(v_s_872_);
goto v___jp_875_;
}
}
}
}
else
{
lean_dec(v_i_886_);
v___y_880_ = v___x_869_;
goto v___jp_879_;
}
}
v___jp_875_:
{
lean_object* v___x_876_; lean_object* v_s_877_; 
v___x_876_ = lean_string_utf8_next(v_input_746_, v_i_870_);
v_s_877_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_877_, 0, v_imports_858_);
lean_ctor_set(v_s_877_, 1, v___x_876_);
lean_ctor_set(v_s_877_, 2, v_error_x3f_861_);
lean_ctor_set_uint8(v_s_877_, sizeof(void*)*3, v_badModifier_860_);
lean_ctor_set_uint8(v_s_877_, sizeof(void*)*3 + 1, v_isModule_862_);
lean_ctor_set_uint8(v_s_877_, sizeof(void*)*3 + 2, v_isMeta_863_);
lean_ctor_set_uint8(v_s_877_, sizeof(void*)*3 + 3, v_isExported_864_);
lean_ctor_set_uint8(v_s_877_, sizeof(void*)*3 + 4, v_importAll_865_);
v_module_748_ = v_module_874_;
v_s_749_ = v_s_877_;
goto _start;
}
v___jp_879_:
{
if (v___y_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_error_x3f_861_);
lean_dec_ref(v_imports_858_);
v___x_881_ = lean_apply_3(v_finalize_747_, v_module_874_, v_input_746_, v_s_872_);
return v___x_881_;
}
else
{
lean_dec_ref(v_s_872_);
goto v___jp_875_;
}
}
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec(v_error_x3f_861_);
lean_dec(v_module_748_);
lean_dec_ref(v_finalize_747_);
lean_dec_ref(v_input_746_);
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v___x_904_);
v___x_906_ = v___x_867_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_imports_858_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_pos_859_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___x_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3, v_badModifier_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 1, v_isModule_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 2, v_isMeta_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 3, v_isExported_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 4, v_importAll_865_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
v___jp_777_:
{
uint32_t v___x_789_; uint8_t v___x_790_; 
v___x_789_ = 95;
v___x_790_ = lean_uint32_dec_eq(v___y_788_, v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; 
v___x_791_ = l_Lean_isLetterLike(v___y_788_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; 
v___x_792_ = lean_uint32_dec_eq(v___y_788_, v___x_776_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
v___x_793_ = lean_apply_3(v_finalize_747_, v___y_780_, v_input_746_, v___y_779_);
return v___x_793_;
}
else
{
lean_dec_ref(v___y_779_);
v___y_751_ = v___y_778_;
v___y_752_ = v___y_780_;
v___y_753_ = v___y_782_;
v___y_754_ = v___y_781_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_783_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
goto v___jp_750_;
}
}
else
{
lean_dec_ref(v___y_779_);
v___y_751_ = v___y_778_;
v___y_752_ = v___y_780_;
v___y_753_ = v___y_782_;
v___y_754_ = v___y_781_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_783_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
goto v___jp_750_;
}
}
else
{
lean_dec_ref(v___y_779_);
v___y_751_ = v___y_778_;
v___y_752_ = v___y_780_;
v___y_753_ = v___y_782_;
v___y_754_ = v___y_781_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_783_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
goto v___jp_750_;
}
}
v___jp_794_:
{
uint32_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = 97;
v___x_807_ = lean_uint32_dec_le(v___x_806_, v___y_805_);
if (v___x_807_ == 0)
{
v___y_778_ = v___y_795_;
v___y_779_ = v___y_796_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_798_;
v___y_783_ = v___y_801_;
v___y_784_ = v___y_800_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
goto v___jp_777_;
}
else
{
uint32_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = 122;
v___x_809_ = lean_uint32_dec_le(v___y_805_, v___x_808_);
if (v___x_809_ == 0)
{
v___y_778_ = v___y_795_;
v___y_779_ = v___y_796_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_799_;
v___y_782_ = v___y_798_;
v___y_783_ = v___y_801_;
v___y_784_ = v___y_800_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v___y_788_ = v___y_805_;
goto v___jp_777_;
}
else
{
lean_dec_ref(v___y_796_);
v___y_751_ = v___y_795_;
v___y_752_ = v___y_797_;
v___y_753_ = v___y_798_;
v___y_754_ = v___y_799_;
v___y_755_ = v___y_800_;
v___y_756_ = v___y_801_;
v___y_757_ = v___y_802_;
v___y_758_ = v___y_803_;
v___y_759_ = v___y_804_;
goto v___jp_750_;
}
}
}
v___jp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_string_utf8_next_fast(v_input_746_, v_pos_764_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_812_);
v___x_814_ = v___x_773_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_imports_763_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_error_x3f_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3, v_badModifier_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3 + 1, v_isModule_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3 + 2, v_isMeta_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3 + 3, v_isExported_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3 + 4, v_importAll_770_);
v___x_814_ = v_reuseFailAlloc_838_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v_s_815_; lean_object* v_imports_816_; lean_object* v_pos_817_; uint8_t v_badModifier_818_; lean_object* v_error_x3f_819_; uint8_t v_isModule_820_; uint8_t v_isMeta_821_; uint8_t v_isExported_822_; uint8_t v_importAll_823_; lean_object* v___x_824_; lean_object* v_module_825_; uint32_t v_curr_826_; uint32_t v___x_827_; uint8_t v___x_828_; 
v_s_815_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_811_, v_curr_775_, v_input_746_, v___x_814_);
v_imports_816_ = lean_ctor_get(v_s_815_, 0);
v_pos_817_ = lean_ctor_get(v_s_815_, 1);
v_badModifier_818_ = lean_ctor_get_uint8(v_s_815_, sizeof(void*)*3);
v_error_x3f_819_ = lean_ctor_get(v_s_815_, 2);
v_isModule_820_ = lean_ctor_get_uint8(v_s_815_, sizeof(void*)*3 + 1);
v_isMeta_821_ = lean_ctor_get_uint8(v_s_815_, sizeof(void*)*3 + 2);
v_isExported_822_ = lean_ctor_get_uint8(v_s_815_, sizeof(void*)*3 + 3);
v_importAll_823_ = lean_ctor_get_uint8(v_s_815_, sizeof(void*)*3 + 4);
v___x_824_ = lean_string_utf8_extract(v_input_746_, v_pos_764_, v_pos_817_);
lean_dec(v_pos_764_);
v_module_825_ = l_Lean_Name_str___override(v_module_748_, v___x_824_);
v_curr_826_ = lean_string_utf8_get(v_input_746_, v_pos_817_);
v___x_827_ = 46;
v___x_828_ = lean_uint32_dec_eq(v_curr_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = lean_apply_3(v_finalize_747_, v_module_825_, v_input_746_, v_s_815_);
return v___x_829_;
}
else
{
lean_object* v_i_830_; uint8_t v___x_831_; 
v_i_830_ = lean_string_utf8_next(v_input_746_, v_pos_817_);
v___x_831_ = lean_string_utf8_at_end(v_input_746_, v_i_830_);
if (v___x_831_ == 0)
{
uint32_t v_curr_832_; uint32_t v___x_833_; uint8_t v___x_834_; 
lean_inc(v_error_x3f_819_);
lean_inc(v_pos_817_);
lean_inc_ref(v_imports_816_);
v_curr_832_ = lean_string_utf8_get_fast(v_input_746_, v_i_830_);
lean_dec(v_i_830_);
v___x_833_ = 65;
v___x_834_ = lean_uint32_dec_le(v___x_833_, v_curr_832_);
if (v___x_834_ == 0)
{
v___y_795_ = v_isModule_820_;
v___y_796_ = v_s_815_;
v___y_797_ = v_module_825_;
v___y_798_ = v_imports_816_;
v___y_799_ = v_pos_817_;
v___y_800_ = v_isExported_822_;
v___y_801_ = v_error_x3f_819_;
v___y_802_ = v_importAll_823_;
v___y_803_ = v_isMeta_821_;
v___y_804_ = v_badModifier_818_;
v___y_805_ = v_curr_832_;
goto v___jp_794_;
}
else
{
uint32_t v___x_835_; uint8_t v___x_836_; 
v___x_835_ = 90;
v___x_836_ = lean_uint32_dec_le(v_curr_832_, v___x_835_);
if (v___x_836_ == 0)
{
v___y_795_ = v_isModule_820_;
v___y_796_ = v_s_815_;
v___y_797_ = v_module_825_;
v___y_798_ = v_imports_816_;
v___y_799_ = v_pos_817_;
v___y_800_ = v_isExported_822_;
v___y_801_ = v_error_x3f_819_;
v___y_802_ = v_importAll_823_;
v___y_803_ = v_isMeta_821_;
v___y_804_ = v_badModifier_818_;
v___y_805_ = v_curr_832_;
goto v___jp_794_;
}
else
{
lean_dec_ref(v_s_815_);
v___y_751_ = v_isModule_820_;
v___y_752_ = v_module_825_;
v___y_753_ = v_imports_816_;
v___y_754_ = v_pos_817_;
v___y_755_ = v_isExported_822_;
v___y_756_ = v_error_x3f_819_;
v___y_757_ = v_importAll_823_;
v___y_758_ = v_isMeta_821_;
v___y_759_ = v_badModifier_818_;
goto v___jp_750_;
}
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_i_830_);
v___x_837_ = lean_apply_3(v_finalize_747_, v_module_825_, v_input_746_, v_s_815_);
return v___x_837_;
}
}
}
}
v___jp_839_:
{
uint32_t v___x_840_; uint8_t v___x_841_; 
v___x_840_ = 95;
v___x_841_ = lean_uint32_dec_eq(v_curr_775_, v___x_840_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_isLetterLike(v_curr_775_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_del_object(v___x_773_);
lean_dec(v_error_x3f_766_);
lean_dec(v_module_748_);
lean_dec_ref(v_finalize_747_);
lean_dec_ref(v_input_746_);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_844_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_844_, 0, v_imports_763_);
lean_ctor_set(v___x_844_, 1, v_pos_764_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3, v_badModifier_765_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3 + 1, v_isModule_767_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3 + 2, v_isMeta_768_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3 + 3, v_isExported_769_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3 + 4, v_importAll_770_);
return v___x_844_;
}
else
{
v___y_811_ = v___x_842_;
goto v___jp_810_;
}
}
else
{
v___y_811_ = v___x_841_;
goto v___jp_810_;
}
}
v___jp_845_:
{
uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 97;
v___x_847_ = lean_uint32_dec_le(v___x_846_, v_curr_775_);
if (v___x_847_ == 0)
{
goto v___jp_839_;
}
else
{
uint32_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = 122;
v___x_849_ = lean_uint32_dec_le(v_curr_775_, v___x_848_);
if (v___x_849_ == 0)
{
goto v___jp_839_;
}
else
{
v___y_811_ = v___x_849_;
goto v___jp_810_;
}
}
}
}
}
else
{
lean_object* v___x_913_; 
lean_dec(v_module_748_);
lean_dec_ref(v_finalize_747_);
lean_dec_ref(v_input_746_);
v___x_913_ = l_Lean_ParseImports_State_mkEOIError(v_s_749_);
return v___x_913_;
}
v___jp_750_:
{
lean_object* v___x_760_; lean_object* v_s_761_; 
v___x_760_ = lean_string_utf8_next(v_input_746_, v___y_754_);
lean_dec(v___y_754_);
v_s_761_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_761_, 0, v___y_753_);
lean_ctor_set(v_s_761_, 1, v___x_760_);
lean_ctor_set(v_s_761_, 2, v___y_756_);
lean_ctor_set_uint8(v_s_761_, sizeof(void*)*3, v___y_759_);
lean_ctor_set_uint8(v_s_761_, sizeof(void*)*3 + 1, v___y_751_);
lean_ctor_set_uint8(v_s_761_, sizeof(void*)*3 + 2, v___y_758_);
lean_ctor_set_uint8(v_s_761_, sizeof(void*)*3 + 3, v___y_755_);
lean_ctor_set_uint8(v_s_761_, sizeof(void*)*3 + 4, v___y_757_);
v_module_748_ = v___y_752_;
v_s_749_ = v_s_761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_914_, lean_object* v_input_915_, lean_object* v_s_916_){
_start:
{
uint8_t v_isMeta_917_; uint8_t v_isExported_918_; uint8_t v_importAll_919_; lean_object* v_imp_920_; lean_object* v___x_921_; lean_object* v_s_922_; lean_object* v_imports_923_; lean_object* v_pos_924_; uint8_t v_badModifier_925_; lean_object* v_error_x3f_926_; uint8_t v_isModule_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_939_; 
v_isMeta_917_ = lean_ctor_get_uint8(v_s_916_, sizeof(void*)*3 + 2);
v_isExported_918_ = lean_ctor_get_uint8(v_s_916_, sizeof(void*)*3 + 3);
v_importAll_919_ = lean_ctor_get_uint8(v_s_916_, sizeof(void*)*3 + 4);
v_imp_920_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_920_, 0, v_module_914_);
lean_ctor_set_uint8(v_imp_920_, sizeof(void*)*1, v_importAll_919_);
lean_ctor_set_uint8(v_imp_920_, sizeof(void*)*1 + 1, v_isExported_918_);
lean_ctor_set_uint8(v_imp_920_, sizeof(void*)*1 + 2, v_isMeta_917_);
v___x_921_ = l_Lean_ParseImports_State_pushImport(v_imp_920_, v_s_916_);
v_s_922_ = l_Lean_ParseImports_whitespace(v_input_915_, v___x_921_);
v_imports_923_ = lean_ctor_get(v_s_922_, 0);
v_pos_924_ = lean_ctor_get(v_s_922_, 1);
v_badModifier_925_ = lean_ctor_get_uint8(v_s_922_, sizeof(void*)*3);
v_error_x3f_926_ = lean_ctor_get(v_s_922_, 2);
v_isModule_927_ = lean_ctor_get_uint8(v_s_922_, sizeof(void*)*3 + 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_s_922_);
if (v_isSharedCheck_939_ == 0)
{
v___x_929_ = v_s_922_;
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_error_x3f_926_);
lean_inc(v_pos_924_);
lean_inc(v_imports_923_);
lean_dec(v_s_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v___x_931_; 
v___x_931_ = 0;
if (v_isModule_927_ == 0)
{
uint8_t v___x_932_; lean_object* v___x_934_; 
v___x_932_ = 1;
if (v_isShared_930_ == 0)
{
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_imports_923_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_pos_924_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_error_x3f_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_935_, sizeof(void*)*3, v_badModifier_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_935_, sizeof(void*)*3 + 1, v_isModule_927_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 2, v___x_931_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 3, v___x_932_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 4, v___x_931_);
return v___x_934_;
}
}
else
{
lean_object* v___x_937_; 
if (v_isShared_930_ == 0)
{
v___x_937_ = v___x_929_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_imports_923_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_pos_924_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_error_x3f_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_938_, sizeof(void*)*3, v_badModifier_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_938_, sizeof(void*)*3 + 1, v_isModule_927_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*3 + 2, v___x_931_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*3 + 3, v___x_931_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*3 + 4, v___x_931_);
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_940_, lean_object* v_input_941_, lean_object* v_s_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_940_, v_input_941_, v_s_942_);
lean_dec_ref(v_input_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_finalize_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_finalize_947_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_948_ = lean_box(0);
v___x_949_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_945_, v_finalize_947_, v___x_948_, v_s_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_950_, lean_object* v_input_951_, lean_object* v_s_952_){
_start:
{
lean_object* v_pos_953_; lean_object* v_s_954_; lean_object* v_error_x3f_955_; 
v_pos_953_ = lean_ctor_get(v_s_952_, 1);
lean_inc(v_pos_953_);
v_s_954_ = lean_apply_2(v_p_950_, v_input_951_, v_s_952_);
v_error_x3f_955_ = lean_ctor_get(v_s_954_, 2);
lean_inc(v_error_x3f_955_);
if (lean_obj_tag(v_error_x3f_955_) == 1)
{
lean_object* v_imports_956_; uint8_t v_badModifier_957_; uint8_t v_isModule_958_; uint8_t v_isMeta_959_; uint8_t v_isExported_960_; uint8_t v_importAll_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_imports_956_ = lean_ctor_get(v_s_954_, 0);
v_badModifier_957_ = lean_ctor_get_uint8(v_s_954_, sizeof(void*)*3);
v_isModule_958_ = lean_ctor_get_uint8(v_s_954_, sizeof(void*)*3 + 1);
v_isMeta_959_ = lean_ctor_get_uint8(v_s_954_, sizeof(void*)*3 + 2);
v_isExported_960_ = lean_ctor_get_uint8(v_s_954_, sizeof(void*)*3 + 3);
v_importAll_961_ = lean_ctor_get_uint8(v_s_954_, sizeof(void*)*3 + 4);
v_isSharedCheck_968_ = !lean_is_exclusive(v_s_954_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v_s_954_, 2);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_s_954_, 1);
lean_dec(v_unused_970_);
v___x_963_ = v_s_954_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_imports_956_);
lean_dec(v_s_954_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_pos_953_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_imports_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_pos_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_error_x3f_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_badModifier_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 1, v_isModule_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 2, v_isMeta_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 3, v_isExported_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3 + 4, v_importAll_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
lean_dec(v_error_x3f_955_);
lean_dec(v_pos_953_);
return v_s_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_974_, lean_object* v_input_975_, lean_object* v_s_976_){
_start:
{
lean_object* v_pos_977_; lean_object* v_s_978_; lean_object* v_error_x3f_979_; 
v_pos_977_ = lean_ctor_get(v_s_976_, 1);
lean_inc(v_pos_977_);
lean_inc_ref(v_p_974_);
lean_inc_ref(v_input_975_);
v_s_978_ = lean_apply_2(v_p_974_, v_input_975_, v_s_976_);
v_error_x3f_979_ = lean_ctor_get(v_s_978_, 2);
lean_inc(v_error_x3f_979_);
if (lean_obj_tag(v_error_x3f_979_) == 1)
{
lean_object* v_imports_980_; lean_object* v_pos_981_; uint8_t v_isModule_982_; uint8_t v_isMeta_983_; uint8_t v_isExported_984_; uint8_t v_importAll_985_; uint8_t v_decide_986_; 
lean_dec_ref_known(v_error_x3f_979_, 1);
lean_dec_ref(v_input_975_);
lean_dec_ref(v_p_974_);
v_imports_980_ = lean_ctor_get(v_s_978_, 0);
lean_inc_ref(v_imports_980_);
v_pos_981_ = lean_ctor_get(v_s_978_, 1);
lean_inc(v_pos_981_);
v_isModule_982_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 1);
v_isMeta_983_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 2);
v_isExported_984_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 3);
v_importAll_985_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 4);
v_decide_986_ = lean_nat_dec_eq(v_pos_981_, v_pos_977_);
lean_dec(v_pos_977_);
if (v_decide_986_ == 0)
{
lean_dec(v_pos_981_);
lean_dec_ref(v_imports_980_);
return v_s_978_;
}
else
{
lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_996_ = lean_ctor_get(v_s_978_, 2);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_s_978_, 1);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_s_978_, 0);
lean_dec(v_unused_998_);
v___x_988_ = v_s_978_;
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
else
{
lean_dec(v_s_978_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = 0;
v___x_991_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 2, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_imports_980_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_pos_981_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v___x_991_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3 + 1, v_isModule_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3 + 2, v_isMeta_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3 + 3, v_isExported_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3 + 4, v_importAll_985_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*3, v___x_990_);
return v___x_993_;
}
}
}
}
else
{
uint8_t v_badModifier_999_; 
lean_dec(v_error_x3f_979_);
v_badModifier_999_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3);
if (v_badModifier_999_ == 0)
{
lean_dec(v_pos_977_);
v_s_976_ = v_s_978_;
goto _start;
}
else
{
lean_object* v_imports_1001_; uint8_t v_isModule_1002_; uint8_t v_isMeta_1003_; uint8_t v_isExported_1004_; uint8_t v_importAll_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_input_975_);
lean_dec_ref(v_p_974_);
v_imports_1001_ = lean_ctor_get(v_s_978_, 0);
v_isModule_1002_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 1);
v_isMeta_1003_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 2);
v_isExported_1004_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 3);
v_importAll_1005_ = lean_ctor_get_uint8(v_s_978_, sizeof(void*)*3 + 4);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1015_ = lean_ctor_get(v_s_978_, 2);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_s_978_, 1);
lean_dec(v_unused_1016_);
v___x_1007_ = v_s_978_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_imports_1001_);
lean_dec(v_s_978_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = 0;
v___x_1010_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 2, v___x_1010_);
lean_ctor_set(v___x_1007_, 1, v_pos_977_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_imports_1001_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_pos_977_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*3 + 1, v_isModule_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*3 + 2, v_isMeta_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*3 + 3, v_isExported_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*3 + 4, v_importAll_1005_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*3, v___x_1009_);
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1017_, lean_object* v_s_1018_){
_start:
{
if (v_isModule_1017_ == 0)
{
lean_object* v_imports_1019_; lean_object* v_pos_1020_; uint8_t v_badModifier_1021_; lean_object* v_error_x3f_1022_; uint8_t v_isMeta_1023_; uint8_t v_importAll_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
v_imports_1019_ = lean_ctor_get(v_s_1018_, 0);
v_pos_1020_ = lean_ctor_get(v_s_1018_, 1);
v_badModifier_1021_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3);
v_error_x3f_1022_ = lean_ctor_get(v_s_1018_, 2);
v_isMeta_1023_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3 + 2);
v_importAll_1024_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3 + 4);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1026_ = v_s_1018_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_error_x3f_1022_);
lean_inc(v_pos_1020_);
lean_inc(v_imports_1019_);
lean_dec(v_s_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = 1;
if (v_isShared_1027_ == 0)
{
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_imports_1019_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_pos_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_error_x3f_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3, v_badModifier_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 2, v_isMeta_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3 + 4, v_importAll_1024_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3 + 1, v_isModule_1017_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3 + 3, v___x_1028_);
return v___x_1030_;
}
}
}
else
{
lean_object* v_imports_1033_; lean_object* v_pos_1034_; uint8_t v_badModifier_1035_; lean_object* v_error_x3f_1036_; uint8_t v_isMeta_1037_; uint8_t v_importAll_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_imports_1033_ = lean_ctor_get(v_s_1018_, 0);
v_pos_1034_ = lean_ctor_get(v_s_1018_, 1);
v_badModifier_1035_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3);
v_error_x3f_1036_ = lean_ctor_get(v_s_1018_, 2);
v_isMeta_1037_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3 + 2);
v_importAll_1038_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*3 + 4);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v_s_1018_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_error_x3f_1036_);
lean_inc(v_pos_1034_);
lean_inc(v_imports_1033_);
lean_dec(v_s_1018_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
uint8_t v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = 0;
if (v_isShared_1041_ == 0)
{
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_imports_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_pos_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_error_x3f_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*3, v_badModifier_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*3 + 2, v_isMeta_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*3 + 4, v_importAll_1038_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*3 + 1, v_isModule_1017_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*3 + 3, v___x_1042_);
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* v_isModule_1047_, lean_object* v_s_1048_){
_start:
{
uint8_t v_isModule_boxed_1049_; lean_object* v_res_1050_; 
v_isModule_boxed_1049_ = lean_unbox(v_isModule_1047_);
v_res_1050_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_1049_, v_s_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1051_, lean_object* v_x_1052_, lean_object* v_s_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1051_, v_s_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1055_, lean_object* v_x_1056_, lean_object* v_s_1057_){
_start:
{
uint8_t v_isModule_boxed_1058_; lean_object* v_res_1059_; 
v_isModule_boxed_1058_ = lean_unbox(v_isModule_1055_);
v_res_1059_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1058_, v_x_1056_, v_s_1057_);
lean_dec_ref(v_x_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1060_){
_start:
{
lean_object* v_imports_1061_; lean_object* v_pos_1062_; uint8_t v_badModifier_1063_; lean_object* v_error_x3f_1064_; uint8_t v_isModule_1065_; uint8_t v_isMeta_1066_; uint8_t v_isExported_1067_; uint8_t v_importAll_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_imports_1061_ = lean_ctor_get(v_s_1060_, 0);
v_pos_1062_ = lean_ctor_get(v_s_1060_, 1);
v_badModifier_1063_ = lean_ctor_get_uint8(v_s_1060_, sizeof(void*)*3);
v_error_x3f_1064_ = lean_ctor_get(v_s_1060_, 2);
v_isModule_1065_ = lean_ctor_get_uint8(v_s_1060_, sizeof(void*)*3 + 1);
v_isMeta_1066_ = lean_ctor_get_uint8(v_s_1060_, sizeof(void*)*3 + 2);
v_isExported_1067_ = lean_ctor_get_uint8(v_s_1060_, sizeof(void*)*3 + 3);
v_importAll_1068_ = lean_ctor_get_uint8(v_s_1060_, sizeof(void*)*3 + 4);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_s_1060_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v_s_1060_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_error_x3f_1064_);
lean_inc(v_pos_1062_);
lean_inc(v_imports_1061_);
lean_dec(v_s_1060_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; 
v___x_1072_ = 1;
if (v_isModule_1065_ == 0)
{
lean_object* v___x_1074_; 
if (v_isShared_1071_ == 0)
{
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_imports_1061_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_pos_1062_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_error_x3f_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3 + 1, v_isModule_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3 + 2, v_isMeta_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3 + 3, v_isExported_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3 + 4, v_importAll_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3, v___x_1072_);
return v___x_1074_;
}
}
else
{
lean_object* v___x_1077_; 
if (v_isShared_1071_ == 0)
{
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_imports_1061_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_pos_1062_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_error_x3f_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*3, v_badModifier_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*3 + 1, v_isModule_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*3 + 3, v_isExported_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1078_, sizeof(void*)*3 + 4, v_importAll_1068_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*3 + 2, v___x_1072_);
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1080_, lean_object* v_s_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_ParseImports_setMeta___redArg(v_s_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1083_, lean_object* v_s_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_ParseImports_setMeta(v_x_1083_, v_s_1084_);
lean_dec_ref(v_x_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1086_){
_start:
{
lean_object* v_imports_1087_; lean_object* v_pos_1088_; uint8_t v_badModifier_1089_; lean_object* v_error_x3f_1090_; uint8_t v_isModule_1091_; uint8_t v_isMeta_1092_; uint8_t v_isExported_1093_; uint8_t v_importAll_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1105_; 
v_imports_1087_ = lean_ctor_get(v_s_1086_, 0);
v_pos_1088_ = lean_ctor_get(v_s_1086_, 1);
v_badModifier_1089_ = lean_ctor_get_uint8(v_s_1086_, sizeof(void*)*3);
v_error_x3f_1090_ = lean_ctor_get(v_s_1086_, 2);
v_isModule_1091_ = lean_ctor_get_uint8(v_s_1086_, sizeof(void*)*3 + 1);
v_isMeta_1092_ = lean_ctor_get_uint8(v_s_1086_, sizeof(void*)*3 + 2);
v_isExported_1093_ = lean_ctor_get_uint8(v_s_1086_, sizeof(void*)*3 + 3);
v_importAll_1094_ = lean_ctor_get_uint8(v_s_1086_, sizeof(void*)*3 + 4);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_s_1086_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1096_ = v_s_1086_;
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_error_x3f_1090_);
lean_inc(v_pos_1088_);
lean_inc(v_imports_1087_);
lean_dec(v_s_1086_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = 1;
if (v_isModule_1091_ == 0)
{
lean_object* v___x_1100_; 
if (v_isShared_1097_ == 0)
{
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_imports_1087_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_pos_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_error_x3f_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*3 + 1, v_isModule_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*3 + 2, v_isMeta_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*3 + 3, v_isExported_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*3 + 4, v_importAll_1094_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*3, v___x_1098_);
return v___x_1100_;
}
}
else
{
lean_object* v___x_1103_; 
if (v_isShared_1097_ == 0)
{
v___x_1103_ = v___x_1096_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_imports_1087_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_pos_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_error_x3f_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*3, v_badModifier_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*3 + 1, v_isModule_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*3 + 2, v_isMeta_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*3 + 4, v_importAll_1094_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*3 + 3, v___x_1098_);
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1106_, lean_object* v_s_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_ParseImports_setExported___redArg(v_s_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_ParseImports_setExported(v_x_1109_, v_s_1110_);
lean_dec_ref(v_x_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1112_){
_start:
{
lean_object* v_imports_1113_; lean_object* v_pos_1114_; uint8_t v_badModifier_1115_; lean_object* v_error_x3f_1116_; uint8_t v_isModule_1117_; uint8_t v_isMeta_1118_; uint8_t v_isExported_1119_; uint8_t v_importAll_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1131_; 
v_imports_1113_ = lean_ctor_get(v_s_1112_, 0);
v_pos_1114_ = lean_ctor_get(v_s_1112_, 1);
v_badModifier_1115_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*3);
v_error_x3f_1116_ = lean_ctor_get(v_s_1112_, 2);
v_isModule_1117_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*3 + 1);
v_isMeta_1118_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*3 + 2);
v_isExported_1119_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*3 + 3);
v_importAll_1120_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*3 + 4);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_s_1112_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1122_ = v_s_1112_;
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_error_x3f_1116_);
lean_inc(v_pos_1114_);
lean_inc(v_imports_1113_);
lean_dec(v_s_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; 
v___x_1124_ = 1;
if (v_isModule_1117_ == 0)
{
lean_object* v___x_1126_; 
if (v_isShared_1123_ == 0)
{
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_imports_1113_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_pos_1114_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_error_x3f_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 1, v_isModule_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 2, v_isMeta_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 3, v_isExported_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 4, v_importAll_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*3, v___x_1124_);
return v___x_1126_;
}
}
else
{
lean_object* v___x_1129_; 
if (v_isShared_1123_ == 0)
{
v___x_1129_ = v___x_1122_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_imports_1113_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_pos_1114_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_error_x3f_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*3, v_badModifier_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*3 + 1, v_isModule_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*3 + 2, v_isMeta_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*3 + 3, v_isExported_1119_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*3 + 4, v___x_1124_);
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1132_, lean_object* v_s_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1135_, lean_object* v_s_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_ParseImports_setImportAll(v_x_1135_, v_s_1136_);
lean_dec_ref(v_x_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1141_, lean_object* v_input_1142_, lean_object* v_s_1143_, lean_object* v_i_1144_, lean_object* v_j_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_string_utf8_at_end(v_k_1141_, v_i_1144_);
if (v___x_1146_ == 0)
{
uint8_t v___x_1147_; lean_object* v_s_1149_; uint8_t v___x_1155_; 
v___x_1147_ = 1;
v___x_1155_ = lean_string_utf8_at_end(v_input_1142_, v_j_1145_);
if (v___x_1155_ == 0)
{
uint32_t v_curr_u2081_1156_; uint32_t v_curr_u2082_1157_; uint8_t v___x_1158_; 
v_curr_u2081_1156_ = lean_string_utf8_get_fast(v_k_1141_, v_i_1144_);
v_curr_u2082_1157_ = lean_string_utf8_get_fast(v_input_1142_, v_j_1145_);
v___x_1158_ = lean_uint32_dec_eq(v_curr_u2081_1156_, v_curr_u2082_1157_);
if (v___x_1158_ == 0)
{
lean_dec(v_j_1145_);
lean_dec(v_i_1144_);
v_s_1149_ = v_s_1143_;
goto v___jp_1148_;
}
else
{
if (v___x_1155_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_string_utf8_next_fast(v_k_1141_, v_i_1144_);
lean_dec(v_i_1144_);
v___x_1160_ = lean_string_utf8_next_fast(v_input_1142_, v_j_1145_);
lean_dec(v_j_1145_);
v_i_1144_ = v___x_1159_;
v_j_1145_ = v___x_1160_;
goto _start;
}
else
{
lean_dec(v_j_1145_);
lean_dec(v_i_1144_);
v_s_1149_ = v_s_1143_;
goto v___jp_1148_;
}
}
}
else
{
lean_dec(v_j_1145_);
lean_dec(v_i_1144_);
v_s_1149_ = v_s_1143_;
goto v___jp_1148_;
}
v___jp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1151_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*1, v___x_1146_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*1 + 1, v___x_1147_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*1 + 2, v___x_1147_);
v___x_1152_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*1, v___x_1146_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*1 + 1, v___x_1147_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*1 + 2, v___x_1146_);
v___x_1153_ = l_Lean_ParseImports_State_pushImport(v___x_1152_, v_s_1149_);
v___x_1154_ = l_Lean_ParseImports_State_pushImport(v___x_1151_, v___x_1153_);
return v___x_1154_;
}
}
else
{
lean_object* v_imports_1162_; uint8_t v_badModifier_1163_; lean_object* v_error_x3f_1164_; uint8_t v_isModule_1165_; uint8_t v_isMeta_1166_; uint8_t v_isExported_1167_; uint8_t v_importAll_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_i_1144_);
v_imports_1162_ = lean_ctor_get(v_s_1143_, 0);
v_badModifier_1163_ = lean_ctor_get_uint8(v_s_1143_, sizeof(void*)*3);
v_error_x3f_1164_ = lean_ctor_get(v_s_1143_, 2);
v_isModule_1165_ = lean_ctor_get_uint8(v_s_1143_, sizeof(void*)*3 + 1);
v_isMeta_1166_ = lean_ctor_get_uint8(v_s_1143_, sizeof(void*)*3 + 2);
v_isExported_1167_ = lean_ctor_get_uint8(v_s_1143_, sizeof(void*)*3 + 3);
v_importAll_1168_ = lean_ctor_get_uint8(v_s_1143_, sizeof(void*)*3 + 4);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_s_1143_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v_s_1143_, 1);
lean_dec(v_unused_1177_);
v___x_1170_ = v_s_1143_;
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_error_x3f_1164_);
lean_inc(v_imports_1162_);
lean_dec(v_s_1143_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_j_1145_);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_imports_1162_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_j_1145_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_error_x3f_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*3, v_badModifier_1163_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*3 + 1, v_isModule_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*3 + 2, v_isMeta_1166_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*3 + 3, v_isExported_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*3 + 4, v_importAll_1168_);
v___x_1173_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_ParseImports_whitespace(v_input_1142_, v___x_1173_);
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1178_, lean_object* v_input_1179_, lean_object* v_s_1180_, lean_object* v_i_1181_, lean_object* v_j_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1178_, v_input_1179_, v_s_1180_, v_i_1181_, v_j_1182_);
lean_dec_ref(v_input_1179_);
lean_dec_ref(v_k_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1187_, lean_object* v_input_1188_, lean_object* v_s_1189_, lean_object* v_i_1190_, lean_object* v_j_1191_){
_start:
{
lean_object* v_s_1193_; uint8_t v___x_1210_; 
v___x_1210_ = lean_string_utf8_at_end(v_k_1187_, v_i_1190_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_string_utf8_at_end(v_input_1188_, v_j_1191_);
if (v___x_1211_ == 0)
{
uint32_t v_curr_u2081_1212_; uint32_t v_curr_u2082_1213_; uint8_t v___x_1214_; 
v_curr_u2081_1212_ = lean_string_utf8_get_fast(v_k_1187_, v_i_1190_);
v_curr_u2082_1213_ = lean_string_utf8_get_fast(v_input_1188_, v_j_1191_);
v___x_1214_ = lean_uint32_dec_eq(v_curr_u2081_1212_, v_curr_u2082_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_j_1191_);
lean_dec(v_i_1190_);
v_s_1193_ = v_s_1189_;
goto v___jp_1192_;
}
else
{
if (v___x_1211_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_string_utf8_next_fast(v_k_1187_, v_i_1190_);
lean_dec(v_i_1190_);
v___x_1216_ = lean_string_utf8_next_fast(v_input_1188_, v_j_1191_);
lean_dec(v_j_1191_);
v_i_1190_ = v___x_1215_;
v_j_1191_ = v___x_1216_;
goto _start;
}
else
{
lean_dec(v_j_1191_);
lean_dec(v_i_1190_);
v_s_1193_ = v_s_1189_;
goto v___jp_1192_;
}
}
}
else
{
lean_dec(v_j_1191_);
lean_dec(v_i_1190_);
v_s_1193_ = v_s_1189_;
goto v___jp_1192_;
}
}
else
{
lean_object* v_imports_1218_; uint8_t v_badModifier_1219_; lean_object* v_error_x3f_1220_; uint8_t v_isModule_1221_; uint8_t v_isMeta_1222_; uint8_t v_isExported_1223_; uint8_t v_importAll_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_i_1190_);
v_imports_1218_ = lean_ctor_get(v_s_1189_, 0);
v_badModifier_1219_ = lean_ctor_get_uint8(v_s_1189_, sizeof(void*)*3);
v_error_x3f_1220_ = lean_ctor_get(v_s_1189_, 2);
v_isModule_1221_ = lean_ctor_get_uint8(v_s_1189_, sizeof(void*)*3 + 1);
v_isMeta_1222_ = lean_ctor_get_uint8(v_s_1189_, sizeof(void*)*3 + 2);
v_isExported_1223_ = lean_ctor_get_uint8(v_s_1189_, sizeof(void*)*3 + 3);
v_importAll_1224_ = lean_ctor_get_uint8(v_s_1189_, sizeof(void*)*3 + 4);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_s_1189_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_s_1189_, 1);
lean_dec(v_unused_1233_);
v___x_1226_ = v_s_1189_;
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_error_x3f_1220_);
lean_inc(v_imports_1218_);
lean_dec(v_s_1189_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v_j_1191_);
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_imports_1218_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_j_1191_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_error_x3f_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3, v_badModifier_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3 + 1, v_isModule_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3 + 2, v_isMeta_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3 + 3, v_isExported_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3 + 4, v_importAll_1224_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_ParseImports_whitespace(v_input_1188_, v___x_1229_);
return v___x_1230_;
}
}
}
v___jp_1192_:
{
lean_object* v_imports_1194_; lean_object* v_pos_1195_; uint8_t v_badModifier_1196_; uint8_t v_isModule_1197_; uint8_t v_isMeta_1198_; uint8_t v_isExported_1199_; uint8_t v_importAll_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_imports_1194_ = lean_ctor_get(v_s_1193_, 0);
v_pos_1195_ = lean_ctor_get(v_s_1193_, 1);
v_badModifier_1196_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*3);
v_isModule_1197_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*3 + 1);
v_isMeta_1198_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*3 + 2);
v_isExported_1199_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*3 + 3);
v_importAll_1200_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*3 + 4);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_s_1193_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_s_1193_, 2);
lean_dec(v_unused_1209_);
v___x_1202_ = v_s_1193_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_pos_1195_);
lean_inc(v_imports_1194_);
lean_dec(v_s_1193_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 2, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_imports_1194_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_pos_1195_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v___x_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*3, v_badModifier_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*3 + 1, v_isModule_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*3 + 2, v_isMeta_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*3 + 3, v_isExported_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*3 + 4, v_importAll_1200_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1234_, lean_object* v_input_1235_, lean_object* v_s_1236_, lean_object* v_i_1237_, lean_object* v_j_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1234_, v_input_1235_, v_s_1236_, v_i_1237_, v_j_1238_);
lean_dec_ref(v_input_1235_);
lean_dec_ref(v_k_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1240_, lean_object* v_input_1241_, lean_object* v_s_1242_, lean_object* v_i_1243_, lean_object* v_j_1244_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_string_utf8_at_end(v_k_1240_, v_i_1243_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_string_utf8_at_end(v_input_1241_, v_j_1244_);
if (v___x_1246_ == 0)
{
uint32_t v_curr_u2081_1247_; uint32_t v_curr_u2082_1248_; uint8_t v___x_1249_; 
v_curr_u2081_1247_ = lean_string_utf8_get_fast(v_k_1240_, v_i_1243_);
v_curr_u2082_1248_ = lean_string_utf8_get_fast(v_input_1241_, v_j_1244_);
v___x_1249_ = lean_uint32_dec_eq(v_curr_u2081_1247_, v_curr_u2082_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v_j_1244_);
lean_dec(v_i_1243_);
return v_s_1242_;
}
else
{
if (v___x_1246_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_string_utf8_next_fast(v_k_1240_, v_i_1243_);
lean_dec(v_i_1243_);
v___x_1251_ = lean_string_utf8_next_fast(v_input_1241_, v_j_1244_);
lean_dec(v_j_1244_);
v_i_1243_ = v___x_1250_;
v_j_1244_ = v___x_1251_;
goto _start;
}
else
{
lean_dec(v_j_1244_);
lean_dec(v_i_1243_);
return v_s_1242_;
}
}
}
else
{
lean_dec(v_j_1244_);
lean_dec(v_i_1243_);
return v_s_1242_;
}
}
else
{
lean_object* v_imports_1253_; uint8_t v_badModifier_1254_; lean_object* v_error_x3f_1255_; uint8_t v_isModule_1256_; uint8_t v_isMeta_1257_; uint8_t v_isExported_1258_; uint8_t v_importAll_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_i_1243_);
v_imports_1253_ = lean_ctor_get(v_s_1242_, 0);
v_badModifier_1254_ = lean_ctor_get_uint8(v_s_1242_, sizeof(void*)*3);
v_error_x3f_1255_ = lean_ctor_get(v_s_1242_, 2);
v_isModule_1256_ = lean_ctor_get_uint8(v_s_1242_, sizeof(void*)*3 + 1);
v_isMeta_1257_ = lean_ctor_get_uint8(v_s_1242_, sizeof(void*)*3 + 2);
v_isExported_1258_ = lean_ctor_get_uint8(v_s_1242_, sizeof(void*)*3 + 3);
v_importAll_1259_ = lean_ctor_get_uint8(v_s_1242_, sizeof(void*)*3 + 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_s_1242_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_s_1242_, 1);
lean_dec(v_unused_1269_);
v___x_1261_ = v_s_1242_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_error_x3f_1255_);
lean_inc(v_imports_1253_);
lean_dec(v_s_1242_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_j_1244_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_imports_1253_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_j_1244_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_error_x3f_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3, v_badModifier_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 1, v_isModule_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 2, v_isMeta_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 3, v_isExported_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 4, v_importAll_1259_);
v___x_1264_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = l_Lean_ParseImports_whitespace(v_input_1241_, v___x_1264_);
v___x_1266_ = l_Lean_ParseImports_setImportAll___redArg(v___x_1265_);
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* v_k_1270_, lean_object* v_input_1271_, lean_object* v_s_1272_, lean_object* v_i_1273_, lean_object* v_j_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_1270_, v_input_1271_, v_s_1272_, v_i_1273_, v_j_1274_);
lean_dec_ref(v_input_1271_);
lean_dec_ref(v_k_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* v_k_1276_, lean_object* v_input_1277_, lean_object* v_s_1278_, lean_object* v_i_1279_, lean_object* v_j_1280_){
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
uint32_t v_curr_u2081_1283_; uint32_t v_curr_u2082_1284_; uint8_t v___x_1285_; 
v_curr_u2081_1283_ = lean_string_utf8_get_fast(v_k_1276_, v_i_1279_);
v_curr_u2082_1284_ = lean_string_utf8_get_fast(v_input_1277_, v_j_1280_);
v___x_1285_ = lean_uint32_dec_eq(v_curr_u2081_1283_, v_curr_u2082_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_j_1280_);
lean_dec(v_i_1279_);
return v_s_1278_;
}
else
{
if (v___x_1282_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_string_utf8_next_fast(v_k_1276_, v_i_1279_);
lean_dec(v_i_1279_);
v___x_1287_ = lean_string_utf8_next_fast(v_input_1277_, v_j_1280_);
lean_dec(v_j_1280_);
v_i_1279_ = v___x_1286_;
v_j_1280_ = v___x_1287_;
goto _start;
}
else
{
lean_dec(v_j_1280_);
lean_dec(v_i_1279_);
return v_s_1278_;
}
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
lean_object* v_imports_1289_; uint8_t v_badModifier_1290_; lean_object* v_error_x3f_1291_; uint8_t v_isModule_1292_; uint8_t v_isMeta_1293_; uint8_t v_isExported_1294_; uint8_t v_importAll_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_i_1279_);
v_imports_1289_ = lean_ctor_get(v_s_1278_, 0);
v_badModifier_1290_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3);
v_error_x3f_1291_ = lean_ctor_get(v_s_1278_, 2);
v_isModule_1292_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 1);
v_isMeta_1293_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 2);
v_isExported_1294_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 3);
v_importAll_1295_ = lean_ctor_get_uint8(v_s_1278_, sizeof(void*)*3 + 4);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_s_1278_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v_s_1278_, 1);
lean_dec(v_unused_1305_);
v___x_1297_ = v_s_1278_;
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_error_x3f_1291_);
lean_inc(v_imports_1289_);
lean_dec(v_s_1278_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v_j_1280_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_imports_1289_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_j_1280_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_error_x3f_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*3, v_badModifier_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*3 + 1, v_isModule_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*3 + 2, v_isMeta_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*3 + 3, v_isExported_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1303_, sizeof(void*)*3 + 4, v_importAll_1295_);
v___x_1300_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = l_Lean_ParseImports_whitespace(v_input_1277_, v___x_1300_);
v___x_1302_ = l_Lean_ParseImports_setExported___redArg(v___x_1301_);
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1306_, lean_object* v_input_1307_, lean_object* v_s_1308_, lean_object* v_i_1309_, lean_object* v_j_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1306_, v_input_1307_, v_s_1308_, v_i_1309_, v_j_1310_);
lean_dec_ref(v_input_1307_);
lean_dec_ref(v_k_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1312_, lean_object* v_input_1313_, lean_object* v_s_1314_, lean_object* v_i_1315_, lean_object* v_j_1316_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_string_utf8_at_end(v_k_1312_, v_i_1315_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_string_utf8_at_end(v_input_1313_, v_j_1316_);
if (v___x_1318_ == 0)
{
uint32_t v_curr_u2081_1319_; uint32_t v_curr_u2082_1320_; uint8_t v___x_1321_; 
v_curr_u2081_1319_ = lean_string_utf8_get_fast(v_k_1312_, v_i_1315_);
v_curr_u2082_1320_ = lean_string_utf8_get_fast(v_input_1313_, v_j_1316_);
v___x_1321_ = lean_uint32_dec_eq(v_curr_u2081_1319_, v_curr_u2082_1320_);
if (v___x_1321_ == 0)
{
lean_dec(v_j_1316_);
lean_dec(v_i_1315_);
return v_s_1314_;
}
else
{
if (v___x_1318_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_string_utf8_next_fast(v_k_1312_, v_i_1315_);
lean_dec(v_i_1315_);
v___x_1323_ = lean_string_utf8_next_fast(v_input_1313_, v_j_1316_);
lean_dec(v_j_1316_);
v_i_1315_ = v___x_1322_;
v_j_1316_ = v___x_1323_;
goto _start;
}
else
{
lean_dec(v_j_1316_);
lean_dec(v_i_1315_);
return v_s_1314_;
}
}
}
else
{
lean_dec(v_j_1316_);
lean_dec(v_i_1315_);
return v_s_1314_;
}
}
else
{
lean_object* v_imports_1325_; uint8_t v_badModifier_1326_; lean_object* v_error_x3f_1327_; uint8_t v_isModule_1328_; uint8_t v_isMeta_1329_; uint8_t v_isExported_1330_; uint8_t v_importAll_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_i_1315_);
v_imports_1325_ = lean_ctor_get(v_s_1314_, 0);
v_badModifier_1326_ = lean_ctor_get_uint8(v_s_1314_, sizeof(void*)*3);
v_error_x3f_1327_ = lean_ctor_get(v_s_1314_, 2);
v_isModule_1328_ = lean_ctor_get_uint8(v_s_1314_, sizeof(void*)*3 + 1);
v_isMeta_1329_ = lean_ctor_get_uint8(v_s_1314_, sizeof(void*)*3 + 2);
v_isExported_1330_ = lean_ctor_get_uint8(v_s_1314_, sizeof(void*)*3 + 3);
v_importAll_1331_ = lean_ctor_get_uint8(v_s_1314_, sizeof(void*)*3 + 4);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_s_1314_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_s_1314_, 1);
lean_dec(v_unused_1341_);
v___x_1333_ = v_s_1314_;
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_error_x3f_1327_);
lean_inc(v_imports_1325_);
lean_dec(v_s_1314_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v_j_1316_);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_imports_1325_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_j_1316_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_error_x3f_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*3, v_badModifier_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*3 + 1, v_isModule_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*3 + 2, v_isMeta_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*3 + 3, v_isExported_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*3 + 4, v_importAll_1331_);
v___x_1336_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = l_Lean_ParseImports_whitespace(v_input_1313_, v___x_1336_);
v___x_1338_ = l_Lean_ParseImports_setMeta___redArg(v___x_1337_);
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1342_, lean_object* v_input_1343_, lean_object* v_s_1344_, lean_object* v_i_1345_, lean_object* v_j_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1342_, v_input_1343_, v_s_1344_, v_i_1345_, v_j_1346_);
lean_dec_ref(v_input_1343_);
lean_dec_ref(v_k_1342_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1352_, lean_object* v_s_1353_){
_start:
{
lean_object* v_pos_1354_; lean_object* v___y_1356_; lean_object* v_imports_1357_; lean_object* v_pos_1358_; uint8_t v_isModule_1359_; uint8_t v_isMeta_1360_; uint8_t v_isExported_1361_; uint8_t v_importAll_1362_; lean_object* v___y_1368_; lean_object* v___y_1395_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_error_x3f_1427_; 
v_pos_1354_ = lean_ctor_get(v_s_1353_, 1);
lean_inc_n(v_pos_1354_, 2);
v___x_1424_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1424_, v_input_1352_, v_s_1353_, v___x_1425_, v_pos_1354_);
v_error_x3f_1427_ = lean_ctor_get(v___x_1426_, 2);
if (lean_obj_tag(v_error_x3f_1427_) == 1)
{
v___y_1395_ = v___x_1426_;
goto v___jp_1394_;
}
else
{
lean_object* v_pos_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_error_x3f_1431_; 
v_pos_1428_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_pos_1428_);
v___x_1429_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1430_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1429_, v_input_1352_, v___x_1426_, v___x_1425_, v_pos_1428_);
v_error_x3f_1431_ = lean_ctor_get(v___x_1430_, 2);
if (lean_obj_tag(v_error_x3f_1431_) == 1)
{
v___y_1395_ = v___x_1430_;
goto v___jp_1394_;
}
else
{
lean_object* v_pos_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_pos_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_pos_1432_);
v___x_1433_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1434_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1433_, v_input_1352_, v___x_1430_, v___x_1425_, v_pos_1432_);
v___y_1395_ = v___x_1434_;
goto v___jp_1394_;
}
}
v___jp_1355_:
{
uint8_t v_decide_1363_; 
v_decide_1363_ = lean_nat_dec_eq(v_pos_1358_, v_pos_1354_);
lean_dec(v_pos_1354_);
if (v_decide_1363_ == 0)
{
lean_dec(v_pos_1358_);
lean_dec_ref(v_imports_1357_);
return v___y_1356_;
}
else
{
uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v___y_1356_);
v___x_1364_ = 0;
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1366_, 0, v_imports_1357_);
lean_ctor_set(v___x_1366_, 1, v_pos_1358_);
lean_ctor_set(v___x_1366_, 2, v___x_1365_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3, v___x_1364_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 1, v_isModule_1359_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 2, v_isMeta_1360_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 3, v_isExported_1361_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 4, v_importAll_1362_);
return v___x_1366_;
}
}
v___jp_1367_:
{
lean_object* v_error_x3f_1369_; 
v_error_x3f_1369_ = lean_ctor_get(v___y_1368_, 2);
if (lean_obj_tag(v_error_x3f_1369_) == 1)
{
lean_object* v_imports_1370_; lean_object* v_pos_1371_; uint8_t v_isModule_1372_; uint8_t v_isMeta_1373_; uint8_t v_isExported_1374_; uint8_t v_importAll_1375_; 
lean_dec_ref(v_input_1352_);
v_imports_1370_ = lean_ctor_get(v___y_1368_, 0);
lean_inc_ref(v_imports_1370_);
v_pos_1371_ = lean_ctor_get(v___y_1368_, 1);
lean_inc(v_pos_1371_);
v_isModule_1372_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 1);
v_isMeta_1373_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 2);
v_isExported_1374_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 3);
v_importAll_1375_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 4);
v___y_1356_ = v___y_1368_;
v_imports_1357_ = v_imports_1370_;
v_pos_1358_ = v_pos_1371_;
v_isModule_1359_ = v_isModule_1372_;
v_isMeta_1360_ = v_isMeta_1373_;
v_isExported_1361_ = v_isExported_1374_;
v_importAll_1362_ = v_importAll_1375_;
goto v___jp_1355_;
}
else
{
uint8_t v_badModifier_1376_; 
v_badModifier_1376_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3);
if (v_badModifier_1376_ == 0)
{
lean_dec(v_pos_1354_);
v_s_1353_ = v___y_1368_;
goto _start;
}
else
{
lean_object* v_imports_1378_; uint8_t v_isModule_1379_; uint8_t v_isMeta_1380_; uint8_t v_isExported_1381_; uint8_t v_importAll_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_input_1352_);
v_imports_1378_ = lean_ctor_get(v___y_1368_, 0);
v_isModule_1379_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 1);
v_isMeta_1380_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 2);
v_isExported_1381_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 3);
v_importAll_1382_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*3 + 4);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___y_1368_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; 
v_unused_1392_ = lean_ctor_get(v___y_1368_, 2);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v___y_1368_, 1);
lean_dec(v_unused_1393_);
v___x_1384_ = v___y_1368_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_imports_1378_);
lean_dec(v___y_1368_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = 0;
v___x_1387_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 2, v___x_1387_);
lean_ctor_set(v___x_1384_, 1, v_pos_1354_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_imports_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_pos_1354_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*3 + 1, v_isModule_1379_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*3 + 2, v_isMeta_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*3 + 3, v_isExported_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*3 + 4, v_importAll_1382_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3, v___x_1386_);
return v___x_1389_;
}
}
}
}
}
v___jp_1394_:
{
lean_object* v_error_x3f_1396_; 
v_error_x3f_1396_ = lean_ctor_get(v___y_1395_, 2);
if (lean_obj_tag(v_error_x3f_1396_) == 1)
{
lean_object* v_imports_1397_; uint8_t v_badModifier_1398_; uint8_t v_isModule_1399_; uint8_t v_isMeta_1400_; uint8_t v_isExported_1401_; uint8_t v_importAll_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_inc_ref(v_error_x3f_1396_);
lean_dec_ref(v_input_1352_);
v_imports_1397_ = lean_ctor_get(v___y_1395_, 0);
v_badModifier_1398_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3);
v_isModule_1399_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 1);
v_isMeta_1400_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 2);
v_isExported_1401_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 3);
v_importAll_1402_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 4);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___y_1395_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1410_ = lean_ctor_get(v___y_1395_, 2);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v___y_1395_, 1);
lean_dec(v_unused_1411_);
v___x_1404_ = v___y_1395_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_imports_1397_);
lean_dec(v___y_1395_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
lean_inc(v_pos_1354_);
lean_inc_ref(v_imports_1397_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v_pos_1354_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_imports_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_pos_1354_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_error_x3f_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3, v_badModifier_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3 + 1, v_isModule_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3 + 2, v_isMeta_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3 + 3, v_isExported_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3 + 4, v_importAll_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_inc(v_pos_1354_);
v___y_1356_ = v___x_1407_;
v_imports_1357_ = v_imports_1397_;
v_pos_1358_ = v_pos_1354_;
v_isModule_1359_ = v_isModule_1399_;
v_isMeta_1360_ = v_isMeta_1400_;
v_isExported_1361_ = v_isExported_1401_;
v_importAll_1362_ = v_importAll_1402_;
goto v___jp_1355_;
}
}
}
else
{
if (lean_obj_tag(v_error_x3f_1396_) == 1)
{
lean_object* v_imports_1412_; lean_object* v_pos_1413_; uint8_t v_isModule_1414_; uint8_t v_isMeta_1415_; uint8_t v_isExported_1416_; uint8_t v_importAll_1417_; 
lean_dec_ref(v_input_1352_);
v_imports_1412_ = lean_ctor_get(v___y_1395_, 0);
lean_inc_ref(v_imports_1412_);
v_pos_1413_ = lean_ctor_get(v___y_1395_, 1);
lean_inc(v_pos_1413_);
v_isModule_1414_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 1);
v_isMeta_1415_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 2);
v_isExported_1416_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 3);
v_importAll_1417_ = lean_ctor_get_uint8(v___y_1395_, sizeof(void*)*3 + 4);
v___y_1356_ = v___y_1395_;
v_imports_1357_ = v_imports_1412_;
v_pos_1358_ = v_pos_1413_;
v_isModule_1359_ = v_isModule_1414_;
v_isMeta_1360_ = v_isMeta_1415_;
v_isExported_1361_ = v_isExported_1416_;
v_importAll_1362_ = v_importAll_1417_;
goto v___jp_1355_;
}
else
{
lean_object* v_pos_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_error_x3f_1422_; 
v_pos_1418_ = lean_ctor_get(v___y_1395_, 1);
lean_inc(v_pos_1418_);
v___x_1419_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1419_, v_input_1352_, v___y_1395_, v___x_1420_, v_pos_1418_);
v_error_x3f_1422_ = lean_ctor_get(v___x_1421_, 2);
if (lean_obj_tag(v_error_x3f_1422_) == 1)
{
v___y_1368_ = v___x_1421_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1423_; 
lean_inc_ref(v_input_1352_);
v___x_1423_ = l_Lean_ParseImports_moduleIdent(v_input_1352_, v___x_1421_);
v___y_1368_ = v___x_1423_;
goto v___jp_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1435_, lean_object* v_input_1436_, lean_object* v_s_1437_, lean_object* v_i_1438_, lean_object* v_j_1439_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_string_utf8_at_end(v_k_1435_, v_i_1438_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_string_utf8_at_end(v_input_1436_, v_j_1439_);
if (v___x_1441_ == 0)
{
uint32_t v_curr_u2081_1442_; uint32_t v_curr_u2082_1443_; uint8_t v___x_1444_; 
v_curr_u2081_1442_ = lean_string_utf8_get_fast(v_k_1435_, v_i_1438_);
v_curr_u2082_1443_ = lean_string_utf8_get_fast(v_input_1436_, v_j_1439_);
v___x_1444_ = lean_uint32_dec_eq(v_curr_u2081_1442_, v_curr_u2082_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_j_1439_);
lean_dec(v_i_1438_);
v___x_1445_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1440_, v_s_1437_);
return v___x_1445_;
}
else
{
if (v___x_1441_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_string_utf8_next_fast(v_k_1435_, v_i_1438_);
lean_dec(v_i_1438_);
v___x_1447_ = lean_string_utf8_next_fast(v_input_1436_, v_j_1439_);
lean_dec(v_j_1439_);
v_i_1438_ = v___x_1446_;
v_j_1439_ = v___x_1447_;
goto _start;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_j_1439_);
lean_dec(v_i_1438_);
v___x_1449_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1440_, v_s_1437_);
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_j_1439_);
lean_dec(v_i_1438_);
v___x_1450_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1440_, v_s_1437_);
return v___x_1450_;
}
}
else
{
lean_object* v_imports_1451_; uint8_t v_badModifier_1452_; lean_object* v_error_x3f_1453_; uint8_t v_isModule_1454_; uint8_t v_isMeta_1455_; uint8_t v_isExported_1456_; uint8_t v_importAll_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_i_1438_);
v_imports_1451_ = lean_ctor_get(v_s_1437_, 0);
v_badModifier_1452_ = lean_ctor_get_uint8(v_s_1437_, sizeof(void*)*3);
v_error_x3f_1453_ = lean_ctor_get(v_s_1437_, 2);
v_isModule_1454_ = lean_ctor_get_uint8(v_s_1437_, sizeof(void*)*3 + 1);
v_isMeta_1455_ = lean_ctor_get_uint8(v_s_1437_, sizeof(void*)*3 + 2);
v_isExported_1456_ = lean_ctor_get_uint8(v_s_1437_, sizeof(void*)*3 + 3);
v_importAll_1457_ = lean_ctor_get_uint8(v_s_1437_, sizeof(void*)*3 + 4);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_s_1437_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_s_1437_, 1);
lean_dec(v_unused_1467_);
v___x_1459_ = v_s_1437_;
v_isShared_1460_ = v_isSharedCheck_1466_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_error_x3f_1453_);
lean_inc(v_imports_1451_);
lean_dec(v_s_1437_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1466_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v_j_1439_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_imports_1451_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_j_1439_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_error_x3f_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3, v_badModifier_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3 + 1, v_isModule_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3 + 2, v_isMeta_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3 + 3, v_isExported_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*3 + 4, v_importAll_1457_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = l_Lean_ParseImports_whitespace(v_input_1436_, v___x_1462_);
v___x_1464_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1440_, v___x_1463_);
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1468_, lean_object* v_input_1469_, lean_object* v_s_1470_, lean_object* v_i_1471_, lean_object* v_j_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1468_, v_input_1469_, v_s_1470_, v_i_1471_, v_j_1472_);
lean_dec_ref(v_input_1469_);
lean_dec_ref(v_k_1468_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_pos_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_s_1481_; lean_object* v_error_x3f_1482_; 
v_pos_1478_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_pos_1478_);
v___x_1479_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1480_ = lean_unsigned_to_nat(0u);
v_s_1481_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1479_, v_a_1476_, v_a_1477_, v___x_1480_, v_pos_1478_);
v_error_x3f_1482_ = lean_ctor_get(v_s_1481_, 2);
if (lean_obj_tag(v_error_x3f_1482_) == 1)
{
lean_dec_ref(v_a_1476_);
return v_s_1481_;
}
else
{
lean_object* v_pos_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_error_x3f_1486_; 
v_pos_1483_ = lean_ctor_get(v_s_1481_, 1);
lean_inc(v_pos_1483_);
v___x_1484_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1485_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1484_, v_a_1476_, v_s_1481_, v___x_1480_, v_pos_1483_);
v_error_x3f_1486_ = lean_ctor_get(v___x_1485_, 2);
if (lean_obj_tag(v_error_x3f_1486_) == 1)
{
lean_dec_ref(v_a_1476_);
return v___x_1485_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1476_, v___x_1485_);
return v___x_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* v_input_1490_, lean_object* v_fileName_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_s_1495_; lean_object* v_error_x3f_1496_; 
v___x_1493_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1494_ = l_Lean_ParseImports_whitespace(v_input_1490_, v___x_1493_);
lean_inc_ref(v_input_1490_);
v_s_1495_ = l_Lean_ParseImports_main(v_input_1490_, v___x_1494_);
v_error_x3f_1496_ = lean_ctor_get(v_s_1495_, 2);
lean_inc(v_error_x3f_1496_);
if (lean_obj_tag(v_error_x3f_1496_) == 1)
{
lean_object* v_pos_1497_; lean_object* v_val_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1520_; 
v_pos_1497_ = lean_ctor_get(v_s_1495_, 1);
lean_inc(v_pos_1497_);
lean_dec_ref(v_s_1495_);
v_val_1498_ = lean_ctor_get(v_error_x3f_1496_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_error_x3f_1496_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1500_ = v_error_x3f_1496_;
v_isShared_1501_ = v_isSharedCheck_1520_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_val_1498_);
lean_dec(v_error_x3f_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1520_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_fileMap_1502_; lean_object* v_pos_1503_; lean_object* v_line_1504_; lean_object* v_column_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v_fileMap_1502_ = l_Lean_String_toFileMap(v_input_1490_);
v_pos_1503_ = l_Lean_FileMap_toPosition(v_fileMap_1502_, v_pos_1497_);
lean_dec(v_pos_1497_);
v_line_1504_ = lean_ctor_get(v_pos_1503_, 0);
lean_inc(v_line_1504_);
v_column_1505_ = lean_ctor_get(v_pos_1503_, 1);
lean_inc(v_column_1505_);
lean_dec_ref(v_pos_1503_);
v___x_1506_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1507_ = lean_string_append(v_fileName_1491_, v___x_1506_);
v___x_1508_ = l_Nat_reprFast(v_line_1504_);
v___x_1509_ = lean_string_append(v___x_1507_, v___x_1508_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = lean_string_append(v___x_1509_, v___x_1506_);
v___x_1511_ = l_Nat_reprFast(v_column_1505_);
v___x_1512_ = lean_string_append(v___x_1510_, v___x_1511_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_string_append(v___x_1514_, v_val_1498_);
lean_dec(v_val_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 18);
lean_ctor_set(v___x_1500_, 0, v___x_1515_);
v___x_1517_ = v___x_1500_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
else
{
lean_object* v_imports_1521_; uint8_t v_isModule_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_error_x3f_1496_);
lean_dec_ref(v_fileName_1491_);
lean_dec_ref(v_input_1490_);
v_imports_1521_ = lean_ctor_get(v_s_1495_, 0);
lean_inc_ref(v_imports_1521_);
v_isModule_1522_ = lean_ctor_get_uint8(v_s_1495_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1495_);
v___x_1523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1523_, 0, v_imports_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*1, v_isModule_1522_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1525_, lean_object* v_fileName_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_parseImports_x27(v_input_1525_, v_fileName_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1529_, lean_object* v_x_1530_){
_start:
{
if (lean_obj_tag(v_x_1530_) == 0)
{
lean_object* v___x_1531_; 
lean_dec_ref(v_k_1529_);
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
else
{
lean_object* v_val_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_val_1532_ = lean_ctor_get(v_x_1530_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v_x_1530_, 1);
v___x_1533_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1532_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_k_1529_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
if (lean_obj_tag(v_a_1537_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_array_to_list(v_a_1538_);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; lean_object* v_tail_1541_; lean_object* v___x_1542_; 
v_head_1540_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_head_1540_);
v_tail_1541_ = lean_ctor_get(v_a_1537_, 1);
lean_inc(v_tail_1541_);
lean_dec_ref_known(v_a_1537_, 2);
v___x_1542_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1538_, v_head_1540_);
v_a_1537_ = v_tail_1541_;
v_a_1538_ = v___x_1542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1544_, size_t v_i_1545_, lean_object* v_bs_1546_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_usize_dec_lt(v_i_1545_, v_sz_1544_);
if (v___x_1547_ == 0)
{
return v_bs_1546_;
}
else
{
lean_object* v_v_1548_; lean_object* v___x_1549_; lean_object* v_bs_x27_1550_; lean_object* v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v_v_1548_ = lean_array_uget(v_bs_1546_, v_i_1545_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v_bs_x27_1550_ = lean_array_uset(v_bs_1546_, v_i_1545_, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_v_1548_);
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_add(v_i_1545_, v___x_1552_);
v___x_1554_ = lean_array_uset(v_bs_x27_1550_, v_i_1545_, v___x_1551_);
v_i_1545_ = v___x_1553_;
v_bs_1546_ = v___x_1554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1556_, lean_object* v_i_1557_, lean_object* v_bs_1558_){
_start:
{
size_t v_sz_boxed_1559_; size_t v_i_boxed_1560_; lean_object* v_res_1561_; 
v_sz_boxed_1559_ = lean_unbox_usize(v_sz_1556_);
lean_dec(v_sz_1556_);
v_i_boxed_1560_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1559_, v_i_boxed_1560_, v_bs_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1562_){
_start:
{
size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_sz_1563_ = lean_array_size(v_a_1562_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1563_, v___x_1564_, v_a_1562_);
v___x_1566_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1571_){
_start:
{
lean_object* v_result_x3f_1572_; lean_object* v_errors_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1591_; 
v_result_x3f_1572_ = lean_ctor_get(v_x_1571_, 0);
v_errors_1573_ = lean_ctor_get(v_x_1571_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1571_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1575_ = v_x_1571_;
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_errors_1573_);
lean_inc(v_result_x3f_1572_);
lean_dec(v_x_1571_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1577_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1578_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1577_, v_result_x3f_1572_);
v___x_1579_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1580_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1580_);
lean_ctor_set(v___x_1575_, 0, v___x_1579_);
v___x_1582_ = v___x_1575_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1578_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1588_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1586_, v___x_1587_);
v___x_1589_ = l_Lean_Json_mkObj(v___x_1588_);
lean_dec(v___x_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_bs_1596_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1597_ == 0)
{
return v_bs_1596_;
}
else
{
lean_object* v_v_1598_; lean_object* v___x_1599_; lean_object* v_bs_x27_1600_; lean_object* v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v_v_1598_ = lean_array_uget(v_bs_1596_, v_i_1595_);
v___x_1599_ = lean_unsigned_to_nat(0u);
v_bs_x27_1600_ = lean_array_uset(v_bs_1596_, v_i_1595_, v___x_1599_);
v___x_1601_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1598_);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_add(v_i_1595_, v___x_1602_);
v___x_1604_ = lean_array_uset(v_bs_x27_1600_, v_i_1595_, v___x_1601_);
v_i_1595_ = v___x_1603_;
v_bs_1596_ = v___x_1604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1606_, lean_object* v_i_1607_, lean_object* v_bs_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1606_);
lean_dec(v_sz_1606_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* v_a_1612_){
_start:
{
size_t v_sz_1613_; size_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_sz_1613_ = lean_array_size(v_a_1612_);
v___x_1614_ = ((size_t)0ULL);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_1613_, v___x_1614_, v_a_1612_);
v___x_1616_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* v_x_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1619_ = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
v___x_1620_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_1618_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1622_);
v___x_1625_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1626_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1624_, v___x_1625_);
v___x_1627_ = l_Lean_Json_mkObj(v___x_1626_);
lean_dec(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1632_, size_t v_i_1633_, lean_object* v_bs_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1633_, v_sz_1632_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1634_);
return v___x_1637_;
}
else
{
lean_object* v_v_1638_; lean_object* v___x_1639_; lean_object* v_bs_x27_1640_; lean_object* v_a_1642_; lean_object* v_a_1648_; lean_object* v___x_1655_; 
v_v_1638_ = lean_array_uget(v_bs_1634_, v_i_1633_);
v___x_1639_ = lean_unsigned_to_nat(0u);
v_bs_x27_1640_ = lean_array_uset(v_bs_1634_, v_i_1633_, v___x_1639_);
v___x_1655_ = l_IO_FS_readFile(v_v_1638_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = l_Lean_parseImports_x27(v_a_1656_, v_v_1638_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 1);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v_a_1642_ = v___x_1665_;
goto v___jp_1641_;
}
}
}
else
{
lean_object* v_a_1668_; 
v_a_1668_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1657_, 1);
v_a_1648_ = v_a_1668_;
goto v___jp_1647_;
}
}
else
{
lean_object* v_a_1669_; 
lean_dec(v_v_1638_);
v_a_1669_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1655_, 1);
v_a_1648_ = v_a_1669_;
goto v___jp_1647_;
}
v___jp_1641_:
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = ((size_t)1ULL);
v___x_1644_ = lean_usize_add(v_i_1633_, v___x_1643_);
v___x_1645_ = lean_array_uset(v_bs_x27_1640_, v_i_1633_, v_a_1642_);
v_i_1633_ = v___x_1644_;
v_bs_1634_ = v___x_1645_;
goto _start;
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_io_error_to_string(v_a_1648_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___x_1651_);
v___x_1653_ = lean_array_push(v___x_1652_, v___x_1650_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1649_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v_a_1642_ = v___x_1654_;
goto v___jp_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1670_, lean_object* v_i_1671_, lean_object* v_bs_1672_, lean_object* v___y_1673_){
_start:
{
size_t v_sz_boxed_1674_; size_t v_i_boxed_1675_; lean_object* v_res_1676_; 
v_sz_boxed_1674_ = lean_unbox_usize(v_sz_1670_);
lean_dec(v_sz_1670_);
v_i_boxed_1675_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1674_, v_i_boxed_1675_, v_bs_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v_putStr_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_get_stdout();
v_putStr_1680_ = lean_ctor_get(v___x_1679_, 4);
lean_inc_ref(v_putStr_1680_);
lean_dec_ref(v___x_1679_);
v___x_1681_ = lean_apply_2(v_putStr_1680_, v_s_1677_, lean_box(0));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1685_){
_start:
{
uint32_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = 10;
v___x_1688_ = lean_string_push(v_s_1685_, v___x_1687_);
v___x_1689_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1693_){
_start:
{
size_t v_sz_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v_sz_1695_ = lean_array_size(v_fileNames_1693_);
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1695_, v___x_1696_, v_fileNames_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1698_);
v___x_1700_ = l_Lean_Json_compress(v___x_1699_);
v___x_1701_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1700_);
return v___x_1701_;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1697_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1697_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_printImportsJson(v_fileNames_1710_);
return v_res_1712_;
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
