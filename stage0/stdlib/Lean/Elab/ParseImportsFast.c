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
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2 = (const lean_object*)&l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value;
static const lean_string_object l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
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
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_string_utf8_next_fast(v_k_450_, v_i_455_);
lean_dec(v_i_455_);
v___x_464_ = lean_string_utf8_next_fast(v_input_453_, v_j_456_);
lean_dec(v_j_456_);
v_i_455_ = v___x_463_;
v_j_456_ = v___x_464_;
goto _start;
}
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
else
{
lean_object* v_imports_467_; uint8_t v_badModifier_468_; lean_object* v_error_x3f_469_; uint8_t v_isModule_470_; uint8_t v_isMeta_471_; uint8_t v_isExported_472_; uint8_t v_importAll_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_i_455_);
lean_dec_ref(v_failure_451_);
v_imports_467_ = lean_ctor_get(v_s_454_, 0);
v_badModifier_468_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3);
v_error_x3f_469_ = lean_ctor_get(v_s_454_, 2);
v_isModule_470_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 1);
v_isMeta_471_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 2);
v_isExported_472_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 3);
v_importAll_473_ = lean_ctor_get_uint8(v_s_454_, sizeof(void*)*3 + 4);
v_isSharedCheck_482_ = !lean_is_exclusive(v_s_454_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_s_454_, 1);
lean_dec(v_unused_483_);
v___x_475_ = v_s_454_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_error_x3f_469_);
lean_inc(v_imports_467_);
lean_dec(v_s_454_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_j_456_);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_imports_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_j_456_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_error_x3f_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3, v_badModifier_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 1, v_isModule_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 2, v_isMeta_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 3, v_isExported_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 4, v_importAll_473_);
v___x_478_ = v_reuseFailAlloc_481_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = l_Lean_ParseImports_whitespace(v_input_453_, v___x_478_);
v___x_480_ = lean_apply_2(v_success_452_, v_input_453_, v___x_479_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* v_k_484_, lean_object* v_failure_485_, lean_object* v_success_486_, lean_object* v_input_487_, lean_object* v_s_488_, lean_object* v_i_489_, lean_object* v_j_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_484_, v_failure_485_, v_success_486_, v_input_487_, v_s_488_, v_i_489_, v_j_490_);
lean_dec_ref(v_k_484_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* v_k_492_, lean_object* v_failure_493_, lean_object* v_success_494_, lean_object* v_input_495_, lean_object* v_s_496_){
_start:
{
lean_object* v_pos_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_pos_497_ = lean_ctor_get(v_s_496_, 1);
lean_inc(v_pos_497_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_492_, v_failure_493_, v_success_494_, v_input_495_, v_s_496_, v___x_498_, v_pos_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* v_k_500_, lean_object* v_failure_501_, lean_object* v_success_502_, lean_object* v_input_503_, lean_object* v_s_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_ParseImports_keywordCore(v_k_500_, v_failure_501_, v_success_502_, v_input_503_, v_s_504_);
lean_dec_ref(v_k_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* v_k_508_, lean_object* v_x_509_, lean_object* v_s_510_){
_start:
{
lean_object* v_imports_511_; lean_object* v_pos_512_; uint8_t v_badModifier_513_; uint8_t v_isModule_514_; uint8_t v_isMeta_515_; uint8_t v_isExported_516_; uint8_t v_importAll_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_imports_511_ = lean_ctor_get(v_s_510_, 0);
v_pos_512_ = lean_ctor_get(v_s_510_, 1);
v_badModifier_513_ = lean_ctor_get_uint8(v_s_510_, sizeof(void*)*3);
v_isModule_514_ = lean_ctor_get_uint8(v_s_510_, sizeof(void*)*3 + 1);
v_isMeta_515_ = lean_ctor_get_uint8(v_s_510_, sizeof(void*)*3 + 2);
v_isExported_516_ = lean_ctor_get_uint8(v_s_510_, sizeof(void*)*3 + 3);
v_importAll_517_ = lean_ctor_get_uint8(v_s_510_, sizeof(void*)*3 + 4);
v_isSharedCheck_529_ = !lean_is_exclusive(v_s_510_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_s_510_, 2);
lean_dec(v_unused_530_);
v___x_519_ = v_s_510_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_pos_512_);
lean_inc(v_imports_511_);
lean_dec(v_s_510_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_521_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
v___x_522_ = lean_string_append(v___x_521_, v_k_508_);
v___x_523_ = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 2, v___x_525_);
v___x_527_ = v___x_519_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_imports_511_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_pos_512_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3, v_badModifier_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3 + 1, v_isModule_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3 + 2, v_isMeta_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3 + 3, v_isExported_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3 + 4, v_importAll_517_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* v_k_531_, lean_object* v_x_532_, lean_object* v_s_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_ParseImports_keyword___lam__0(v_k_531_, v_x_532_, v_s_533_);
lean_dec_ref(v_x_532_);
lean_dec_ref(v_k_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* v_k_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_pos_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_pos_538_ = lean_ctor_get(v_a_537_, 1);
lean_inc(v_pos_538_);
lean_inc_ref(v_k_535_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(v___f_539_, 0, v_k_535_);
v___x_540_ = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(v_k_535_, v___f_539_, v___x_540_, v_a_536_, v_a_537_, v___x_541_, v_pos_538_);
lean_dec_ref(v_k_535_);
return v___x_542_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* v_input_543_, lean_object* v_s_544_){
_start:
{
lean_object* v_pos_545_; uint32_t v_curr_546_; uint32_t v___x_547_; uint8_t v___x_548_; 
v_pos_545_ = lean_ctor_get(v_s_544_, 1);
v_curr_546_ = lean_string_utf8_get(v_input_543_, v_pos_545_);
v___x_547_ = 46;
v___x_548_ = lean_uint32_dec_eq(v_curr_546_, v___x_547_);
if (v___x_548_ == 0)
{
return v___x_548_;
}
else
{
lean_object* v_i_549_; uint8_t v___x_550_; 
v_i_549_ = lean_string_utf8_next(v_input_543_, v_pos_545_);
v___x_550_ = lean_string_utf8_at_end(v_input_543_, v_i_549_);
if (v___x_550_ == 0)
{
uint32_t v_curr_551_; uint32_t v___x_563_; uint8_t v___x_564_; 
v_curr_551_ = lean_string_utf8_get_fast(v_input_543_, v_i_549_);
lean_dec(v_i_549_);
v___x_563_ = 65;
v___x_564_ = lean_uint32_dec_le(v___x_563_, v_curr_551_);
if (v___x_564_ == 0)
{
goto v___jp_558_;
}
else
{
uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 90;
v___x_566_ = lean_uint32_dec_le(v_curr_551_, v___x_565_);
if (v___x_566_ == 0)
{
goto v___jp_558_;
}
else
{
return v___x_548_;
}
}
v___jp_552_:
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 95;
v___x_554_ = lean_uint32_dec_eq(v_curr_551_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
v___x_555_ = l_Lean_isLetterLike(v_curr_551_);
if (v___x_555_ == 0)
{
uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = l_Lean_idBeginEscape;
v___x_557_ = lean_uint32_dec_eq(v_curr_551_, v___x_556_);
return v___x_557_;
}
else
{
return v___x_548_;
}
}
else
{
return v___x_548_;
}
}
v___jp_558_:
{
uint32_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 97;
v___x_560_ = lean_uint32_dec_le(v___x_559_, v_curr_551_);
if (v___x_560_ == 0)
{
goto v___jp_552_;
}
else
{
uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 122;
v___x_562_ = lean_uint32_dec_le(v_curr_551_, v___x_561_);
if (v___x_562_ == 0)
{
goto v___jp_552_;
}
else
{
return v___x_548_;
}
}
}
}
else
{
uint8_t v___x_567_; 
lean_dec(v_i_549_);
v___x_567_ = 0;
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* v_input_568_, lean_object* v_s_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Lean_ParseImports_isIdCont(v_input_568_, v_s_569_);
lean_dec_ref(v_s_569_);
lean_dec_ref(v_input_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* v_i_572_, lean_object* v_s_573_){
_start:
{
lean_object* v_imports_574_; lean_object* v_pos_575_; uint8_t v_badModifier_576_; lean_object* v_error_x3f_577_; uint8_t v_isModule_578_; uint8_t v_isMeta_579_; uint8_t v_isExported_580_; uint8_t v_importAll_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_imports_574_ = lean_ctor_get(v_s_573_, 0);
v_pos_575_ = lean_ctor_get(v_s_573_, 1);
v_badModifier_576_ = lean_ctor_get_uint8(v_s_573_, sizeof(void*)*3);
v_error_x3f_577_ = lean_ctor_get(v_s_573_, 2);
v_isModule_578_ = lean_ctor_get_uint8(v_s_573_, sizeof(void*)*3 + 1);
v_isMeta_579_ = lean_ctor_get_uint8(v_s_573_, sizeof(void*)*3 + 2);
v_isExported_580_ = lean_ctor_get_uint8(v_s_573_, sizeof(void*)*3 + 3);
v_importAll_581_ = lean_ctor_get_uint8(v_s_573_, sizeof(void*)*3 + 4);
v_isSharedCheck_589_ = !lean_is_exclusive(v_s_573_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v_s_573_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_error_x3f_577_);
lean_inc(v_pos_575_);
lean_inc(v_imports_574_);
lean_dec(v_s_573_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_array_push(v_imports_574_, v_i_572_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_pos_575_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_error_x3f_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*3, v_badModifier_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*3 + 1, v_isModule_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*3 + 2, v_isMeta_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*3 + 3, v_isExported_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*3 + 4, v_importAll_581_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t v_c_590_){
_start:
{
uint32_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 95;
v___x_592_ = lean_uint32_dec_eq(v_c_590_, v___x_591_);
if (v___x_592_ == 0)
{
uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 39;
v___x_594_ = lean_uint32_dec_eq(v_c_590_, v___x_593_);
if (v___x_594_ == 0)
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 33;
v___x_596_ = lean_uint32_dec_eq(v_c_590_, v___x_595_);
if (v___x_596_ == 0)
{
uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 63;
v___x_598_ = lean_uint32_dec_eq(v_c_590_, v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_isLetterLike(v_c_590_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_isSubScriptAlnum(v_c_590_);
return v___x_600_;
}
else
{
return v___x_599_;
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
else
{
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* v_c_601_){
_start:
{
uint32_t v_c_boxed_602_; uint8_t v_res_603_; lean_object* v_r_604_; 
v_c_boxed_602_ = lean_unbox_uint32(v_c_601_);
lean_dec(v_c_601_);
v_res_603_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t v_c_605_){
_start:
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 65;
v___x_635_ = lean_uint32_dec_le(v___x_634_, v_c_605_);
if (v___x_635_ == 0)
{
goto v___jp_629_;
}
else
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 90;
v___x_637_ = lean_uint32_dec_le(v_c_605_, v___x_636_);
if (v___x_637_ == 0)
{
goto v___jp_629_;
}
else
{
return v___x_637_;
}
}
v___jp_606_:
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 46;
v___x_608_ = lean_uint32_dec_eq(v_c_605_, v___x_607_);
if (v___x_608_ == 0)
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 10;
v___x_610_ = lean_uint32_dec_eq(v_c_605_, v___x_609_);
if (v___x_610_ == 0)
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 32;
v___x_612_ = lean_uint32_dec_eq(v_c_605_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 95;
v___x_614_ = lean_uint32_dec_eq(v_c_605_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 39;
v___x_616_ = lean_uint32_dec_eq(v_c_605_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 33;
v___x_618_ = lean_uint32_dec_eq(v_c_605_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 63;
v___x_620_ = lean_uint32_dec_eq(v_c_605_, v___x_619_);
if (v___x_620_ == 0)
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_isLetterLike(v_c_605_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_isSubScriptAlnum(v_c_605_);
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
return v___x_616_;
}
}
else
{
return v___x_614_;
}
}
else
{
return v___x_610_;
}
}
else
{
return v___x_608_;
}
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
v___jp_624_:
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 48;
v___x_626_ = lean_uint32_dec_le(v___x_625_, v_c_605_);
if (v___x_626_ == 0)
{
goto v___jp_606_;
}
else
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 57;
v___x_628_ = lean_uint32_dec_le(v_c_605_, v___x_627_);
if (v___x_628_ == 0)
{
goto v___jp_606_;
}
else
{
return v___x_628_;
}
}
}
v___jp_629_:
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 97;
v___x_631_ = lean_uint32_dec_le(v___x_630_, v_c_605_);
if (v___x_631_ == 0)
{
goto v___jp_624_;
}
else
{
uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 122;
v___x_633_ = lean_uint32_dec_le(v_c_605_, v___x_632_);
if (v___x_633_ == 0)
{
goto v___jp_624_;
}
else
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* v_c_638_){
_start:
{
uint32_t v_c_boxed_639_; uint8_t v_res_640_; lean_object* v_r_641_; 
v_c_boxed_639_ = lean_unbox_uint32(v_c_638_);
lean_dec(v_c_638_);
v_res_640_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* v_input_642_, lean_object* v_s_643_){
_start:
{
lean_object* v_imports_644_; lean_object* v_pos_645_; uint8_t v_badModifier_646_; lean_object* v_error_x3f_647_; uint8_t v_isModule_648_; uint8_t v_isMeta_649_; uint8_t v_isExported_650_; uint8_t v_importAll_651_; uint8_t v___x_652_; 
v_imports_644_ = lean_ctor_get(v_s_643_, 0);
v_pos_645_ = lean_ctor_get(v_s_643_, 1);
v_badModifier_646_ = lean_ctor_get_uint8(v_s_643_, sizeof(void*)*3);
v_error_x3f_647_ = lean_ctor_get(v_s_643_, 2);
v_isModule_648_ = lean_ctor_get_uint8(v_s_643_, sizeof(void*)*3 + 1);
v_isMeta_649_ = lean_ctor_get_uint8(v_s_643_, sizeof(void*)*3 + 2);
v_isExported_650_ = lean_ctor_get_uint8(v_s_643_, sizeof(void*)*3 + 3);
v_importAll_651_ = lean_ctor_get_uint8(v_s_643_, sizeof(void*)*3 + 4);
v___x_652_ = lean_string_utf8_at_end(v_input_642_, v_pos_645_);
if (v___x_652_ == 0)
{
uint32_t v___x_653_; uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_string_utf8_get_fast(v_input_642_, v_pos_645_);
v___x_654_ = l_Lean_idEndEscape;
v___x_655_ = lean_uint32_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
lean_inc(v_error_x3f_647_);
lean_inc(v_pos_645_);
lean_inc_ref(v_imports_644_);
v_isSharedCheck_664_ = !lean_is_exclusive(v_s_643_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_665_ = lean_ctor_get(v_s_643_, 2);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_s_643_, 1);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_s_643_, 0);
lean_dec(v_unused_667_);
v___x_657_ = v_s_643_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_s_643_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_string_utf8_next_fast(v_input_642_, v_pos_645_);
lean_dec(v_pos_645_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_imports_644_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_error_x3f_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3, v_badModifier_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3 + 1, v_isModule_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3 + 2, v_isMeta_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3 + 3, v_isExported_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_663_, sizeof(void*)*3 + 4, v_importAll_651_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_s_643_ = v___x_661_;
goto _start;
}
}
}
else
{
return v_s_643_;
}
}
else
{
return v_s_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* v_input_668_, lean_object* v_s_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_668_, v_s_669_);
lean_dec_ref(v_input_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t v___y_671_, uint32_t v___x_672_, lean_object* v_input_673_, lean_object* v_s_674_){
_start:
{
lean_object* v_imports_675_; lean_object* v_pos_676_; uint8_t v_badModifier_677_; lean_object* v_error_x3f_678_; uint8_t v_isModule_679_; uint8_t v_isMeta_680_; uint8_t v_isExported_681_; uint8_t v_importAll_682_; uint8_t v___y_684_; uint8_t v___x_697_; 
v_imports_675_ = lean_ctor_get(v_s_674_, 0);
v_pos_676_ = lean_ctor_get(v_s_674_, 1);
v_badModifier_677_ = lean_ctor_get_uint8(v_s_674_, sizeof(void*)*3);
v_error_x3f_678_ = lean_ctor_get(v_s_674_, 2);
v_isModule_679_ = lean_ctor_get_uint8(v_s_674_, sizeof(void*)*3 + 1);
v_isMeta_680_ = lean_ctor_get_uint8(v_s_674_, sizeof(void*)*3 + 2);
v_isExported_681_ = lean_ctor_get_uint8(v_s_674_, sizeof(void*)*3 + 3);
v_importAll_682_ = lean_ctor_get_uint8(v_s_674_, sizeof(void*)*3 + 4);
v___x_697_ = lean_string_utf8_at_end(v_input_673_, v_pos_676_);
if (v___x_697_ == 0)
{
uint32_t v___x_698_; uint8_t v___x_699_; uint32_t v___x_700_; uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_698_ = l_Lean_idBeginEscape;
v___x_699_ = lean_uint32_dec_eq(v___x_672_, v___x_698_);
v___x_700_ = lean_string_utf8_get_fast(v_input_673_, v_pos_676_);
v___x_728_ = 65;
v___x_729_ = lean_uint32_dec_le(v___x_728_, v___x_700_);
if (v___x_729_ == 0)
{
goto v___jp_723_;
}
else
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 90;
v___x_731_ = lean_uint32_dec_le(v___x_700_, v___x_730_);
if (v___x_731_ == 0)
{
goto v___jp_723_;
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
v___jp_701_:
{
uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 46;
v___x_703_ = lean_uint32_dec_eq(v___x_700_, v___x_702_);
if (v___x_703_ == 0)
{
uint32_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = 10;
v___x_705_ = lean_uint32_dec_eq(v___x_700_, v___x_704_);
if (v___x_705_ == 0)
{
uint32_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 32;
v___x_707_ = lean_uint32_dec_eq(v___x_700_, v___x_706_);
if (v___x_707_ == 0)
{
uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 95;
v___x_709_ = lean_uint32_dec_eq(v___x_700_, v___x_708_);
if (v___x_709_ == 0)
{
uint32_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = 39;
v___x_711_ = lean_uint32_dec_eq(v___x_700_, v___x_710_);
if (v___x_711_ == 0)
{
uint32_t v___x_712_; uint8_t v___x_713_; 
v___x_712_ = 33;
v___x_713_ = lean_uint32_dec_eq(v___x_700_, v___x_712_);
if (v___x_713_ == 0)
{
uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 63;
v___x_715_ = lean_uint32_dec_eq(v___x_700_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_isLetterLike(v___x_700_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_isSubScriptAlnum(v___x_700_);
if (v___x_717_ == 0)
{
v___y_684_ = v___y_671_;
goto v___jp_683_;
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___y_671_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___y_671_;
goto v___jp_683_;
}
}
else
{
v___y_684_ = v___y_671_;
goto v___jp_683_;
}
}
v___jp_718_:
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 48;
v___x_720_ = lean_uint32_dec_le(v___x_719_, v___x_700_);
if (v___x_720_ == 0)
{
goto v___jp_701_;
}
else
{
uint32_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 57;
v___x_722_ = lean_uint32_dec_le(v___x_700_, v___x_721_);
if (v___x_722_ == 0)
{
goto v___jp_701_;
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
}
v___jp_723_:
{
uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = 97;
v___x_725_ = lean_uint32_dec_le(v___x_724_, v___x_700_);
if (v___x_725_ == 0)
{
goto v___jp_718_;
}
else
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 122;
v___x_727_ = lean_uint32_dec_le(v___x_700_, v___x_726_);
if (v___x_727_ == 0)
{
goto v___jp_718_;
}
else
{
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
}
}
else
{
return v_s_674_;
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
lean_inc(v_error_x3f_678_);
lean_inc(v_pos_676_);
lean_inc_ref(v_imports_675_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_s_674_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_694_ = lean_ctor_get(v_s_674_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_s_674_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_s_674_, 0);
lean_dec(v_unused_696_);
v___x_686_ = v_s_674_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_dec(v_s_674_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_string_utf8_next_fast(v_input_673_, v_pos_676_);
lean_dec(v_pos_676_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_imports_675_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_error_x3f_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*3, v_badModifier_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*3 + 1, v_isModule_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*3 + 2, v_isMeta_680_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*3 + 3, v_isExported_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*3 + 4, v_importAll_682_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_s_674_ = v___x_690_;
goto _start;
}
}
}
else
{
return v_s_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* v___y_732_, lean_object* v___x_733_, lean_object* v_input_734_, lean_object* v_s_735_){
_start:
{
uint8_t v___y_1014__boxed_736_; uint32_t v___x_1015__boxed_737_; lean_object* v_res_738_; 
v___y_1014__boxed_736_ = lean_unbox(v___y_732_);
v___x_1015__boxed_737_ = lean_unbox_uint32(v___x_733_);
lean_dec(v___x_733_);
v_res_738_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_1014__boxed_736_, v___x_1015__boxed_737_, v_input_734_, v_s_735_);
lean_dec_ref(v_input_734_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* v_input_745_, lean_object* v_finalize_746_, lean_object* v_module_747_, lean_object* v_s_748_){
_start:
{
uint8_t v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v_imports_762_; lean_object* v_pos_763_; uint8_t v_badModifier_764_; lean_object* v_error_x3f_765_; uint8_t v_isModule_766_; uint8_t v_isMeta_767_; uint8_t v_isExported_768_; uint8_t v_importAll_769_; uint8_t v___x_770_; 
v_imports_762_ = lean_ctor_get(v_s_748_, 0);
v_pos_763_ = lean_ctor_get(v_s_748_, 1);
v_badModifier_764_ = lean_ctor_get_uint8(v_s_748_, sizeof(void*)*3);
v_error_x3f_765_ = lean_ctor_get(v_s_748_, 2);
v_isModule_766_ = lean_ctor_get_uint8(v_s_748_, sizeof(void*)*3 + 1);
v_isMeta_767_ = lean_ctor_get_uint8(v_s_748_, sizeof(void*)*3 + 2);
v_isExported_768_ = lean_ctor_get_uint8(v_s_748_, sizeof(void*)*3 + 3);
v_importAll_769_ = lean_ctor_get_uint8(v_s_748_, sizeof(void*)*3 + 4);
v___x_770_ = lean_string_utf8_at_end(v_input_745_, v_pos_763_);
if (v___x_770_ == 0)
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_error_x3f_765_);
lean_inc(v_pos_763_);
lean_inc_ref(v_imports_762_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_s_748_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_908_ = lean_ctor_get(v_s_748_, 2);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_s_748_, 1);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_s_748_, 0);
lean_dec(v_unused_910_);
v___x_772_ = v_s_748_;
v_isShared_773_ = v_isSharedCheck_907_;
goto v_resetjp_771_;
}
else
{
lean_dec(v_s_748_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_907_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint32_t v_curr_774_; uint32_t v___x_775_; uint8_t v___y_777_; uint8_t v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; uint8_t v___y_781_; uint32_t v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; uint8_t v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; uint8_t v___y_798_; uint32_t v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; uint8_t v___y_810_; uint8_t v___x_849_; 
v_curr_774_ = lean_string_utf8_get_fast(v_input_745_, v_pos_763_);
v___x_775_ = l_Lean_idBeginEscape;
v___x_849_ = lean_uint32_dec_eq(v_curr_774_, v___x_775_);
if (v___x_849_ == 0)
{
uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = 65;
v___x_851_ = lean_uint32_dec_le(v___x_850_, v_curr_774_);
if (v___x_851_ == 0)
{
goto v___jp_844_;
}
else
{
uint32_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = 90;
v___x_853_ = lean_uint32_dec_le(v_curr_774_, v___x_852_);
if (v___x_853_ == 0)
{
goto v___jp_844_;
}
else
{
v___y_810_ = v___x_853_;
goto v___jp_809_;
}
}
}
else
{
lean_object* v_startPart_854_; lean_object* v___x_855_; lean_object* v_s_856_; lean_object* v_imports_857_; lean_object* v_pos_858_; uint8_t v_badModifier_859_; lean_object* v_error_x3f_860_; uint8_t v_isModule_861_; uint8_t v_isMeta_862_; uint8_t v_isExported_863_; uint8_t v_importAll_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_772_);
v_startPart_854_ = lean_string_utf8_next_fast(v_input_745_, v_pos_763_);
lean_dec(v_pos_763_);
v___x_855_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_855_, 0, v_imports_762_);
lean_ctor_set(v___x_855_, 1, v_startPart_854_);
lean_ctor_set(v___x_855_, 2, v_error_x3f_765_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3, v_badModifier_764_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3 + 1, v_isModule_766_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3 + 2, v_isMeta_767_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3 + 3, v_isExported_768_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3 + 4, v_importAll_769_);
v_s_856_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_745_, v___x_855_);
v_imports_857_ = lean_ctor_get(v_s_856_, 0);
v_pos_858_ = lean_ctor_get(v_s_856_, 1);
v_badModifier_859_ = lean_ctor_get_uint8(v_s_856_, sizeof(void*)*3);
v_error_x3f_860_ = lean_ctor_get(v_s_856_, 2);
v_isModule_861_ = lean_ctor_get_uint8(v_s_856_, sizeof(void*)*3 + 1);
v_isMeta_862_ = lean_ctor_get_uint8(v_s_856_, sizeof(void*)*3 + 2);
v_isExported_863_ = lean_ctor_get_uint8(v_s_856_, sizeof(void*)*3 + 3);
v_importAll_864_ = lean_ctor_get_uint8(v_s_856_, sizeof(void*)*3 + 4);
v_isSharedCheck_906_ = !lean_is_exclusive(v_s_856_);
if (v_isSharedCheck_906_ == 0)
{
v___x_866_ = v_s_856_;
v_isShared_867_ = v_isSharedCheck_906_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_error_x3f_860_);
lean_inc(v_pos_858_);
lean_inc(v_imports_857_);
lean_dec(v_s_856_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_906_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
v___x_868_ = lean_string_utf8_at_end(v_input_745_, v_pos_858_);
if (v___x_868_ == 0)
{
lean_object* v_i_869_; lean_object* v_s_871_; 
v_i_869_ = lean_string_utf8_next_fast(v_input_745_, v_pos_858_);
lean_inc(v_error_x3f_860_);
lean_inc_ref(v_imports_857_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_i_869_);
v_s_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_imports_857_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_i_869_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_error_x3f_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3, v_badModifier_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 1, v_isModule_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 2, v_isMeta_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 3, v_isExported_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_901_, sizeof(void*)*3 + 4, v_importAll_864_);
v_s_871_ = v_reuseFailAlloc_901_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v_module_873_; uint32_t v_curr_878_; uint32_t v___x_879_; uint8_t v___x_880_; 
v___x_872_ = lean_string_utf8_extract(v_input_745_, v_startPart_854_, v_pos_858_);
lean_dec(v_pos_858_);
v_module_873_ = l_Lean_Name_str___override(v_module_747_, v___x_872_);
v_curr_878_ = lean_string_utf8_get(v_input_745_, v_i_869_);
v___x_879_ = 46;
v___x_880_ = lean_uint32_dec_eq(v_curr_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_error_x3f_860_);
lean_dec_ref(v_imports_857_);
v___x_881_ = lean_apply_3(v_finalize_746_, v_module_873_, v_input_745_, v_s_871_);
return v___x_881_;
}
else
{
lean_object* v_i_882_; uint8_t v___x_883_; 
v_i_882_ = lean_string_utf8_next(v_input_745_, v_i_869_);
v___x_883_ = lean_string_utf8_at_end(v_input_745_, v_i_882_);
if (v___x_883_ == 0)
{
uint32_t v_curr_884_; uint32_t v___x_896_; uint8_t v___x_897_; 
v_curr_884_ = lean_string_utf8_get_fast(v_input_745_, v_i_882_);
lean_dec(v_i_882_);
v___x_896_ = 65;
v___x_897_ = lean_uint32_dec_le(v___x_896_, v_curr_884_);
if (v___x_897_ == 0)
{
goto v___jp_891_;
}
else
{
uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = 90;
v___x_899_ = lean_uint32_dec_le(v_curr_884_, v___x_898_);
if (v___x_899_ == 0)
{
goto v___jp_891_;
}
else
{
lean_dec_ref(v_s_871_);
goto v___jp_874_;
}
}
v___jp_885_:
{
uint32_t v___x_886_; uint8_t v___x_887_; 
v___x_886_ = 95;
v___x_887_ = lean_uint32_dec_eq(v_curr_884_, v___x_886_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_isLetterLike(v_curr_884_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; 
v___x_889_ = lean_uint32_dec_eq(v_curr_884_, v___x_775_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_error_x3f_860_);
lean_dec_ref(v_imports_857_);
v___x_890_ = lean_apply_3(v_finalize_746_, v_module_873_, v_input_745_, v_s_871_);
return v___x_890_;
}
else
{
lean_dec_ref(v_s_871_);
goto v___jp_874_;
}
}
else
{
lean_dec_ref(v_s_871_);
goto v___jp_874_;
}
}
else
{
lean_dec_ref(v_s_871_);
goto v___jp_874_;
}
}
v___jp_891_:
{
uint32_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = 97;
v___x_893_ = lean_uint32_dec_le(v___x_892_, v_curr_884_);
if (v___x_893_ == 0)
{
goto v___jp_885_;
}
else
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 122;
v___x_895_ = lean_uint32_dec_le(v_curr_884_, v___x_894_);
if (v___x_895_ == 0)
{
goto v___jp_885_;
}
else
{
lean_dec_ref(v_s_871_);
goto v___jp_874_;
}
}
}
}
else
{
lean_object* v___x_900_; 
lean_dec(v_i_882_);
lean_dec(v_error_x3f_860_);
lean_dec_ref(v_imports_857_);
v___x_900_ = lean_apply_3(v_finalize_746_, v_module_873_, v_input_745_, v_s_871_);
return v___x_900_;
}
}
v___jp_874_:
{
lean_object* v___x_875_; lean_object* v_s_876_; 
v___x_875_ = lean_string_utf8_next(v_input_745_, v_i_869_);
v_s_876_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_876_, 0, v_imports_857_);
lean_ctor_set(v_s_876_, 1, v___x_875_);
lean_ctor_set(v_s_876_, 2, v_error_x3f_860_);
lean_ctor_set_uint8(v_s_876_, sizeof(void*)*3, v_badModifier_859_);
lean_ctor_set_uint8(v_s_876_, sizeof(void*)*3 + 1, v_isModule_861_);
lean_ctor_set_uint8(v_s_876_, sizeof(void*)*3 + 2, v_isMeta_862_);
lean_ctor_set_uint8(v_s_876_, sizeof(void*)*3 + 3, v_isExported_863_);
lean_ctor_set_uint8(v_s_876_, sizeof(void*)*3 + 4, v_importAll_864_);
v_module_747_ = v_module_873_;
v_s_748_ = v_s_876_;
goto _start;
}
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_error_x3f_860_);
lean_dec(v_module_747_);
lean_dec_ref(v_finalize_746_);
lean_dec_ref(v_input_745_);
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 2, v___x_902_);
v___x_904_ = v___x_866_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_imports_857_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_pos_858_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*3, v_badModifier_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*3 + 1, v_isModule_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*3 + 2, v_isMeta_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*3 + 3, v_isExported_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, sizeof(void*)*3 + 4, v_importAll_864_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
v___jp_776_:
{
uint32_t v___x_788_; uint8_t v___x_789_; 
v___x_788_ = 95;
v___x_789_ = lean_uint32_dec_eq(v___y_782_, v___x_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; 
v___x_790_ = l_Lean_isLetterLike(v___y_782_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; 
v___x_791_ = lean_uint32_dec_eq(v___y_782_, v___x_775_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_779_);
v___x_792_ = lean_apply_3(v_finalize_746_, v___y_784_, v_input_745_, v___y_780_);
return v___x_792_;
}
else
{
lean_dec_ref(v___y_780_);
v___y_750_ = v___y_778_;
v___y_751_ = v___y_777_;
v___y_752_ = v___y_779_;
v___y_753_ = v___y_781_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_787_;
v___y_757_ = v___y_786_;
v___y_758_ = v___y_785_;
goto v___jp_749_;
}
}
else
{
lean_dec_ref(v___y_780_);
v___y_750_ = v___y_778_;
v___y_751_ = v___y_777_;
v___y_752_ = v___y_779_;
v___y_753_ = v___y_781_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_787_;
v___y_757_ = v___y_786_;
v___y_758_ = v___y_785_;
goto v___jp_749_;
}
}
else
{
lean_dec_ref(v___y_780_);
v___y_750_ = v___y_778_;
v___y_751_ = v___y_777_;
v___y_752_ = v___y_779_;
v___y_753_ = v___y_781_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_787_;
v___y_757_ = v___y_786_;
v___y_758_ = v___y_785_;
goto v___jp_749_;
}
}
v___jp_793_:
{
uint32_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = 97;
v___x_806_ = lean_uint32_dec_le(v___x_805_, v___y_799_);
if (v___x_806_ == 0)
{
v___y_777_ = v___y_795_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_796_;
v___y_781_ = v___y_798_;
v___y_782_ = v___y_799_;
v___y_783_ = v___y_800_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_804_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_802_;
goto v___jp_776_;
}
else
{
uint32_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = 122;
v___x_808_ = lean_uint32_dec_le(v___y_799_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_777_ = v___y_795_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_796_;
v___y_781_ = v___y_798_;
v___y_782_ = v___y_799_;
v___y_783_ = v___y_800_;
v___y_784_ = v___y_801_;
v___y_785_ = v___y_804_;
v___y_786_ = v___y_803_;
v___y_787_ = v___y_802_;
goto v___jp_776_;
}
else
{
lean_dec_ref(v___y_796_);
v___y_750_ = v___y_794_;
v___y_751_ = v___y_795_;
v___y_752_ = v___y_797_;
v___y_753_ = v___y_798_;
v___y_754_ = v___y_800_;
v___y_755_ = v___y_801_;
v___y_756_ = v___y_802_;
v___y_757_ = v___y_803_;
v___y_758_ = v___y_804_;
goto v___jp_749_;
}
}
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_string_utf8_next_fast(v_input_745_, v_pos_763_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_811_);
v___x_813_ = v___x_772_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_imports_762_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_error_x3f_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3, v_badModifier_764_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3 + 1, v_isModule_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3 + 2, v_isMeta_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3 + 3, v_isExported_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3 + 4, v_importAll_769_);
v___x_813_ = v_reuseFailAlloc_837_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v_s_814_; lean_object* v_imports_815_; lean_object* v_pos_816_; uint8_t v_badModifier_817_; lean_object* v_error_x3f_818_; uint8_t v_isModule_819_; uint8_t v_isMeta_820_; uint8_t v_isExported_821_; uint8_t v_importAll_822_; lean_object* v___x_823_; lean_object* v_module_824_; uint32_t v_curr_825_; uint32_t v___x_826_; uint8_t v___x_827_; 
v_s_814_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_810_, v_curr_774_, v_input_745_, v___x_813_);
v_imports_815_ = lean_ctor_get(v_s_814_, 0);
v_pos_816_ = lean_ctor_get(v_s_814_, 1);
v_badModifier_817_ = lean_ctor_get_uint8(v_s_814_, sizeof(void*)*3);
v_error_x3f_818_ = lean_ctor_get(v_s_814_, 2);
v_isModule_819_ = lean_ctor_get_uint8(v_s_814_, sizeof(void*)*3 + 1);
v_isMeta_820_ = lean_ctor_get_uint8(v_s_814_, sizeof(void*)*3 + 2);
v_isExported_821_ = lean_ctor_get_uint8(v_s_814_, sizeof(void*)*3 + 3);
v_importAll_822_ = lean_ctor_get_uint8(v_s_814_, sizeof(void*)*3 + 4);
v___x_823_ = lean_string_utf8_extract(v_input_745_, v_pos_763_, v_pos_816_);
lean_dec(v_pos_763_);
v_module_824_ = l_Lean_Name_str___override(v_module_747_, v___x_823_);
v_curr_825_ = lean_string_utf8_get(v_input_745_, v_pos_816_);
v___x_826_ = 46;
v___x_827_ = lean_uint32_dec_eq(v_curr_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_apply_3(v_finalize_746_, v_module_824_, v_input_745_, v_s_814_);
return v___x_828_;
}
else
{
lean_object* v_i_829_; uint8_t v___x_830_; 
v_i_829_ = lean_string_utf8_next(v_input_745_, v_pos_816_);
v___x_830_ = lean_string_utf8_at_end(v_input_745_, v_i_829_);
if (v___x_830_ == 0)
{
uint32_t v_curr_831_; uint32_t v___x_832_; uint8_t v___x_833_; 
lean_inc(v_error_x3f_818_);
lean_inc(v_pos_816_);
lean_inc_ref(v_imports_815_);
v_curr_831_ = lean_string_utf8_get_fast(v_input_745_, v_i_829_);
lean_dec(v_i_829_);
v___x_832_ = 65;
v___x_833_ = lean_uint32_dec_le(v___x_832_, v_curr_831_);
if (v___x_833_ == 0)
{
v___y_794_ = v_importAll_822_;
v___y_795_ = v_isExported_821_;
v___y_796_ = v_s_814_;
v___y_797_ = v_pos_816_;
v___y_798_ = v_isMeta_820_;
v___y_799_ = v_curr_831_;
v___y_800_ = v_badModifier_817_;
v___y_801_ = v_module_824_;
v___y_802_ = v_isModule_819_;
v___y_803_ = v_error_x3f_818_;
v___y_804_ = v_imports_815_;
goto v___jp_793_;
}
else
{
uint32_t v___x_834_; uint8_t v___x_835_; 
v___x_834_ = 90;
v___x_835_ = lean_uint32_dec_le(v_curr_831_, v___x_834_);
if (v___x_835_ == 0)
{
v___y_794_ = v_importAll_822_;
v___y_795_ = v_isExported_821_;
v___y_796_ = v_s_814_;
v___y_797_ = v_pos_816_;
v___y_798_ = v_isMeta_820_;
v___y_799_ = v_curr_831_;
v___y_800_ = v_badModifier_817_;
v___y_801_ = v_module_824_;
v___y_802_ = v_isModule_819_;
v___y_803_ = v_error_x3f_818_;
v___y_804_ = v_imports_815_;
goto v___jp_793_;
}
else
{
lean_dec_ref(v_s_814_);
v___y_750_ = v_importAll_822_;
v___y_751_ = v_isExported_821_;
v___y_752_ = v_pos_816_;
v___y_753_ = v_isMeta_820_;
v___y_754_ = v_badModifier_817_;
v___y_755_ = v_module_824_;
v___y_756_ = v_isModule_819_;
v___y_757_ = v_error_x3f_818_;
v___y_758_ = v_imports_815_;
goto v___jp_749_;
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v_i_829_);
v___x_836_ = lean_apply_3(v_finalize_746_, v_module_824_, v_input_745_, v_s_814_);
return v___x_836_;
}
}
}
}
v___jp_838_:
{
uint32_t v___x_839_; uint8_t v___x_840_; 
v___x_839_ = 95;
v___x_840_ = lean_uint32_dec_eq(v_curr_774_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_isLetterLike(v_curr_774_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_772_);
lean_dec(v_error_x3f_765_);
lean_dec(v_module_747_);
lean_dec_ref(v_finalize_746_);
lean_dec_ref(v_input_745_);
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
v___x_843_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_843_, 0, v_imports_762_);
lean_ctor_set(v___x_843_, 1, v_pos_763_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3, v_badModifier_764_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 1, v_isModule_766_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 2, v_isMeta_767_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 3, v_isExported_768_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 4, v_importAll_769_);
return v___x_843_;
}
else
{
v___y_810_ = v___x_841_;
goto v___jp_809_;
}
}
else
{
v___y_810_ = v___x_840_;
goto v___jp_809_;
}
}
v___jp_844_:
{
uint32_t v___x_845_; uint8_t v___x_846_; 
v___x_845_ = 97;
v___x_846_ = lean_uint32_dec_le(v___x_845_, v_curr_774_);
if (v___x_846_ == 0)
{
goto v___jp_838_;
}
else
{
uint32_t v___x_847_; uint8_t v___x_848_; 
v___x_847_ = 122;
v___x_848_ = lean_uint32_dec_le(v_curr_774_, v___x_847_);
if (v___x_848_ == 0)
{
goto v___jp_838_;
}
else
{
v___y_810_ = v___x_848_;
goto v___jp_809_;
}
}
}
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_module_747_);
lean_dec_ref(v_finalize_746_);
lean_dec_ref(v_input_745_);
v___x_911_ = l_Lean_ParseImports_State_mkEOIError(v_s_748_);
return v___x_911_;
}
v___jp_749_:
{
lean_object* v___x_759_; lean_object* v_s_760_; 
v___x_759_ = lean_string_utf8_next(v_input_745_, v___y_752_);
lean_dec(v___y_752_);
v_s_760_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_s_760_, 0, v___y_758_);
lean_ctor_set(v_s_760_, 1, v___x_759_);
lean_ctor_set(v_s_760_, 2, v___y_757_);
lean_ctor_set_uint8(v_s_760_, sizeof(void*)*3, v___y_754_);
lean_ctor_set_uint8(v_s_760_, sizeof(void*)*3 + 1, v___y_756_);
lean_ctor_set_uint8(v_s_760_, sizeof(void*)*3 + 2, v___y_753_);
lean_ctor_set_uint8(v_s_760_, sizeof(void*)*3 + 3, v___y_751_);
lean_ctor_set_uint8(v_s_760_, sizeof(void*)*3 + 4, v___y_750_);
v_module_747_ = v___y_755_;
v_s_748_ = v_s_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* v_module_912_, lean_object* v_input_913_, lean_object* v_s_914_){
_start:
{
uint8_t v_isMeta_915_; uint8_t v_isExported_916_; uint8_t v_importAll_917_; lean_object* v_imp_918_; lean_object* v___x_919_; lean_object* v_s_920_; lean_object* v_imports_921_; lean_object* v_pos_922_; uint8_t v_badModifier_923_; lean_object* v_error_x3f_924_; uint8_t v_isModule_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v_isMeta_915_ = lean_ctor_get_uint8(v_s_914_, sizeof(void*)*3 + 2);
v_isExported_916_ = lean_ctor_get_uint8(v_s_914_, sizeof(void*)*3 + 3);
v_importAll_917_ = lean_ctor_get_uint8(v_s_914_, sizeof(void*)*3 + 4);
v_imp_918_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_imp_918_, 0, v_module_912_);
lean_ctor_set_uint8(v_imp_918_, sizeof(void*)*1, v_importAll_917_);
lean_ctor_set_uint8(v_imp_918_, sizeof(void*)*1 + 1, v_isExported_916_);
lean_ctor_set_uint8(v_imp_918_, sizeof(void*)*1 + 2, v_isMeta_915_);
v___x_919_ = l_Lean_ParseImports_State_pushImport(v_imp_918_, v_s_914_);
v_s_920_ = l_Lean_ParseImports_whitespace(v_input_913_, v___x_919_);
v_imports_921_ = lean_ctor_get(v_s_920_, 0);
v_pos_922_ = lean_ctor_get(v_s_920_, 1);
v_badModifier_923_ = lean_ctor_get_uint8(v_s_920_, sizeof(void*)*3);
v_error_x3f_924_ = lean_ctor_get(v_s_920_, 2);
v_isModule_925_ = lean_ctor_get_uint8(v_s_920_, sizeof(void*)*3 + 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_s_920_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v_s_920_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_error_x3f_924_);
lean_inc(v_pos_922_);
lean_inc(v_imports_921_);
lean_dec(v_s_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
uint8_t v___x_929_; 
v___x_929_ = 0;
if (v_isModule_925_ == 0)
{
uint8_t v___x_930_; lean_object* v___x_932_; 
v___x_930_ = 1;
if (v_isShared_928_ == 0)
{
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_imports_921_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_pos_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_error_x3f_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*3, v_badModifier_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*3 + 1, v_isModule_925_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*3 + 2, v___x_929_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*3 + 3, v___x_930_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*3 + 4, v___x_929_);
return v___x_932_;
}
}
else
{
lean_object* v___x_935_; 
if (v_isShared_928_ == 0)
{
v___x_935_ = v___x_927_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_imports_921_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_pos_922_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_error_x3f_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3, v_badModifier_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 1, v_isModule_925_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*3 + 2, v___x_929_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*3 + 3, v___x_929_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*3 + 4, v___x_929_);
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* v_module_938_, lean_object* v_input_939_, lean_object* v_s_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_ParseImports_moduleIdent___lam__0(v_module_938_, v_input_939_, v_s_940_);
lean_dec_ref(v_input_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* v_input_943_, lean_object* v_s_944_){
_start:
{
lean_object* v_finalize_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_finalize_945_ = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
v___x_946_ = lean_box(0);
v___x_947_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(v_input_943_, v_finalize_945_, v___x_946_, v_s_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* v_p_948_, lean_object* v_input_949_, lean_object* v_s_950_){
_start:
{
lean_object* v_pos_951_; lean_object* v_s_952_; lean_object* v_error_x3f_953_; 
v_pos_951_ = lean_ctor_get(v_s_950_, 1);
lean_inc(v_pos_951_);
v_s_952_ = lean_apply_2(v_p_948_, v_input_949_, v_s_950_);
v_error_x3f_953_ = lean_ctor_get(v_s_952_, 2);
lean_inc(v_error_x3f_953_);
if (lean_obj_tag(v_error_x3f_953_) == 1)
{
lean_object* v_imports_954_; uint8_t v_badModifier_955_; uint8_t v_isModule_956_; uint8_t v_isMeta_957_; uint8_t v_isExported_958_; uint8_t v_importAll_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_imports_954_ = lean_ctor_get(v_s_952_, 0);
v_badModifier_955_ = lean_ctor_get_uint8(v_s_952_, sizeof(void*)*3);
v_isModule_956_ = lean_ctor_get_uint8(v_s_952_, sizeof(void*)*3 + 1);
v_isMeta_957_ = lean_ctor_get_uint8(v_s_952_, sizeof(void*)*3 + 2);
v_isExported_958_ = lean_ctor_get_uint8(v_s_952_, sizeof(void*)*3 + 3);
v_importAll_959_ = lean_ctor_get_uint8(v_s_952_, sizeof(void*)*3 + 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v_s_952_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; 
v_unused_967_ = lean_ctor_get(v_s_952_, 2);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_s_952_, 1);
lean_dec(v_unused_968_);
v___x_961_ = v_s_952_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_imports_954_);
lean_dec(v_s_952_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_pos_951_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_imports_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_pos_951_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_error_x3f_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*3, v_badModifier_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*3 + 1, v_isModule_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*3 + 2, v_isMeta_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*3 + 3, v_isExported_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_965_, sizeof(void*)*3 + 4, v_importAll_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_dec(v_error_x3f_953_);
lean_dec(v_pos_951_);
return v_s_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* v_p_972_, lean_object* v_input_973_, lean_object* v_s_974_){
_start:
{
lean_object* v_pos_975_; lean_object* v_s_976_; lean_object* v_error_x3f_977_; 
v_pos_975_ = lean_ctor_get(v_s_974_, 1);
lean_inc(v_pos_975_);
lean_inc_ref(v_p_972_);
lean_inc_ref(v_input_973_);
v_s_976_ = lean_apply_2(v_p_972_, v_input_973_, v_s_974_);
v_error_x3f_977_ = lean_ctor_get(v_s_976_, 2);
lean_inc(v_error_x3f_977_);
if (lean_obj_tag(v_error_x3f_977_) == 1)
{
lean_object* v_imports_978_; lean_object* v_pos_979_; uint8_t v_isModule_980_; uint8_t v_isMeta_981_; uint8_t v_isExported_982_; uint8_t v_importAll_983_; uint8_t v_decide_984_; 
lean_dec_ref_known(v_error_x3f_977_, 1);
lean_dec_ref(v_input_973_);
lean_dec_ref(v_p_972_);
v_imports_978_ = lean_ctor_get(v_s_976_, 0);
lean_inc_ref(v_imports_978_);
v_pos_979_ = lean_ctor_get(v_s_976_, 1);
lean_inc(v_pos_979_);
v_isModule_980_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 1);
v_isMeta_981_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 2);
v_isExported_982_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 3);
v_importAll_983_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 4);
v_decide_984_ = lean_nat_dec_eq(v_pos_979_, v_pos_975_);
lean_dec(v_pos_975_);
if (v_decide_984_ == 0)
{
lean_dec(v_pos_979_);
lean_dec_ref(v_imports_978_);
return v_s_976_;
}
else
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
v_isSharedCheck_993_ = !lean_is_exclusive(v_s_976_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_994_ = lean_ctor_get(v_s_976_, 2);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_s_976_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_s_976_, 0);
lean_dec(v_unused_996_);
v___x_986_ = v_s_976_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_dec(v_s_976_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_988_ = 0;
v___x_989_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 2, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_imports_978_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_pos_979_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3 + 1, v_isModule_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3 + 2, v_isMeta_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3 + 3, v_isExported_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3 + 4, v_importAll_983_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*3, v___x_988_);
return v___x_991_;
}
}
}
}
else
{
uint8_t v_badModifier_997_; 
lean_dec(v_error_x3f_977_);
v_badModifier_997_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3);
if (v_badModifier_997_ == 0)
{
lean_dec(v_pos_975_);
v_s_974_ = v_s_976_;
goto _start;
}
else
{
lean_object* v_imports_999_; uint8_t v_isModule_1000_; uint8_t v_isMeta_1001_; uint8_t v_isExported_1002_; uint8_t v_importAll_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_input_973_);
lean_dec_ref(v_p_972_);
v_imports_999_ = lean_ctor_get(v_s_976_, 0);
v_isModule_1000_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 1);
v_isMeta_1001_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 2);
v_isExported_1002_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 3);
v_importAll_1003_ = lean_ctor_get_uint8(v_s_976_, sizeof(void*)*3 + 4);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_s_976_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; lean_object* v_unused_1014_; 
v_unused_1013_ = lean_ctor_get(v_s_976_, 2);
lean_dec(v_unused_1013_);
v_unused_1014_ = lean_ctor_get(v_s_976_, 1);
lean_dec(v_unused_1014_);
v___x_1005_ = v_s_976_;
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_imports_999_);
lean_dec(v_s_976_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = 0;
v___x_1008_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 2, v___x_1008_);
lean_ctor_set(v___x_1005_, 1, v_pos_975_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_imports_999_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_pos_975_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v___x_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1011_, sizeof(void*)*3 + 1, v_isModule_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1011_, sizeof(void*)*3 + 2, v_isMeta_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1011_, sizeof(void*)*3 + 3, v_isExported_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1011_, sizeof(void*)*3 + 4, v_importAll_1003_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*3, v___x_1007_);
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t v_isModule_1015_, lean_object* v_s_1016_){
_start:
{
if (v_isModule_1015_ == 0)
{
lean_object* v_imports_1017_; lean_object* v_pos_1018_; uint8_t v_badModifier_1019_; lean_object* v_error_x3f_1020_; uint8_t v_isMeta_1021_; uint8_t v_importAll_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_imports_1017_ = lean_ctor_get(v_s_1016_, 0);
v_pos_1018_ = lean_ctor_get(v_s_1016_, 1);
v_badModifier_1019_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3);
v_error_x3f_1020_ = lean_ctor_get(v_s_1016_, 2);
v_isMeta_1021_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3 + 2);
v_importAll_1022_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3 + 4);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_s_1016_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_error_x3f_1020_);
lean_inc(v_pos_1018_);
lean_inc(v_imports_1017_);
lean_dec(v_s_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
uint8_t v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = 1;
if (v_isShared_1025_ == 0)
{
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_imports_1017_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_pos_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_error_x3f_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1029_, sizeof(void*)*3, v_badModifier_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1029_, sizeof(void*)*3 + 2, v_isMeta_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1029_, sizeof(void*)*3 + 4, v_importAll_1022_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*3 + 1, v_isModule_1015_);
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*3 + 3, v___x_1026_);
return v___x_1028_;
}
}
}
else
{
lean_object* v_imports_1031_; lean_object* v_pos_1032_; uint8_t v_badModifier_1033_; lean_object* v_error_x3f_1034_; uint8_t v_isMeta_1035_; uint8_t v_importAll_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_imports_1031_ = lean_ctor_get(v_s_1016_, 0);
v_pos_1032_ = lean_ctor_get(v_s_1016_, 1);
v_badModifier_1033_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3);
v_error_x3f_1034_ = lean_ctor_get(v_s_1016_, 2);
v_isMeta_1035_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3 + 2);
v_importAll_1036_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*3 + 4);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_s_1016_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_error_x3f_1034_);
lean_inc(v_pos_1032_);
lean_inc(v_imports_1031_);
lean_dec(v_s_1016_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = 0;
if (v_isShared_1039_ == 0)
{
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_imports_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_pos_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_error_x3f_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*3, v_badModifier_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*3 + 2, v_isMeta_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*3 + 4, v_importAll_1036_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*3 + 1, v_isModule_1015_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*3 + 3, v___x_1040_);
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* v_isModule_1045_, lean_object* v_s_1046_){
_start:
{
uint8_t v_isModule_boxed_1047_; lean_object* v_res_1048_; 
v_isModule_boxed_1047_ = lean_unbox(v_isModule_1045_);
v_res_1048_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_1047_, v_s_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t v_isModule_1049_, lean_object* v_x_1050_, lean_object* v_s_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_1049_, v_s_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* v_isModule_1053_, lean_object* v_x_1054_, lean_object* v_s_1055_){
_start:
{
uint8_t v_isModule_boxed_1056_; lean_object* v_res_1057_; 
v_isModule_boxed_1056_ = lean_unbox(v_isModule_1053_);
v_res_1057_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_1056_, v_x_1054_, v_s_1055_);
lean_dec_ref(v_x_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* v_s_1058_){
_start:
{
lean_object* v_imports_1059_; lean_object* v_pos_1060_; uint8_t v_badModifier_1061_; lean_object* v_error_x3f_1062_; uint8_t v_isModule_1063_; uint8_t v_isMeta_1064_; uint8_t v_isExported_1065_; uint8_t v_importAll_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
v_imports_1059_ = lean_ctor_get(v_s_1058_, 0);
v_pos_1060_ = lean_ctor_get(v_s_1058_, 1);
v_badModifier_1061_ = lean_ctor_get_uint8(v_s_1058_, sizeof(void*)*3);
v_error_x3f_1062_ = lean_ctor_get(v_s_1058_, 2);
v_isModule_1063_ = lean_ctor_get_uint8(v_s_1058_, sizeof(void*)*3 + 1);
v_isMeta_1064_ = lean_ctor_get_uint8(v_s_1058_, sizeof(void*)*3 + 2);
v_isExported_1065_ = lean_ctor_get_uint8(v_s_1058_, sizeof(void*)*3 + 3);
v_importAll_1066_ = lean_ctor_get_uint8(v_s_1058_, sizeof(void*)*3 + 4);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_s_1058_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1068_ = v_s_1058_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_error_x3f_1062_);
lean_inc(v_pos_1060_);
lean_inc(v_imports_1059_);
lean_dec(v_s_1058_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; 
v___x_1070_ = 1;
if (v_isModule_1063_ == 0)
{
lean_object* v___x_1072_; 
if (v_isShared_1069_ == 0)
{
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_imports_1059_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_pos_1060_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_error_x3f_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*3 + 1, v_isModule_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*3 + 2, v_isMeta_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*3 + 3, v_isExported_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*3 + 4, v_importAll_1066_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*3, v___x_1070_);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1075_; 
if (v_isShared_1069_ == 0)
{
v___x_1075_ = v___x_1068_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_imports_1059_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_pos_1060_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_error_x3f_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*3, v_badModifier_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*3 + 1, v_isModule_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*3 + 3, v_isExported_1065_);
lean_ctor_set_uint8(v_reuseFailAlloc_1076_, sizeof(void*)*3 + 4, v_importAll_1066_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*3 + 2, v___x_1070_);
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* v_x_1078_, lean_object* v_s_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_ParseImports_setMeta___redArg(v_s_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* v_x_1081_, lean_object* v_s_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_ParseImports_setMeta(v_x_1081_, v_s_1082_);
lean_dec_ref(v_x_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* v_s_1084_){
_start:
{
lean_object* v_imports_1085_; lean_object* v_pos_1086_; uint8_t v_badModifier_1087_; lean_object* v_error_x3f_1088_; uint8_t v_isModule_1089_; uint8_t v_isMeta_1090_; uint8_t v_isExported_1091_; uint8_t v_importAll_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1103_; 
v_imports_1085_ = lean_ctor_get(v_s_1084_, 0);
v_pos_1086_ = lean_ctor_get(v_s_1084_, 1);
v_badModifier_1087_ = lean_ctor_get_uint8(v_s_1084_, sizeof(void*)*3);
v_error_x3f_1088_ = lean_ctor_get(v_s_1084_, 2);
v_isModule_1089_ = lean_ctor_get_uint8(v_s_1084_, sizeof(void*)*3 + 1);
v_isMeta_1090_ = lean_ctor_get_uint8(v_s_1084_, sizeof(void*)*3 + 2);
v_isExported_1091_ = lean_ctor_get_uint8(v_s_1084_, sizeof(void*)*3 + 3);
v_importAll_1092_ = lean_ctor_get_uint8(v_s_1084_, sizeof(void*)*3 + 4);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_s_1084_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1094_ = v_s_1084_;
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_error_x3f_1088_);
lean_inc(v_pos_1086_);
lean_inc(v_imports_1085_);
lean_dec(v_s_1084_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = 1;
if (v_isModule_1089_ == 0)
{
lean_object* v___x_1098_; 
if (v_isShared_1095_ == 0)
{
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_imports_1085_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_pos_1086_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_error_x3f_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*3 + 1, v_isModule_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*3 + 2, v_isMeta_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*3 + 3, v_isExported_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*3 + 4, v_importAll_1092_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*3, v___x_1096_);
return v___x_1098_;
}
}
else
{
lean_object* v___x_1101_; 
if (v_isShared_1095_ == 0)
{
v___x_1101_ = v___x_1094_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_imports_1085_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_pos_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_error_x3f_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3, v_badModifier_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3 + 1, v_isModule_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3 + 2, v_isMeta_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3 + 4, v_importAll_1092_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*3 + 3, v___x_1096_);
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* v_x_1104_, lean_object* v_s_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_ParseImports_setExported___redArg(v_s_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* v_x_1107_, lean_object* v_s_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_ParseImports_setExported(v_x_1107_, v_s_1108_);
lean_dec_ref(v_x_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* v_s_1110_){
_start:
{
lean_object* v_imports_1111_; lean_object* v_pos_1112_; uint8_t v_badModifier_1113_; lean_object* v_error_x3f_1114_; uint8_t v_isModule_1115_; uint8_t v_isMeta_1116_; uint8_t v_isExported_1117_; uint8_t v_importAll_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1129_; 
v_imports_1111_ = lean_ctor_get(v_s_1110_, 0);
v_pos_1112_ = lean_ctor_get(v_s_1110_, 1);
v_badModifier_1113_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*3);
v_error_x3f_1114_ = lean_ctor_get(v_s_1110_, 2);
v_isModule_1115_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*3 + 1);
v_isMeta_1116_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*3 + 2);
v_isExported_1117_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*3 + 3);
v_importAll_1118_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*3 + 4);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_s_1110_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1120_ = v_s_1110_;
v_isShared_1121_ = v_isSharedCheck_1129_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_error_x3f_1114_);
lean_inc(v_pos_1112_);
lean_inc(v_imports_1111_);
lean_dec(v_s_1110_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1129_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = 1;
if (v_isModule_1115_ == 0)
{
lean_object* v___x_1124_; 
if (v_isShared_1121_ == 0)
{
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_imports_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_pos_1112_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_error_x3f_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3 + 1, v_isModule_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3 + 2, v_isMeta_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3 + 3, v_isExported_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3 + 4, v_importAll_1118_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*3, v___x_1122_);
return v___x_1124_;
}
}
else
{
lean_object* v___x_1127_; 
if (v_isShared_1121_ == 0)
{
v___x_1127_ = v___x_1120_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_imports_1111_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_pos_1112_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_error_x3f_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*3, v_badModifier_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*3 + 1, v_isModule_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*3 + 2, v_isMeta_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*3 + 3, v_isExported_1117_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3 + 4, v___x_1122_);
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* v_x_1130_, lean_object* v_s_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_ParseImports_setImportAll___redArg(v_s_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* v_x_1133_, lean_object* v_s_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_ParseImports_setImportAll(v_x_1133_, v_s_1134_);
lean_dec_ref(v_x_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* v_k_1139_, lean_object* v_input_1140_, lean_object* v_s_1141_, lean_object* v_i_1142_, lean_object* v_j_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_string_utf8_at_end(v_k_1139_, v_i_1142_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; lean_object* v_s_1147_; uint8_t v___x_1153_; 
v___x_1145_ = 1;
v___x_1153_ = lean_string_utf8_at_end(v_input_1140_, v_j_1143_);
if (v___x_1153_ == 0)
{
uint32_t v_curr_u2081_1154_; uint32_t v_curr_u2082_1155_; uint8_t v___x_1156_; 
v_curr_u2081_1154_ = lean_string_utf8_get_fast(v_k_1139_, v_i_1142_);
v_curr_u2082_1155_ = lean_string_utf8_get_fast(v_input_1140_, v_j_1143_);
v___x_1156_ = lean_uint32_dec_eq(v_curr_u2081_1154_, v_curr_u2082_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v_j_1143_);
lean_dec(v_i_1142_);
v_s_1147_ = v_s_1141_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_string_utf8_next_fast(v_k_1139_, v_i_1142_);
lean_dec(v_i_1142_);
v___x_1158_ = lean_string_utf8_next_fast(v_input_1140_, v_j_1143_);
lean_dec(v_j_1143_);
v_i_1142_ = v___x_1157_;
v_j_1143_ = v___x_1158_;
goto _start;
}
}
else
{
lean_dec(v_j_1143_);
lean_dec(v_i_1142_);
v_s_1147_ = v_s_1141_;
goto v___jp_1146_;
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
v___x_1149_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*1, v___x_1144_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*1 + 1, v___x_1145_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*1 + 2, v___x_1145_);
v___x_1150_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*1, v___x_1144_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*1 + 1, v___x_1145_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*1 + 2, v___x_1144_);
v___x_1151_ = l_Lean_ParseImports_State_pushImport(v___x_1150_, v_s_1147_);
v___x_1152_ = l_Lean_ParseImports_State_pushImport(v___x_1149_, v___x_1151_);
return v___x_1152_;
}
}
else
{
lean_object* v_imports_1160_; uint8_t v_badModifier_1161_; lean_object* v_error_x3f_1162_; uint8_t v_isModule_1163_; uint8_t v_isMeta_1164_; uint8_t v_isExported_1165_; uint8_t v_importAll_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_i_1142_);
v_imports_1160_ = lean_ctor_get(v_s_1141_, 0);
v_badModifier_1161_ = lean_ctor_get_uint8(v_s_1141_, sizeof(void*)*3);
v_error_x3f_1162_ = lean_ctor_get(v_s_1141_, 2);
v_isModule_1163_ = lean_ctor_get_uint8(v_s_1141_, sizeof(void*)*3 + 1);
v_isMeta_1164_ = lean_ctor_get_uint8(v_s_1141_, sizeof(void*)*3 + 2);
v_isExported_1165_ = lean_ctor_get_uint8(v_s_1141_, sizeof(void*)*3 + 3);
v_importAll_1166_ = lean_ctor_get_uint8(v_s_1141_, sizeof(void*)*3 + 4);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_s_1141_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_s_1141_, 1);
lean_dec(v_unused_1175_);
v___x_1168_ = v_s_1141_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_error_x3f_1162_);
lean_inc(v_imports_1160_);
lean_dec(v_s_1141_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_j_1143_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_imports_1160_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_j_1143_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_error_x3f_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3, v_badModifier_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3 + 1, v_isModule_1163_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3 + 2, v_isMeta_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3 + 3, v_isExported_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3 + 4, v_importAll_1166_);
v___x_1171_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_ParseImports_whitespace(v_input_1140_, v___x_1171_);
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* v_k_1176_, lean_object* v_input_1177_, lean_object* v_s_1178_, lean_object* v_i_1179_, lean_object* v_j_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_1176_, v_input_1177_, v_s_1178_, v_i_1179_, v_j_1180_);
lean_dec_ref(v_input_1177_);
lean_dec_ref(v_k_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* v_k_1185_, lean_object* v_input_1186_, lean_object* v_s_1187_, lean_object* v_i_1188_, lean_object* v_j_1189_){
_start:
{
lean_object* v_s_1191_; uint8_t v___x_1208_; 
v___x_1208_ = lean_string_utf8_at_end(v_k_1185_, v_i_1188_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_string_utf8_at_end(v_input_1186_, v_j_1189_);
if (v___x_1209_ == 0)
{
uint32_t v_curr_u2081_1210_; uint32_t v_curr_u2082_1211_; uint8_t v___x_1212_; 
v_curr_u2081_1210_ = lean_string_utf8_get_fast(v_k_1185_, v_i_1188_);
v_curr_u2082_1211_ = lean_string_utf8_get_fast(v_input_1186_, v_j_1189_);
v___x_1212_ = lean_uint32_dec_eq(v_curr_u2081_1210_, v_curr_u2082_1211_);
if (v___x_1212_ == 0)
{
lean_dec(v_j_1189_);
lean_dec(v_i_1188_);
v_s_1191_ = v_s_1187_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_string_utf8_next_fast(v_k_1185_, v_i_1188_);
lean_dec(v_i_1188_);
v___x_1214_ = lean_string_utf8_next_fast(v_input_1186_, v_j_1189_);
lean_dec(v_j_1189_);
v_i_1188_ = v___x_1213_;
v_j_1189_ = v___x_1214_;
goto _start;
}
}
else
{
lean_dec(v_j_1189_);
lean_dec(v_i_1188_);
v_s_1191_ = v_s_1187_;
goto v___jp_1190_;
}
}
else
{
lean_object* v_imports_1216_; uint8_t v_badModifier_1217_; lean_object* v_error_x3f_1218_; uint8_t v_isModule_1219_; uint8_t v_isMeta_1220_; uint8_t v_isExported_1221_; uint8_t v_importAll_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_i_1188_);
v_imports_1216_ = lean_ctor_get(v_s_1187_, 0);
v_badModifier_1217_ = lean_ctor_get_uint8(v_s_1187_, sizeof(void*)*3);
v_error_x3f_1218_ = lean_ctor_get(v_s_1187_, 2);
v_isModule_1219_ = lean_ctor_get_uint8(v_s_1187_, sizeof(void*)*3 + 1);
v_isMeta_1220_ = lean_ctor_get_uint8(v_s_1187_, sizeof(void*)*3 + 2);
v_isExported_1221_ = lean_ctor_get_uint8(v_s_1187_, sizeof(void*)*3 + 3);
v_importAll_1222_ = lean_ctor_get_uint8(v_s_1187_, sizeof(void*)*3 + 4);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_s_1187_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_s_1187_, 1);
lean_dec(v_unused_1231_);
v___x_1224_ = v_s_1187_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_error_x3f_1218_);
lean_inc(v_imports_1216_);
lean_dec(v_s_1187_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_j_1189_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_imports_1216_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_j_1189_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_error_x3f_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*3, v_badModifier_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*3 + 1, v_isModule_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*3 + 2, v_isMeta_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*3 + 3, v_isExported_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*3 + 4, v_importAll_1222_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_ParseImports_whitespace(v_input_1186_, v___x_1227_);
return v___x_1228_;
}
}
}
v___jp_1190_:
{
lean_object* v_imports_1192_; lean_object* v_pos_1193_; uint8_t v_badModifier_1194_; uint8_t v_isModule_1195_; uint8_t v_isMeta_1196_; uint8_t v_isExported_1197_; uint8_t v_importAll_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1206_; 
v_imports_1192_ = lean_ctor_get(v_s_1191_, 0);
v_pos_1193_ = lean_ctor_get(v_s_1191_, 1);
v_badModifier_1194_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*3);
v_isModule_1195_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*3 + 1);
v_isMeta_1196_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*3 + 2);
v_isExported_1197_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*3 + 3);
v_importAll_1198_ = lean_ctor_get_uint8(v_s_1191_, sizeof(void*)*3 + 4);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_s_1191_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v_s_1191_, 2);
lean_dec(v_unused_1207_);
v___x_1200_ = v_s_1191_;
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_pos_1193_);
lean_inc(v_imports_1192_);
lean_dec(v_s_1191_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 2, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_imports_1192_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_pos_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*3, v_badModifier_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*3 + 1, v_isModule_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*3 + 2, v_isMeta_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*3 + 3, v_isExported_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*3 + 4, v_importAll_1198_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* v_k_1232_, lean_object* v_input_1233_, lean_object* v_s_1234_, lean_object* v_i_1235_, lean_object* v_j_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_1232_, v_input_1233_, v_s_1234_, v_i_1235_, v_j_1236_);
lean_dec_ref(v_input_1233_);
lean_dec_ref(v_k_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* v_k_1238_, lean_object* v_input_1239_, lean_object* v_s_1240_, lean_object* v_i_1241_, lean_object* v_j_1242_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_string_utf8_at_end(v_k_1238_, v_i_1241_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_string_utf8_at_end(v_input_1239_, v_j_1242_);
if (v___x_1244_ == 0)
{
uint32_t v_curr_u2081_1245_; uint32_t v_curr_u2082_1246_; uint8_t v___x_1247_; 
v_curr_u2081_1245_ = lean_string_utf8_get_fast(v_k_1238_, v_i_1241_);
v_curr_u2082_1246_ = lean_string_utf8_get_fast(v_input_1239_, v_j_1242_);
v___x_1247_ = lean_uint32_dec_eq(v_curr_u2081_1245_, v_curr_u2082_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v_j_1242_);
lean_dec(v_i_1241_);
return v_s_1240_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_string_utf8_next_fast(v_k_1238_, v_i_1241_);
lean_dec(v_i_1241_);
v___x_1249_ = lean_string_utf8_next_fast(v_input_1239_, v_j_1242_);
lean_dec(v_j_1242_);
v_i_1241_ = v___x_1248_;
v_j_1242_ = v___x_1249_;
goto _start;
}
}
else
{
lean_dec(v_j_1242_);
lean_dec(v_i_1241_);
return v_s_1240_;
}
}
else
{
lean_object* v_imports_1251_; uint8_t v_badModifier_1252_; lean_object* v_error_x3f_1253_; uint8_t v_isModule_1254_; uint8_t v_isMeta_1255_; uint8_t v_isExported_1256_; uint8_t v_importAll_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_i_1241_);
v_imports_1251_ = lean_ctor_get(v_s_1240_, 0);
v_badModifier_1252_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*3);
v_error_x3f_1253_ = lean_ctor_get(v_s_1240_, 2);
v_isModule_1254_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*3 + 1);
v_isMeta_1255_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*3 + 2);
v_isExported_1256_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*3 + 3);
v_importAll_1257_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*3 + 4);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_s_1240_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_s_1240_, 1);
lean_dec(v_unused_1267_);
v___x_1259_ = v_s_1240_;
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_error_x3f_1253_);
lean_inc(v_imports_1251_);
lean_dec(v_s_1240_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_j_1242_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_imports_1251_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_j_1242_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_error_x3f_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3, v_badModifier_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 1, v_isModule_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 2, v_isMeta_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 3, v_isExported_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 4, v_importAll_1257_);
v___x_1262_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = l_Lean_ParseImports_whitespace(v_input_1239_, v___x_1262_);
v___x_1264_ = l_Lean_ParseImports_setImportAll___redArg(v___x_1263_);
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* v_k_1268_, lean_object* v_input_1269_, lean_object* v_s_1270_, lean_object* v_i_1271_, lean_object* v_j_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_1268_, v_input_1269_, v_s_1270_, v_i_1271_, v_j_1272_);
lean_dec_ref(v_input_1269_);
lean_dec_ref(v_k_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* v_k_1274_, lean_object* v_input_1275_, lean_object* v_s_1276_, lean_object* v_i_1277_, lean_object* v_j_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_string_utf8_at_end(v_k_1274_, v_i_1277_);
if (v___x_1279_ == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_string_utf8_at_end(v_input_1275_, v_j_1278_);
if (v___x_1280_ == 0)
{
uint32_t v_curr_u2081_1281_; uint32_t v_curr_u2082_1282_; uint8_t v___x_1283_; 
v_curr_u2081_1281_ = lean_string_utf8_get_fast(v_k_1274_, v_i_1277_);
v_curr_u2082_1282_ = lean_string_utf8_get_fast(v_input_1275_, v_j_1278_);
v___x_1283_ = lean_uint32_dec_eq(v_curr_u2081_1281_, v_curr_u2082_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v_j_1278_);
lean_dec(v_i_1277_);
return v_s_1276_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_string_utf8_next_fast(v_k_1274_, v_i_1277_);
lean_dec(v_i_1277_);
v___x_1285_ = lean_string_utf8_next_fast(v_input_1275_, v_j_1278_);
lean_dec(v_j_1278_);
v_i_1277_ = v___x_1284_;
v_j_1278_ = v___x_1285_;
goto _start;
}
}
else
{
lean_dec(v_j_1278_);
lean_dec(v_i_1277_);
return v_s_1276_;
}
}
else
{
lean_object* v_imports_1287_; uint8_t v_badModifier_1288_; lean_object* v_error_x3f_1289_; uint8_t v_isModule_1290_; uint8_t v_isMeta_1291_; uint8_t v_isExported_1292_; uint8_t v_importAll_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_i_1277_);
v_imports_1287_ = lean_ctor_get(v_s_1276_, 0);
v_badModifier_1288_ = lean_ctor_get_uint8(v_s_1276_, sizeof(void*)*3);
v_error_x3f_1289_ = lean_ctor_get(v_s_1276_, 2);
v_isModule_1290_ = lean_ctor_get_uint8(v_s_1276_, sizeof(void*)*3 + 1);
v_isMeta_1291_ = lean_ctor_get_uint8(v_s_1276_, sizeof(void*)*3 + 2);
v_isExported_1292_ = lean_ctor_get_uint8(v_s_1276_, sizeof(void*)*3 + 3);
v_importAll_1293_ = lean_ctor_get_uint8(v_s_1276_, sizeof(void*)*3 + 4);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_s_1276_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_s_1276_, 1);
lean_dec(v_unused_1303_);
v___x_1295_ = v_s_1276_;
v_isShared_1296_ = v_isSharedCheck_1302_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_error_x3f_1289_);
lean_inc(v_imports_1287_);
lean_dec(v_s_1276_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1302_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v_j_1278_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_imports_1287_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_j_1278_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_error_x3f_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*3, v_badModifier_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*3 + 1, v_isModule_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*3 + 2, v_isMeta_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*3 + 3, v_isExported_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, sizeof(void*)*3 + 4, v_importAll_1293_);
v___x_1298_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = l_Lean_ParseImports_whitespace(v_input_1275_, v___x_1298_);
v___x_1300_ = l_Lean_ParseImports_setExported___redArg(v___x_1299_);
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* v_k_1304_, lean_object* v_input_1305_, lean_object* v_s_1306_, lean_object* v_i_1307_, lean_object* v_j_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_1304_, v_input_1305_, v_s_1306_, v_i_1307_, v_j_1308_);
lean_dec_ref(v_input_1305_);
lean_dec_ref(v_k_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* v_k_1310_, lean_object* v_input_1311_, lean_object* v_s_1312_, lean_object* v_i_1313_, lean_object* v_j_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_string_utf8_at_end(v_k_1310_, v_i_1313_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_string_utf8_at_end(v_input_1311_, v_j_1314_);
if (v___x_1316_ == 0)
{
uint32_t v_curr_u2081_1317_; uint32_t v_curr_u2082_1318_; uint8_t v___x_1319_; 
v_curr_u2081_1317_ = lean_string_utf8_get_fast(v_k_1310_, v_i_1313_);
v_curr_u2082_1318_ = lean_string_utf8_get_fast(v_input_1311_, v_j_1314_);
v___x_1319_ = lean_uint32_dec_eq(v_curr_u2081_1317_, v_curr_u2082_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v_j_1314_);
lean_dec(v_i_1313_);
return v_s_1312_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_string_utf8_next_fast(v_k_1310_, v_i_1313_);
lean_dec(v_i_1313_);
v___x_1321_ = lean_string_utf8_next_fast(v_input_1311_, v_j_1314_);
lean_dec(v_j_1314_);
v_i_1313_ = v___x_1320_;
v_j_1314_ = v___x_1321_;
goto _start;
}
}
else
{
lean_dec(v_j_1314_);
lean_dec(v_i_1313_);
return v_s_1312_;
}
}
else
{
lean_object* v_imports_1323_; uint8_t v_badModifier_1324_; lean_object* v_error_x3f_1325_; uint8_t v_isModule_1326_; uint8_t v_isMeta_1327_; uint8_t v_isExported_1328_; uint8_t v_importAll_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_i_1313_);
v_imports_1323_ = lean_ctor_get(v_s_1312_, 0);
v_badModifier_1324_ = lean_ctor_get_uint8(v_s_1312_, sizeof(void*)*3);
v_error_x3f_1325_ = lean_ctor_get(v_s_1312_, 2);
v_isModule_1326_ = lean_ctor_get_uint8(v_s_1312_, sizeof(void*)*3 + 1);
v_isMeta_1327_ = lean_ctor_get_uint8(v_s_1312_, sizeof(void*)*3 + 2);
v_isExported_1328_ = lean_ctor_get_uint8(v_s_1312_, sizeof(void*)*3 + 3);
v_importAll_1329_ = lean_ctor_get_uint8(v_s_1312_, sizeof(void*)*3 + 4);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_s_1312_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_s_1312_, 1);
lean_dec(v_unused_1339_);
v___x_1331_ = v_s_1312_;
v_isShared_1332_ = v_isSharedCheck_1338_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_error_x3f_1325_);
lean_inc(v_imports_1323_);
lean_dec(v_s_1312_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1338_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_j_1314_);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_imports_1323_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_j_1314_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_error_x3f_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*3, v_badModifier_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*3 + 1, v_isModule_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*3 + 2, v_isMeta_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*3 + 3, v_isExported_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*3 + 4, v_importAll_1329_);
v___x_1334_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = l_Lean_ParseImports_whitespace(v_input_1311_, v___x_1334_);
v___x_1336_ = l_Lean_ParseImports_setMeta___redArg(v___x_1335_);
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* v_k_1340_, lean_object* v_input_1341_, lean_object* v_s_1342_, lean_object* v_i_1343_, lean_object* v_j_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_1340_, v_input_1341_, v_s_1342_, v_i_1343_, v_j_1344_);
lean_dec_ref(v_input_1341_);
lean_dec_ref(v_k_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* v_input_1350_, lean_object* v_s_1351_){
_start:
{
lean_object* v_pos_1352_; lean_object* v___y_1354_; lean_object* v_imports_1355_; lean_object* v_pos_1356_; uint8_t v_isModule_1357_; uint8_t v_isMeta_1358_; uint8_t v_isExported_1359_; uint8_t v_importAll_1360_; lean_object* v_imports_1366_; uint8_t v_badModifier_1367_; lean_object* v_error_x3f_1368_; uint8_t v_isModule_1369_; uint8_t v_isMeta_1370_; uint8_t v_isExported_1371_; uint8_t v_importAll_1372_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_error_x3f_1377_; 
v_pos_1352_ = lean_ctor_get(v_s_1351_, 1);
lean_inc_n(v_pos_1352_, 2);
v___x_1374_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_1374_, v_input_1350_, v_s_1351_, v___x_1375_, v_pos_1352_);
v_error_x3f_1377_ = lean_ctor_get(v___x_1376_, 2);
if (lean_obj_tag(v_error_x3f_1377_) == 1)
{
lean_object* v_imports_1378_; uint8_t v_badModifier_1379_; uint8_t v_isModule_1380_; uint8_t v_isMeta_1381_; uint8_t v_isExported_1382_; uint8_t v_importAll_1383_; 
lean_inc_ref(v_error_x3f_1377_);
lean_dec_ref(v_input_1350_);
v_imports_1378_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_imports_1378_);
v_badModifier_1379_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*3);
v_isModule_1380_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*3 + 1);
v_isMeta_1381_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*3 + 2);
v_isExported_1382_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*3 + 3);
v_importAll_1383_ = lean_ctor_get_uint8(v___x_1376_, sizeof(void*)*3 + 4);
lean_dec_ref(v___x_1376_);
v_imports_1366_ = v_imports_1378_;
v_badModifier_1367_ = v_badModifier_1379_;
v_error_x3f_1368_ = v_error_x3f_1377_;
v_isModule_1369_ = v_isModule_1380_;
v_isMeta_1370_ = v_isMeta_1381_;
v_isExported_1371_ = v_isExported_1382_;
v_importAll_1372_ = v_importAll_1383_;
goto v___jp_1365_;
}
else
{
lean_object* v_pos_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_error_x3f_1387_; 
v_pos_1384_ = lean_ctor_get(v___x_1376_, 1);
lean_inc(v_pos_1384_);
v___x_1385_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
v___x_1386_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_1385_, v_input_1350_, v___x_1376_, v___x_1375_, v_pos_1384_);
v_error_x3f_1387_ = lean_ctor_get(v___x_1386_, 2);
if (lean_obj_tag(v_error_x3f_1387_) == 1)
{
lean_object* v_imports_1388_; uint8_t v_badModifier_1389_; uint8_t v_isModule_1390_; uint8_t v_isMeta_1391_; uint8_t v_isExported_1392_; uint8_t v_importAll_1393_; 
lean_inc_ref(v_error_x3f_1387_);
lean_dec_ref(v_input_1350_);
v_imports_1388_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_ref(v_imports_1388_);
v_badModifier_1389_ = lean_ctor_get_uint8(v___x_1386_, sizeof(void*)*3);
v_isModule_1390_ = lean_ctor_get_uint8(v___x_1386_, sizeof(void*)*3 + 1);
v_isMeta_1391_ = lean_ctor_get_uint8(v___x_1386_, sizeof(void*)*3 + 2);
v_isExported_1392_ = lean_ctor_get_uint8(v___x_1386_, sizeof(void*)*3 + 3);
v_importAll_1393_ = lean_ctor_get_uint8(v___x_1386_, sizeof(void*)*3 + 4);
lean_dec_ref(v___x_1386_);
v_imports_1366_ = v_imports_1388_;
v_badModifier_1367_ = v_badModifier_1389_;
v_error_x3f_1368_ = v_error_x3f_1387_;
v_isModule_1369_ = v_isModule_1390_;
v_isMeta_1370_ = v_isMeta_1391_;
v_isExported_1371_ = v_isExported_1392_;
v_importAll_1372_ = v_importAll_1393_;
goto v___jp_1365_;
}
else
{
lean_object* v_pos_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_error_x3f_1397_; 
v_pos_1394_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_pos_1394_);
v___x_1395_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
v___x_1396_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_1395_, v_input_1350_, v___x_1386_, v___x_1375_, v_pos_1394_);
v_error_x3f_1397_ = lean_ctor_get(v___x_1396_, 2);
if (lean_obj_tag(v_error_x3f_1397_) == 1)
{
lean_object* v_imports_1398_; uint8_t v_badModifier_1399_; uint8_t v_isModule_1400_; uint8_t v_isMeta_1401_; uint8_t v_isExported_1402_; uint8_t v_importAll_1403_; 
lean_inc_ref(v_error_x3f_1397_);
lean_dec_ref(v_input_1350_);
v_imports_1398_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_imports_1398_);
v_badModifier_1399_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3);
v_isModule_1400_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 1);
v_isMeta_1401_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 2);
v_isExported_1402_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 3);
v_importAll_1403_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 4);
lean_dec_ref(v___x_1396_);
v_imports_1366_ = v_imports_1398_;
v_badModifier_1367_ = v_badModifier_1399_;
v_error_x3f_1368_ = v_error_x3f_1397_;
v_isModule_1369_ = v_isModule_1400_;
v_isMeta_1370_ = v_isMeta_1401_;
v_isExported_1371_ = v_isExported_1402_;
v_importAll_1372_ = v_importAll_1403_;
goto v___jp_1365_;
}
else
{
if (lean_obj_tag(v_error_x3f_1397_) == 1)
{
lean_object* v_imports_1404_; lean_object* v_pos_1405_; uint8_t v_isModule_1406_; uint8_t v_isMeta_1407_; uint8_t v_isExported_1408_; uint8_t v_importAll_1409_; 
lean_dec_ref(v_input_1350_);
v_imports_1404_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_imports_1404_);
v_pos_1405_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_pos_1405_);
v_isModule_1406_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 1);
v_isMeta_1407_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 2);
v_isExported_1408_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 3);
v_importAll_1409_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*3 + 4);
v___y_1354_ = v___x_1396_;
v_imports_1355_ = v_imports_1404_;
v_pos_1356_ = v_pos_1405_;
v_isModule_1357_ = v_isModule_1406_;
v_isMeta_1358_ = v_isMeta_1407_;
v_isExported_1359_ = v_isExported_1408_;
v_importAll_1360_ = v_importAll_1409_;
goto v___jp_1353_;
}
else
{
lean_object* v_pos_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_error_x3f_1413_; 
v_pos_1410_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_pos_1410_);
v___x_1411_ = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
v___x_1412_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_1411_, v_input_1350_, v___x_1396_, v___x_1375_, v_pos_1410_);
v_error_x3f_1413_ = lean_ctor_get(v___x_1412_, 2);
if (lean_obj_tag(v_error_x3f_1413_) == 1)
{
lean_object* v_imports_1414_; lean_object* v_pos_1415_; uint8_t v_isModule_1416_; uint8_t v_isMeta_1417_; uint8_t v_isExported_1418_; uint8_t v_importAll_1419_; 
lean_dec_ref(v_input_1350_);
v_imports_1414_ = lean_ctor_get(v___x_1412_, 0);
lean_inc_ref(v_imports_1414_);
v_pos_1415_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_pos_1415_);
v_isModule_1416_ = lean_ctor_get_uint8(v___x_1412_, sizeof(void*)*3 + 1);
v_isMeta_1417_ = lean_ctor_get_uint8(v___x_1412_, sizeof(void*)*3 + 2);
v_isExported_1418_ = lean_ctor_get_uint8(v___x_1412_, sizeof(void*)*3 + 3);
v_importAll_1419_ = lean_ctor_get_uint8(v___x_1412_, sizeof(void*)*3 + 4);
v___y_1354_ = v___x_1412_;
v_imports_1355_ = v_imports_1414_;
v_pos_1356_ = v_pos_1415_;
v_isModule_1357_ = v_isModule_1416_;
v_isMeta_1358_ = v_isMeta_1417_;
v_isExported_1359_ = v_isExported_1418_;
v_importAll_1360_ = v_importAll_1419_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1420_; lean_object* v_error_x3f_1421_; 
lean_inc_ref(v_input_1350_);
v___x_1420_ = l_Lean_ParseImports_moduleIdent(v_input_1350_, v___x_1412_);
v_error_x3f_1421_ = lean_ctor_get(v___x_1420_, 2);
if (lean_obj_tag(v_error_x3f_1421_) == 1)
{
lean_object* v_imports_1422_; lean_object* v_pos_1423_; uint8_t v_isModule_1424_; uint8_t v_isMeta_1425_; uint8_t v_isExported_1426_; uint8_t v_importAll_1427_; 
lean_dec_ref(v_input_1350_);
v_imports_1422_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_ref(v_imports_1422_);
v_pos_1423_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_pos_1423_);
v_isModule_1424_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 1);
v_isMeta_1425_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 2);
v_isExported_1426_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 3);
v_importAll_1427_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 4);
v___y_1354_ = v___x_1420_;
v_imports_1355_ = v_imports_1422_;
v_pos_1356_ = v_pos_1423_;
v_isModule_1357_ = v_isModule_1424_;
v_isMeta_1358_ = v_isMeta_1425_;
v_isExported_1359_ = v_isExported_1426_;
v_importAll_1360_ = v_importAll_1427_;
goto v___jp_1353_;
}
else
{
uint8_t v_badModifier_1428_; 
v_badModifier_1428_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3);
if (v_badModifier_1428_ == 0)
{
lean_dec(v_pos_1352_);
v_s_1351_ = v___x_1420_;
goto _start;
}
else
{
lean_object* v_imports_1430_; uint8_t v_isModule_1431_; uint8_t v_isMeta_1432_; uint8_t v_isExported_1433_; uint8_t v_importAll_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_input_1350_);
v_imports_1430_ = lean_ctor_get(v___x_1420_, 0);
v_isModule_1431_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 1);
v_isMeta_1432_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 2);
v_isExported_1433_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 3);
v_importAll_1434_ = lean_ctor_get_uint8(v___x_1420_, sizeof(void*)*3 + 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1444_ = lean_ctor_get(v___x_1420_, 2);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v___x_1420_, 1);
lean_dec(v_unused_1445_);
v___x_1436_ = v___x_1420_;
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_imports_1430_);
lean_dec(v___x_1420_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = 0;
v___x_1439_ = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 2, v___x_1439_);
lean_ctor_set(v___x_1436_, 1, v_pos_1352_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_imports_1430_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_pos_1352_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___x_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1442_, sizeof(void*)*3 + 1, v_isModule_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1442_, sizeof(void*)*3 + 2, v_isMeta_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1442_, sizeof(void*)*3 + 3, v_isExported_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1442_, sizeof(void*)*3 + 4, v_importAll_1434_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3, v___x_1438_);
return v___x_1441_;
}
}
}
}
}
}
}
}
}
v___jp_1353_:
{
uint8_t v_decide_1361_; 
v_decide_1361_ = lean_nat_dec_eq(v_pos_1356_, v_pos_1352_);
lean_dec(v_pos_1352_);
if (v_decide_1361_ == 0)
{
lean_dec(v_pos_1356_);
lean_dec_ref(v_imports_1355_);
return v___y_1354_;
}
else
{
uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v___y_1354_);
v___x_1362_ = 0;
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1364_, 0, v_imports_1355_);
lean_ctor_set(v___x_1364_, 1, v_pos_1356_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3, v___x_1362_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3 + 1, v_isModule_1357_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3 + 2, v_isMeta_1358_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3 + 3, v_isExported_1359_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3 + 4, v_importAll_1360_);
return v___x_1364_;
}
}
v___jp_1365_:
{
lean_object* v___x_1373_; 
lean_inc_n(v_pos_1352_, 2);
lean_inc_ref(v_imports_1366_);
v___x_1373_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1373_, 0, v_imports_1366_);
lean_ctor_set(v___x_1373_, 1, v_pos_1352_);
lean_ctor_set(v___x_1373_, 2, v_error_x3f_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v_badModifier_1367_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 1, v_isModule_1369_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 2, v_isMeta_1370_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 3, v_isExported_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 4, v_importAll_1372_);
v___y_1354_ = v___x_1373_;
v_imports_1355_ = v_imports_1366_;
v_pos_1356_ = v_pos_1352_;
v_isModule_1357_ = v_isModule_1369_;
v_isMeta_1358_ = v_isMeta_1370_;
v_isExported_1359_ = v_isExported_1371_;
v_importAll_1360_ = v_importAll_1372_;
goto v___jp_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* v_k_1446_, lean_object* v_input_1447_, lean_object* v_s_1448_, lean_object* v_i_1449_, lean_object* v_j_1450_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_string_utf8_at_end(v_k_1446_, v_i_1449_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_string_utf8_at_end(v_input_1447_, v_j_1450_);
if (v___x_1452_ == 0)
{
uint32_t v_curr_u2081_1453_; uint32_t v_curr_u2082_1454_; uint8_t v___x_1455_; 
v_curr_u2081_1453_ = lean_string_utf8_get_fast(v_k_1446_, v_i_1449_);
v_curr_u2082_1454_ = lean_string_utf8_get_fast(v_input_1447_, v_j_1450_);
v___x_1455_ = lean_uint32_dec_eq(v_curr_u2081_1453_, v_curr_u2082_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_j_1450_);
lean_dec(v_i_1449_);
v___x_1456_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1451_, v_s_1448_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_string_utf8_next_fast(v_k_1446_, v_i_1449_);
lean_dec(v_i_1449_);
v___x_1458_ = lean_string_utf8_next_fast(v_input_1447_, v_j_1450_);
lean_dec(v_j_1450_);
v_i_1449_ = v___x_1457_;
v_j_1450_ = v___x_1458_;
goto _start;
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_j_1450_);
lean_dec(v_i_1449_);
v___x_1460_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1451_, v_s_1448_);
return v___x_1460_;
}
}
else
{
lean_object* v_imports_1461_; uint8_t v_badModifier_1462_; lean_object* v_error_x3f_1463_; uint8_t v_isModule_1464_; uint8_t v_isMeta_1465_; uint8_t v_isExported_1466_; uint8_t v_importAll_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_i_1449_);
v_imports_1461_ = lean_ctor_get(v_s_1448_, 0);
v_badModifier_1462_ = lean_ctor_get_uint8(v_s_1448_, sizeof(void*)*3);
v_error_x3f_1463_ = lean_ctor_get(v_s_1448_, 2);
v_isModule_1464_ = lean_ctor_get_uint8(v_s_1448_, sizeof(void*)*3 + 1);
v_isMeta_1465_ = lean_ctor_get_uint8(v_s_1448_, sizeof(void*)*3 + 2);
v_isExported_1466_ = lean_ctor_get_uint8(v_s_1448_, sizeof(void*)*3 + 3);
v_importAll_1467_ = lean_ctor_get_uint8(v_s_1448_, sizeof(void*)*3 + 4);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_s_1448_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_s_1448_, 1);
lean_dec(v_unused_1477_);
v___x_1469_ = v_s_1448_;
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_error_x3f_1463_);
lean_inc(v_imports_1461_);
lean_dec(v_s_1448_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v_j_1450_);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_imports_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_j_1450_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_error_x3f_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3, v_badModifier_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3 + 1, v_isModule_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3 + 2, v_isMeta_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3 + 3, v_isExported_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3 + 4, v_importAll_1467_);
v___x_1472_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = l_Lean_ParseImports_whitespace(v_input_1447_, v___x_1472_);
v___x_1474_ = l_Lean_ParseImports_setIsModule___redArg(v___x_1451_, v___x_1473_);
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* v_k_1478_, lean_object* v_input_1479_, lean_object* v_s_1480_, lean_object* v_i_1481_, lean_object* v_j_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_1478_, v_input_1479_, v_s_1480_, v_i_1481_, v_j_1482_);
lean_dec_ref(v_input_1479_);
lean_dec_ref(v_k_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_pos_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_s_1491_; lean_object* v_error_x3f_1492_; 
v_pos_1488_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_pos_1488_);
v___x_1489_ = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
v___x_1490_ = lean_unsigned_to_nat(0u);
v_s_1491_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_1489_, v_a_1486_, v_a_1487_, v___x_1490_, v_pos_1488_);
v_error_x3f_1492_ = lean_ctor_get(v_s_1491_, 2);
if (lean_obj_tag(v_error_x3f_1492_) == 1)
{
lean_dec_ref(v_a_1486_);
return v_s_1491_;
}
else
{
lean_object* v_pos_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_error_x3f_1496_; 
v_pos_1493_ = lean_ctor_get(v_s_1491_, 1);
lean_inc(v_pos_1493_);
v___x_1494_ = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
v___x_1495_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_1494_, v_a_1486_, v_s_1491_, v___x_1490_, v_pos_1493_);
v_error_x3f_1496_ = lean_ctor_get(v___x_1495_, 2);
if (lean_obj_tag(v_error_x3f_1496_) == 1)
{
lean_dec_ref(v_a_1486_);
return v___x_1495_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(v_a_1486_, v___x_1495_);
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* v_input_1500_, lean_object* v_fileName_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_s_1505_; lean_object* v_error_x3f_1506_; 
v___x_1503_ = ((lean_object*)(l_Lean_ParseImports_instInhabitedState_default___closed__1));
v___x_1504_ = l_Lean_ParseImports_whitespace(v_input_1500_, v___x_1503_);
lean_inc_ref(v_input_1500_);
v_s_1505_ = l_Lean_ParseImports_main(v_input_1500_, v___x_1504_);
v_error_x3f_1506_ = lean_ctor_get(v_s_1505_, 2);
lean_inc(v_error_x3f_1506_);
if (lean_obj_tag(v_error_x3f_1506_) == 1)
{
lean_object* v_pos_1507_; lean_object* v_val_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1530_; 
v_pos_1507_ = lean_ctor_get(v_s_1505_, 1);
lean_inc(v_pos_1507_);
lean_dec_ref(v_s_1505_);
v_val_1508_ = lean_ctor_get(v_error_x3f_1506_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_error_x3f_1506_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1510_ = v_error_x3f_1506_;
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_val_1508_);
lean_dec(v_error_x3f_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_fileMap_1512_; lean_object* v_pos_1513_; lean_object* v_line_1514_; lean_object* v_column_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v_fileMap_1512_ = l_Lean_String_toFileMap(v_input_1500_);
v_pos_1513_ = l_Lean_FileMap_toPosition(v_fileMap_1512_, v_pos_1507_);
lean_dec(v_pos_1507_);
v_line_1514_ = lean_ctor_get(v_pos_1513_, 0);
lean_inc(v_line_1514_);
v_column_1515_ = lean_ctor_get(v_pos_1513_, 1);
lean_inc(v_column_1515_);
lean_dec_ref(v_pos_1513_);
v___x_1516_ = ((lean_object*)(l_Lean_parseImports_x27___closed__0));
v___x_1517_ = lean_string_append(v_fileName_1501_, v___x_1516_);
v___x_1518_ = l_Nat_reprFast(v_line_1514_);
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = lean_string_append(v___x_1519_, v___x_1516_);
v___x_1521_ = l_Nat_reprFast(v_column_1515_);
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
v___x_1525_ = lean_string_append(v___x_1524_, v_val_1508_);
lean_dec(v_val_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 18);
lean_ctor_set(v___x_1510_, 0, v___x_1525_);
v___x_1527_ = v___x_1510_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
}
else
{
lean_object* v_imports_1531_; uint8_t v_isModule_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_error_x3f_1506_);
lean_dec_ref(v_fileName_1501_);
lean_dec_ref(v_input_1500_);
v_imports_1531_ = lean_ctor_get(v_s_1505_, 0);
lean_inc_ref(v_imports_1531_);
v_isModule_1532_ = lean_ctor_get_uint8(v_s_1505_, sizeof(void*)*3 + 1);
lean_dec_ref(v_s_1505_);
v___x_1533_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1533_, 0, v_imports_1531_);
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*1, v_isModule_1532_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* v_input_1535_, lean_object* v_fileName_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_parseImports_x27(v_input_1535_, v_fileName_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* v_k_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref(v_k_1539_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v_val_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_val_1542_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1543_ = l_Lean_instToJsonModuleHeader_toJson(v_val_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_k_1539_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
if (lean_obj_tag(v_a_1547_) == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_array_to_list(v_a_1548_);
return v___x_1549_;
}
else
{
lean_object* v_head_1550_; lean_object* v_tail_1551_; lean_object* v___x_1552_; 
v_head_1550_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_head_1550_);
v_tail_1551_ = lean_ctor_get(v_a_1547_, 1);
lean_inc(v_tail_1551_);
lean_dec_ref_known(v_a_1547_, 2);
v___x_1552_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1548_, v_head_1550_);
v_a_1547_ = v_tail_1551_;
v_a_1548_ = v___x_1552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_bs_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1557_ == 0)
{
return v_bs_1556_;
}
else
{
lean_object* v_v_1558_; lean_object* v___x_1559_; lean_object* v_bs_x27_1560_; lean_object* v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_v_1558_ = lean_array_uget(v_bs_1556_, v_i_1555_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v_bs_x27_1560_ = lean_array_uset(v_bs_1556_, v_i_1555_, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_v_1558_);
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1555_, v___x_1562_);
v___x_1564_ = lean_array_uset(v_bs_x27_1560_, v_i_1555_, v___x_1561_);
v_i_1555_ = v___x_1563_;
v_bs_1556_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* v_sz_1566_, lean_object* v_i_1567_, lean_object* v_bs_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1566_);
lean_dec(v_sz_1566_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* v_a_1572_){
_start:
{
size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_sz_1573_ = lean_array_size(v_a_1572_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_1573_, v___x_1574_, v_a_1572_);
v___x_1576_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* v_x_1581_){
_start:
{
lean_object* v_result_x3f_1582_; lean_object* v_errors_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1601_; 
v_result_x3f_1582_ = lean_ctor_get(v_x_1581_, 0);
v_errors_1583_ = lean_ctor_get(v_x_1581_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1581_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1585_ = v_x_1581_;
v_isShared_1586_ = v_isSharedCheck_1601_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_errors_1583_);
lean_inc(v_result_x3f_1582_);
lean_dec(v_x_1581_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1601_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
v___x_1588_ = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(v___x_1587_, v_result_x3f_1582_);
v___x_1589_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
v___x_1590_ = l_Lean_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(v_errors_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___x_1590_);
lean_ctor_set(v___x_1585_, 0, v___x_1589_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___x_1593_);
v___x_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1588_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
v___x_1598_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_1596_, v___x_1597_);
v___x_1599_ = l_Lean_Json_mkObj(v___x_1598_);
lean_dec(v___x_1598_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t v_sz_1604_, size_t v_i_1605_, lean_object* v_bs_1606_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_lt(v_i_1605_, v_sz_1604_);
if (v___x_1607_ == 0)
{
return v_bs_1606_;
}
else
{
lean_object* v_v_1608_; lean_object* v___x_1609_; lean_object* v_bs_x27_1610_; lean_object* v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v_v_1608_ = lean_array_uget(v_bs_1606_, v_i_1605_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v_bs_x27_1610_ = lean_array_uset(v_bs_1606_, v_i_1605_, v___x_1609_);
v___x_1611_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_1608_);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1605_, v___x_1612_);
v___x_1614_ = lean_array_uset(v_bs_x27_1610_, v_i_1605_, v___x_1611_);
v_i_1605_ = v___x_1613_;
v_bs_1606_ = v___x_1614_;
goto _start;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t v_sz_1642_, size_t v_i_1643_, lean_object* v_bs_1644_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* v_sz_1680_, lean_object* v_i_1681_, lean_object* v_bs_1682_, lean_object* v___y_1683_){
_start:
{
size_t v_sz_boxed_1684_; size_t v_i_boxed_1685_; lean_object* v_res_1686_; 
v_sz_boxed_1684_ = lean_unbox_usize(v_sz_1680_);
lean_dec(v_sz_1680_);
v_i_boxed_1685_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_1684_, v_i_boxed_1685_, v_bs_1682_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* v_s_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v_putStr_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_get_stdout();
v_putStr_1690_ = lean_ctor_get(v___x_1689_, 4);
lean_inc_ref(v_putStr_1690_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = lean_apply_2(v_putStr_1690_, v_s_1687_, lean_box(0));
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* v_s_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* v_s_1695_){
_start:
{
uint32_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = 10;
v___x_1698_ = lean_string_push(v_s_1695_, v___x_1697_);
v___x_1699_ = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* v_s_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* v_fileNames_1703_){
_start:
{
size_t v_sz_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v_sz_1705_ = lean_array_size(v_fileNames_1703_);
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_1705_, v___x_1706_, v_fileNames_1703_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_1708_);
v___x_1710_ = l_Lean_Json_compress(v___x_1709_);
v___x_1711_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1707_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1707_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* v_fileNames_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_printImportsJson(v_fileNames_1720_);
return v_res_1722_;
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
