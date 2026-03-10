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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unterminated comment"};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1 = (const lean_object*)&l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParseImports_keyword___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_ParseImports_keyword___lam__0___closed__0 = (const lean_object*)&l_Lean_ParseImports_keyword___lam__0___closed__0_value;
static const lean_string_object l_Lean_ParseImports_keyword___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` expected"};
static const lean_object* l_Lean_ParseImports_keyword___lam__0___closed__1 = (const lean_object*)&l_Lean_ParseImports_keyword___lam__0___closed__1_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_parseImports_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_parseImports_x27___closed__0 = (const lean_object*)&l_Lean_parseImports_x27___closed__0_value;
static const lean_ctor_object l_Lean_parseImports_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_parseImports_x27___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_parseImports_x27___closed__1 = (const lean_object*)&l_Lean_parseImports_x27___closed__1_value;
static const lean_string_object l_Lean_parseImports_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_parseImports_x27___closed__2 = (const lean_object*)&l_Lean_parseImports_x27___closed__2_value;
static const lean_string_object l_Lean_parseImports_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_parseImports_x27___closed__3 = (const lean_object*)&l_Lean_parseImports_x27___closed__3_value;
lean_object* l_String_toFileMap(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object*);
static const lean_string_object l_Lean_instToJsonPrintImportResult_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__0_value;
static const lean_string_object l_Lean_instToJsonPrintImportResult_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "errors"};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__1 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__1_value;
static const lean_array_object l_Lean_instToJsonPrintImportResult_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToJsonPrintImportResult_toJson___closed__2 = (const lean_object*)&l_Lean_instToJsonPrintImportResult_toJson___closed__2_value;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPrintImportResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPrintImportResult_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPrintImportResult___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPrintImportResult = (const lean_object*)&l_Lean_instToJsonPrintImportResult___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l_Lean_instToJsonPrintImportsResult_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPrintImportsResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPrintImportsResult_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPrintImportsResult___closed__0 = (const lean_object*)&l_Lean_instToJsonPrintImportsResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPrintImportsResult = (const lean_object*)&l_Lean_instToJsonPrintImportsResult___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_skip___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_skip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_skip(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_10 = x_1;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_2);
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 2);
lean_dec(x_18);
x_10 = x_1;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
if (x_11 == 0)
{
lean_ctor_set(x_10, 2, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 2);
lean_dec(x_17);
x_9 = x_1;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_Lean_ParseImports_State_mkEOIError___closed__1));
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_8);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_clearError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 2);
lean_dec(x_17);
x_8 = x_1;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 2, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_7);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_10);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_11 = x_1;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_utf8_next(x_2, x_3);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 4, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_11 = x_1;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_utf8_next_fast(x_2, x_3);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 4, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next_x27___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_12 = x_1;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_2, x_3);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 4, x_11);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ParseImports_State_next_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 2);
lean_dec(x_17);
x_9 = x_1;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1));
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_8);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_12 = lean_string_utf8_at_end(x_2, x_5);
if (x_12 == 0)
{
uint32_t x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_13 = lean_string_utf8_get_fast(x_2, x_5);
x_14 = lean_string_utf8_next_fast(x_2, x_5);
x_15 = 45;
x_16 = lean_uint32_dec_eq(x_13, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 47;
x_18 = lean_uint32_dec_eq(x_13, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_26; 
lean_inc(x_7);
lean_inc_ref(x_4);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_19 = x_3;
x_20 = x_26;
goto block_25;
}
else
{
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_14);
x_21 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 4, x_11);
x_21 = x_24;
goto block_23;
}
block_23:
{
x_3 = x_21;
goto _start;
}
}
}
else
{
uint8_t x_30; 
x_30 = lean_string_utf8_at_end(x_2, x_14);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_47; 
lean_inc(x_7);
lean_inc_ref(x_4);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_3, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 0);
lean_dec(x_50);
x_31 = x_3;
x_32 = x_47;
goto block_46;
}
else
{
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = x_47;
goto block_46;
}
block_46:
{
uint32_t x_33; uint8_t x_34; 
x_33 = lean_string_utf8_get_fast(x_2, x_14);
x_34 = lean_uint32_dec_eq(x_33, x_15);
if (x_34 == 0)
{
lean_object* x_35; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_14);
x_35 = x_31;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_14);
lean_ctor_set(x_38, 2, x_7);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 4, x_11);
x_35 = x_38;
goto block_37;
}
block_37:
{
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_1, x_39);
lean_dec(x_1);
x_41 = lean_string_utf8_next_fast(x_2, x_14);
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_41);
x_42 = x_31;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_7);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 4, x_11);
x_42 = x_45;
goto block_44;
}
block_44:
{
x_1 = x_40;
x_3 = x_42;
goto _start;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = lean_string_utf8_at_end(x_2, x_14);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_76; 
lean_inc(x_7);
lean_inc_ref(x_4);
x_76 = !lean_is_exclusive(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_3, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 0);
lean_dec(x_79);
x_53 = x_3;
x_54 = x_76;
goto block_75;
}
else
{
lean_dec(x_3);
x_53 = lean_box(0);
x_54 = x_76;
goto block_75;
}
block_75:
{
uint32_t x_55; uint32_t x_56; uint8_t x_57; 
x_55 = lean_string_utf8_get_fast(x_2, x_14);
x_56 = 47;
x_57 = lean_uint32_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_string_utf8_next_fast(x_2, x_14);
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_58);
x_59 = x_53;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_62, 2, x_7);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 4, x_11);
x_59 = x_62;
goto block_61;
}
block_61:
{
x_3 = x_59;
goto _start;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_dec_eq(x_1, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_nat_sub(x_1, x_63);
lean_dec(x_1);
x_66 = lean_string_utf8_next_fast(x_2, x_14);
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_66);
x_67 = x_53;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_7);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 4, x_11);
x_67 = x_70;
goto block_69;
}
block_69:
{
x_1 = x_65;
x_3 = x_67;
goto _start;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_string_utf8_next(x_2, x_14);
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_71);
x_72 = x_53;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_7);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_74, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_74, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_74, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_74, sizeof(void*)*3 + 4, x_11);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_1);
x_81 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_finishCommentBlock(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_12 = lean_string_utf8_at_end(x_2, x_5);
if (x_12 == 0)
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_string_utf8_get_fast(x_2, x_5);
x_14 = lean_box_uint32(x_13);
lean_inc_ref(x_1);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_25; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_17 = x_3;
x_18 = x_25;
goto block_24;
}
else
{
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_19);
x_20 = x_17;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 2, x_9);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 3, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 4, x_11);
x_20 = x_23;
goto block_22;
}
block_22:
{
x_3 = x_20;
goto _start;
}
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_ParseImports_takeWhile___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_ParseImports_takeWhile___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_ParseImports_takeUntil(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeWhile(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_7; 
lean_dec(x_6);
x_7 = lean_apply_2(x_2, x_3, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_11 = lean_string_utf8_at_end(x_1, x_4);
if (x_11 == 0)
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_string_utf8_get_fast(x_1, x_4);
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_23; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_15 = x_2;
x_16 = x_23;
goto block_22;
}
else
{
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 4, x_10);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_2 = x_18;
goto _start;
}
}
}
else
{
return x_2;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_15 = lean_string_utf8_at_end(x_1, x_4);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_63; uint32_t x_69; uint8_t x_70; 
x_16 = lean_string_utf8_get_fast(x_1, x_4);
x_69 = 9;
x_70 = lean_uint32_dec_eq(x_16, x_69);
if (x_70 == 0)
{
uint32_t x_71; uint8_t x_72; 
x_71 = 32;
x_72 = lean_uint32_dec_eq(x_16, x_71);
if (x_72 == 0)
{
x_63 = x_70;
goto block_68;
}
else
{
x_63 = x_72;
goto block_68;
}
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_80; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_80 = !lean_is_exclusive(x_2);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_2, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 0);
lean_dec(x_83);
x_73 = x_2;
x_74 = x_80;
goto block_79;
}
else
{
lean_dec(x_2);
x_73 = lean_box(0);
x_74 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_75; lean_object* x_76; 
x_75 = ((lean_object*)(l_Lean_ParseImports_whitespace___closed__1));
if (x_74 == 0)
{
lean_ctor_set(x_73, 2, x_75);
x_76 = x_73;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_4);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 4, x_10);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
block_62:
{
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 45;
x_19 = lean_uint32_dec_eq(x_16, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 47;
x_21 = lean_uint32_dec_eq(x_16, x_20);
if (x_21 == 0)
{
return x_2;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_string_utf8_next_fast(x_1, x_4);
x_23 = lean_string_utf8_get(x_1, x_22);
x_24 = lean_uint32_dec_eq(x_23, x_18);
if (x_24 == 0)
{
return x_2;
}
else
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_string_utf8_next(x_1, x_22);
x_26 = lean_string_utf8_get(x_1, x_25);
x_27 = lean_uint32_dec_eq(x_26, x_18);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 33;
x_29 = lean_uint32_dec_eq(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_41; 
lean_inc(x_6);
lean_inc_ref(x_3);
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_30 = x_2;
x_31 = x_41;
goto block_40;
}
else
{
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_string_utf8_next(x_1, x_25);
lean_dec(x_25);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_33);
x_34 = x_30;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 4, x_10);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_ParseImports_finishCommentBlock(x_32, x_1, x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 1)
{
lean_dec_ref(x_36);
return x_35;
}
else
{
lean_dec(x_36);
x_2 = x_35;
goto _start;
}
}
}
}
else
{
lean_dec(x_25);
return x_2;
}
}
else
{
lean_dec(x_25);
return x_2;
}
}
}
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_string_utf8_next_fast(x_1, x_4);
x_46 = lean_string_utf8_get(x_1, x_45);
x_47 = lean_uint32_dec_eq(x_46, x_18);
if (x_47 == 0)
{
return x_2;
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_58; 
lean_inc(x_6);
lean_inc_ref(x_3);
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_2, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_2, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_2, 0);
lean_dec(x_61);
x_48 = x_2;
x_49 = x_58;
goto block_57;
}
else
{
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_string_utf8_next(x_1, x_45);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_50);
x_51 = x_48;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_6);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 4, x_10);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(x_1, x_51);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_dec_ref(x_53);
return x_52;
}
else
{
lean_dec(x_53);
x_2 = x_52;
goto _start;
}
}
}
}
}
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
goto block_14;
}
}
block_68:
{
if (x_63 == 0)
{
uint32_t x_64; uint8_t x_65; 
x_64 = 13;
x_65 = lean_uint32_dec_eq(x_16, x_64);
if (x_65 == 0)
{
uint32_t x_66; uint8_t x_67; 
x_66 = 10;
x_67 = lean_uint32_dec_eq(x_16, x_66);
x_17 = x_67;
goto block_62;
}
else
{
x_17 = x_65;
goto block_62;
}
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
goto block_14;
}
}
}
else
{
return x_2;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 4, x_10);
x_2 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_whitespace(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_utf8_at_end(x_4, x_7);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_1, x_6);
x_11 = lean_string_utf8_get_fast(x_4, x_7);
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_13 = lean_apply_2(x_2, x_4, x_5);
return x_13;
}
else
{
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_6);
lean_dec(x_6);
x_15 = lean_string_utf8_next_fast(x_4, x_7);
lean_dec(x_7);
x_6 = x_14;
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_17 = lean_apply_2(x_2, x_4, x_5);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_18 = lean_apply_2(x_2, x_4, x_5);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_6);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 3);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 4);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_5, 1);
lean_dec(x_35);
x_26 = x_5;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_5);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_7);
x_28 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 1, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 2, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 3, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 4, x_25);
x_28 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_ParseImports_whitespace(x_4, x_28);
x_30 = lean_apply_2(x_3, x_4, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_22; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_3, 2);
lean_dec(x_23);
x_11 = x_3;
x_12 = x_22;
goto block_21;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__0));
x_14 = lean_string_append(x_13, x_1);
x_15 = ((lean_object*)(l_Lean_ParseImports_keyword___lam__0___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_17);
x_18 = x_11;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 4, x_10);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_keyword___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_ParseImports_skip___boxed), 2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(x_1, x_5, x_6, x_2, x_3, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_string_utf8_next(x_1, x_3);
x_8 = lean_string_utf8_at_end(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; uint8_t x_14; uint32_t x_24; uint8_t x_25; 
x_9 = lean_string_utf8_get_fast(x_1, x_7);
lean_dec(x_7);
x_24 = 65;
x_25 = lean_uint32_dec_le(x_24, x_9);
if (x_25 == 0)
{
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 90;
x_27 = lean_uint32_dec_le(x_9, x_26);
if (x_27 == 0)
{
goto block_23;
}
else
{
return x_6;
}
}
block_13:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 171;
x_12 = lean_uint32_dec_eq(x_9, x_11);
return x_12;
}
else
{
return x_6;
}
}
block_18:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 95;
x_16 = lean_uint32_dec_eq(x_9, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_isLetterLike(x_9);
x_10 = x_17;
goto block_13;
}
else
{
x_10 = x_16;
goto block_13;
}
}
else
{
return x_6;
}
}
block_23:
{
uint32_t x_19; uint8_t x_20; 
x_19 = 97;
x_20 = lean_uint32_dec_le(x_19, x_9);
if (x_20 == 0)
{
x_14 = x_20;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 122;
x_22 = lean_uint32_dec_le(x_9, x_21);
x_14 = x_22;
goto block_18;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = 0;
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ParseImports_isIdCont(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_11 = x_2;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_3, x_1);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 4, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_10; uint8_t x_11; 
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 39;
x_13 = lean_uint32_dec_eq(x_1, x_12);
x_2 = x_13;
goto block_9;
}
else
{
x_2 = x_11;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 33;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 63;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_isLetterLike(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_isSubScriptAlnum(x_1);
return x_8;
}
else
{
return x_7;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestCold(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_10; uint8_t x_22; uint32_t x_33; uint8_t x_34; 
x_33 = 65;
x_34 = lean_uint32_dec_le(x_33, x_1);
if (x_34 == 0)
{
goto block_32;
}
else
{
uint32_t x_35; uint8_t x_36; 
x_35 = 90;
x_36 = lean_uint32_dec_le(x_1, x_35);
if (x_36 == 0)
{
goto block_32;
}
else
{
return x_36;
}
}
block_9:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 33;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 63;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_isLetterLike(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_isSubScriptAlnum(x_1);
return x_8;
}
else
{
return x_7;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_21:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 46;
x_12 = lean_uint32_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 32;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 95;
x_18 = lean_uint32_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 39;
x_20 = lean_uint32_dec_eq(x_1, x_19);
x_2 = x_20;
goto block_9;
}
else
{
x_2 = x_18;
goto block_9;
}
}
else
{
return x_10;
}
}
else
{
return x_10;
}
}
else
{
return x_10;
}
}
else
{
return x_10;
}
}
block_27:
{
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 48;
x_24 = lean_uint32_dec_le(x_23, x_1);
if (x_24 == 0)
{
x_10 = x_24;
goto block_21;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 57;
x_26 = lean_uint32_dec_le(x_1, x_25);
x_10 = x_26;
goto block_21;
}
}
else
{
return x_22;
}
}
block_32:
{
uint32_t x_28; uint8_t x_29; 
x_28 = 97;
x_29 = lean_uint32_dec_le(x_28, x_1);
if (x_29 == 0)
{
x_22 = x_29;
goto block_27;
}
else
{
uint32_t x_30; uint8_t x_31; 
x_30 = 122;
x_31 = lean_uint32_dec_le(x_1, x_30);
x_22 = x_31;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestFast(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_11 = lean_string_utf8_at_end(x_1, x_4);
if (x_11 == 0)
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_string_utf8_get_fast(x_1, x_4);
x_13 = 187;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_23; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_15 = x_2;
x_16 = x_23;
goto block_22;
}
else
{
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 4, x_10);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_2 = x_18;
goto _start;
}
}
}
else
{
return x_2;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_27; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 4);
x_27 = lean_string_utf8_at_end(x_3, x_6);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; uint32_t x_30; uint8_t x_31; uint8_t x_39; uint8_t x_51; uint32_t x_62; uint8_t x_63; 
x_28 = 171;
x_29 = lean_uint32_dec_eq(x_2, x_28);
x_30 = lean_string_utf8_get_fast(x_3, x_6);
x_62 = 65;
x_63 = lean_uint32_dec_le(x_62, x_30);
if (x_63 == 0)
{
goto block_61;
}
else
{
uint32_t x_64; uint8_t x_65; 
x_64 = 90;
x_65 = lean_uint32_dec_le(x_30, x_64);
if (x_65 == 0)
{
goto block_61;
}
else
{
x_13 = x_29;
goto block_26;
}
}
block_38:
{
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 33;
x_33 = lean_uint32_dec_eq(x_30, x_32);
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
x_34 = 63;
x_35 = lean_uint32_dec_eq(x_30, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_isLetterLike(x_30);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_isSubScriptAlnum(x_30);
if (x_37 == 0)
{
x_13 = x_1;
goto block_26;
}
else
{
x_13 = x_29;
goto block_26;
}
}
else
{
if (x_36 == 0)
{
x_13 = x_1;
goto block_26;
}
else
{
x_13 = x_29;
goto block_26;
}
}
}
else
{
if (x_35 == 0)
{
x_13 = x_1;
goto block_26;
}
else
{
x_13 = x_29;
goto block_26;
}
}
}
else
{
if (x_33 == 0)
{
x_13 = x_1;
goto block_26;
}
else
{
x_13 = x_29;
goto block_26;
}
}
}
else
{
x_13 = x_29;
goto block_26;
}
}
block_50:
{
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 46;
x_41 = lean_uint32_dec_eq(x_30, x_40);
if (x_41 == 0)
{
uint32_t x_42; uint8_t x_43; 
x_42 = 10;
x_43 = lean_uint32_dec_eq(x_30, x_42);
if (x_43 == 0)
{
uint32_t x_44; uint8_t x_45; 
x_44 = 32;
x_45 = lean_uint32_dec_eq(x_30, x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; 
x_46 = 95;
x_47 = lean_uint32_dec_eq(x_30, x_46);
if (x_47 == 0)
{
uint32_t x_48; uint8_t x_49; 
x_48 = 39;
x_49 = lean_uint32_dec_eq(x_30, x_48);
x_31 = x_49;
goto block_38;
}
else
{
x_31 = x_47;
goto block_38;
}
}
else
{
x_13 = x_45;
goto block_26;
}
}
else
{
x_13 = x_43;
goto block_26;
}
}
else
{
x_13 = x_41;
goto block_26;
}
}
else
{
x_13 = x_29;
goto block_26;
}
}
block_56:
{
if (x_51 == 0)
{
uint32_t x_52; uint8_t x_53; 
x_52 = 48;
x_53 = lean_uint32_dec_le(x_52, x_30);
if (x_53 == 0)
{
x_39 = x_53;
goto block_50;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 57;
x_55 = lean_uint32_dec_le(x_30, x_54);
x_39 = x_55;
goto block_50;
}
}
else
{
x_13 = x_29;
goto block_26;
}
}
block_61:
{
uint32_t x_57; uint8_t x_58; 
x_57 = 97;
x_58 = lean_uint32_dec_le(x_57, x_30);
if (x_58 == 0)
{
x_51 = x_58;
goto block_56;
}
else
{
uint32_t x_59; uint8_t x_60; 
x_59 = 122;
x_60 = lean_uint32_dec_le(x_30, x_59);
x_51 = x_60;
goto block_56;
}
}
}
else
{
return x_4;
}
block_26:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_22; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 0);
lean_dec(x_25);
x_14 = x_4;
x_15 = x_22;
goto block_21;
}
else
{
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_utf8_next_fast(x_3, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
x_17 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 2, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 3, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 4, x_12);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_4 = x_17;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(x_5, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 3);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 4);
x_29 = lean_string_utf8_at_end(x_1, x_22);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_185; 
lean_inc(x_24);
lean_inc(x_22);
lean_inc_ref(x_21);
x_185 = !lean_is_exclusive(x_4);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_4, 2);
lean_dec(x_186);
x_187 = lean_ctor_get(x_4, 1);
lean_dec(x_187);
x_188 = lean_ctor_get(x_4, 0);
lean_dec(x_188);
x_30 = x_4;
x_31 = x_185;
goto block_184;
}
else
{
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_185;
goto block_184;
}
block_184:
{
uint32_t x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint32_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint32_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint32_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; uint8_t x_83; uint8_t x_84; uint8_t x_111; uint8_t x_115; 
x_32 = lean_string_utf8_get_fast(x_1, x_22);
x_33 = 171;
x_83 = lean_uint32_dec_eq(x_32, x_33);
if (x_83 == 0)
{
uint32_t x_125; uint8_t x_126; 
x_125 = 65;
x_126 = lean_uint32_dec_le(x_125, x_32);
if (x_126 == 0)
{
goto block_124;
}
else
{
uint32_t x_127; uint8_t x_128; 
x_127 = 90;
x_128 = lean_uint32_dec_le(x_32, x_127);
if (x_128 == 0)
{
goto block_124;
}
else
{
x_84 = x_128;
goto block_110;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; uint8_t x_183; 
lean_del_object(x_30);
x_129 = lean_string_utf8_next_fast(x_1, x_22);
lean_dec(x_22);
x_130 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_130, 0, x_21);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_24);
lean_ctor_set_uint8(x_130, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_130, sizeof(void*)*3 + 1, x_25);
lean_ctor_set_uint8(x_130, sizeof(void*)*3 + 2, x_26);
lean_ctor_set_uint8(x_130, sizeof(void*)*3 + 3, x_27);
lean_ctor_set_uint8(x_130, sizeof(void*)*3 + 4, x_28);
x_131 = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(x_1, x_130);
x_132 = lean_ctor_get(x_131, 0);
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get_uint8(x_131, sizeof(void*)*3);
x_135 = lean_ctor_get(x_131, 2);
x_136 = lean_ctor_get_uint8(x_131, sizeof(void*)*3 + 1);
x_137 = lean_ctor_get_uint8(x_131, sizeof(void*)*3 + 2);
x_138 = lean_ctor_get_uint8(x_131, sizeof(void*)*3 + 3);
x_139 = lean_ctor_get_uint8(x_131, sizeof(void*)*3 + 4);
x_183 = !lean_is_exclusive(x_131);
if (x_183 == 0)
{
x_140 = x_131;
x_141 = x_183;
goto block_182;
}
else
{
lean_inc(x_135);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_131);
x_140 = lean_box(0);
x_141 = x_183;
goto block_182;
}
block_182:
{
uint8_t x_142; 
x_142 = lean_string_utf8_at_end(x_1, x_133);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_string_utf8_next_fast(x_1, x_133);
lean_inc(x_135);
lean_inc_ref(x_132);
if (x_141 == 0)
{
lean_ctor_set(x_140, 1, x_143);
x_144 = x_140;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_177, 0, x_132);
lean_ctor_set(x_177, 1, x_143);
lean_ctor_set(x_177, 2, x_135);
lean_ctor_set_uint8(x_177, sizeof(void*)*3, x_134);
lean_ctor_set_uint8(x_177, sizeof(void*)*3 + 1, x_136);
lean_ctor_set_uint8(x_177, sizeof(void*)*3 + 2, x_137);
lean_ctor_set_uint8(x_177, sizeof(void*)*3 + 3, x_138);
lean_ctor_set_uint8(x_177, sizeof(void*)*3 + 4, x_139);
x_144 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint32_t x_153; uint32_t x_154; uint8_t x_155; 
x_145 = lean_string_utf8_extract(x_1, x_129, x_133);
lean_dec(x_133);
x_146 = l_Lean_Name_str___override(x_3, x_145);
x_153 = lean_string_utf8_get(x_1, x_143);
x_154 = 46;
x_155 = lean_uint32_dec_eq(x_153, x_154);
if (x_155 == 0)
{
x_147 = x_155;
goto block_152;
}
else
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_string_utf8_next(x_1, x_143);
x_157 = lean_string_utf8_at_end(x_1, x_156);
if (x_157 == 0)
{
uint32_t x_158; uint8_t x_159; uint8_t x_162; uint32_t x_172; uint8_t x_173; 
x_158 = lean_string_utf8_get_fast(x_1, x_156);
lean_dec(x_156);
x_172 = 65;
x_173 = lean_uint32_dec_le(x_172, x_158);
if (x_173 == 0)
{
goto block_171;
}
else
{
uint32_t x_174; uint8_t x_175; 
x_174 = 90;
x_175 = lean_uint32_dec_le(x_158, x_174);
if (x_175 == 0)
{
goto block_171;
}
else
{
x_147 = x_155;
goto block_152;
}
}
block_161:
{
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_uint32_dec_eq(x_158, x_33);
x_147 = x_160;
goto block_152;
}
else
{
x_147 = x_155;
goto block_152;
}
}
block_166:
{
if (x_162 == 0)
{
uint32_t x_163; uint8_t x_164; 
x_163 = 95;
x_164 = lean_uint32_dec_eq(x_158, x_163);
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = l_Lean_isLetterLike(x_158);
x_159 = x_165;
goto block_161;
}
else
{
x_159 = x_164;
goto block_161;
}
}
else
{
x_147 = x_155;
goto block_152;
}
}
block_171:
{
uint32_t x_167; uint8_t x_168; 
x_167 = 97;
x_168 = lean_uint32_dec_le(x_167, x_158);
if (x_168 == 0)
{
x_162 = x_168;
goto block_166;
}
else
{
uint32_t x_169; uint8_t x_170; 
x_169 = 122;
x_170 = lean_uint32_dec_le(x_158, x_169);
x_162 = x_170;
goto block_166;
}
}
}
else
{
lean_dec(x_156);
x_147 = x_142;
goto block_152;
}
}
block_152:
{
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_135);
lean_dec_ref(x_132);
x_148 = lean_apply_3(x_2, x_146, x_1, x_144);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_144);
x_149 = lean_string_utf8_next(x_1, x_143);
x_150 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_150, 0, x_132);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_135);
lean_ctor_set_uint8(x_150, sizeof(void*)*3, x_134);
lean_ctor_set_uint8(x_150, sizeof(void*)*3 + 1, x_136);
lean_ctor_set_uint8(x_150, sizeof(void*)*3 + 2, x_137);
lean_ctor_set_uint8(x_150, sizeof(void*)*3 + 3, x_138);
lean_ctor_set_uint8(x_150, sizeof(void*)*3 + 4, x_139);
x_3 = x_146;
x_4 = x_150;
goto _start;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_135);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_178 = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3));
if (x_141 == 0)
{
lean_ctor_set(x_140, 2, x_178);
x_179 = x_140;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_181, 0, x_132);
lean_ctor_set(x_181, 1, x_133);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set_uint8(x_181, sizeof(void*)*3, x_134);
lean_ctor_set_uint8(x_181, sizeof(void*)*3 + 1, x_136);
lean_ctor_set_uint8(x_181, sizeof(void*)*3 + 2, x_137);
lean_ctor_set_uint8(x_181, sizeof(void*)*3 + 3, x_138);
lean_ctor_set_uint8(x_181, sizeof(void*)*3 + 4, x_139);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
}
}
block_48:
{
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = lean_uint32_dec_eq(x_39, x_33);
x_5 = x_35;
x_6 = x_34;
x_7 = x_36;
x_8 = x_38;
x_9 = x_40;
x_10 = x_42;
x_11 = x_41;
x_12 = x_43;
x_13 = x_44;
x_14 = x_45;
x_15 = x_47;
goto block_20;
}
else
{
x_5 = x_35;
x_6 = x_34;
x_7 = x_36;
x_8 = x_38;
x_9 = x_40;
x_10 = x_42;
x_11 = x_41;
x_12 = x_43;
x_13 = x_44;
x_14 = x_45;
x_15 = x_37;
goto block_20;
}
}
block_65:
{
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = 95;
x_63 = lean_uint32_dec_eq(x_54, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_isLetterLike(x_54);
x_34 = x_50;
x_35 = x_49;
x_36 = x_51;
x_37 = x_53;
x_38 = x_52;
x_39 = x_54;
x_40 = x_55;
x_41 = x_57;
x_42 = x_56;
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_64;
goto block_48;
}
else
{
x_34 = x_50;
x_35 = x_49;
x_36 = x_51;
x_37 = x_53;
x_38 = x_52;
x_39 = x_54;
x_40 = x_55;
x_41 = x_57;
x_42 = x_56;
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_63;
goto block_48;
}
}
else
{
x_5 = x_49;
x_6 = x_50;
x_7 = x_51;
x_8 = x_52;
x_9 = x_55;
x_10 = x_56;
x_11 = x_57;
x_12 = x_58;
x_13 = x_59;
x_14 = x_60;
x_15 = x_53;
goto block_20;
}
}
block_82:
{
uint32_t x_78; uint8_t x_79; 
x_78 = 97;
x_79 = lean_uint32_dec_le(x_78, x_71);
if (x_79 == 0)
{
x_49 = x_67;
x_50 = x_66;
x_51 = x_68;
x_52 = x_70;
x_53 = x_69;
x_54 = x_71;
x_55 = x_72;
x_56 = x_74;
x_57 = x_73;
x_58 = x_75;
x_59 = x_76;
x_60 = x_77;
x_61 = x_79;
goto block_65;
}
else
{
uint32_t x_80; uint8_t x_81; 
x_80 = 122;
x_81 = lean_uint32_dec_le(x_71, x_80);
x_49 = x_67;
x_50 = x_66;
x_51 = x_68;
x_52 = x_70;
x_53 = x_69;
x_54 = x_71;
x_55 = x_72;
x_56 = x_74;
x_57 = x_73;
x_58 = x_75;
x_59 = x_76;
x_60 = x_77;
x_61 = x_81;
goto block_65;
}
}
block_110:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_string_utf8_next_fast(x_1, x_22);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_85);
x_86 = x_30;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_109, 0, x_21);
lean_ctor_set(x_109, 1, x_85);
lean_ctor_set(x_109, 2, x_24);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_109, sizeof(void*)*3 + 1, x_25);
lean_ctor_set_uint8(x_109, sizeof(void*)*3 + 2, x_26);
lean_ctor_set_uint8(x_109, sizeof(void*)*3 + 3, x_27);
lean_ctor_set_uint8(x_109, sizeof(void*)*3 + 4, x_28);
x_86 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; uint32_t x_99; uint8_t x_100; 
x_87 = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(x_84, x_32, x_1, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_87, sizeof(void*)*3);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_87, sizeof(void*)*3 + 1);
x_93 = lean_ctor_get_uint8(x_87, sizeof(void*)*3 + 2);
x_94 = lean_ctor_get_uint8(x_87, sizeof(void*)*3 + 3);
x_95 = lean_ctor_get_uint8(x_87, sizeof(void*)*3 + 4);
x_96 = lean_string_utf8_extract(x_1, x_22, x_89);
lean_dec(x_22);
x_97 = l_Lean_Name_str___override(x_3, x_96);
x_98 = lean_string_utf8_get(x_1, x_89);
x_99 = 46;
x_100 = lean_uint32_dec_eq(x_98, x_99);
if (x_100 == 0)
{
x_5 = x_91;
x_6 = x_88;
x_7 = x_87;
x_8 = x_92;
x_9 = x_94;
x_10 = x_90;
x_11 = x_97;
x_12 = x_95;
x_13 = x_89;
x_14 = x_93;
x_15 = x_100;
goto block_20;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_string_utf8_next(x_1, x_89);
x_102 = lean_string_utf8_at_end(x_1, x_101);
if (x_102 == 0)
{
uint32_t x_103; uint32_t x_104; uint8_t x_105; 
x_103 = lean_string_utf8_get_fast(x_1, x_101);
lean_dec(x_101);
x_104 = 65;
x_105 = lean_uint32_dec_le(x_104, x_103);
if (x_105 == 0)
{
x_66 = x_88;
x_67 = x_91;
x_68 = x_87;
x_69 = x_100;
x_70 = x_92;
x_71 = x_103;
x_72 = x_94;
x_73 = x_97;
x_74 = x_90;
x_75 = x_95;
x_76 = x_89;
x_77 = x_93;
goto block_82;
}
else
{
uint32_t x_106; uint8_t x_107; 
x_106 = 90;
x_107 = lean_uint32_dec_le(x_103, x_106);
if (x_107 == 0)
{
x_66 = x_88;
x_67 = x_91;
x_68 = x_87;
x_69 = x_100;
x_70 = x_92;
x_71 = x_103;
x_72 = x_94;
x_73 = x_97;
x_74 = x_90;
x_75 = x_95;
x_76 = x_89;
x_77 = x_93;
goto block_82;
}
else
{
x_5 = x_91;
x_6 = x_88;
x_7 = x_87;
x_8 = x_92;
x_9 = x_94;
x_10 = x_90;
x_11 = x_97;
x_12 = x_95;
x_13 = x_89;
x_14 = x_93;
x_15 = x_100;
goto block_20;
}
}
}
else
{
lean_dec(x_101);
x_5 = x_91;
x_6 = x_88;
x_7 = x_87;
x_8 = x_92;
x_9 = x_94;
x_10 = x_90;
x_11 = x_97;
x_12 = x_95;
x_13 = x_89;
x_14 = x_93;
x_15 = x_83;
goto block_20;
}
}
}
}
block_114:
{
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_del_object(x_30);
lean_dec(x_24);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_112 = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1));
x_113 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_113, 0, x_21);
lean_ctor_set(x_113, 1, x_22);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 1, x_25);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 2, x_26);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 3, x_27);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 4, x_28);
return x_113;
}
else
{
x_84 = x_111;
goto block_110;
}
}
block_119:
{
if (x_115 == 0)
{
uint32_t x_116; uint8_t x_117; 
x_116 = 95;
x_117 = lean_uint32_dec_eq(x_32, x_116);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = l_Lean_isLetterLike(x_32);
x_111 = x_118;
goto block_114;
}
else
{
x_111 = x_117;
goto block_114;
}
}
else
{
x_84 = x_115;
goto block_110;
}
}
block_124:
{
uint32_t x_120; uint8_t x_121; 
x_120 = 97;
x_121 = lean_uint32_dec_le(x_120, x_32);
if (x_121 == 0)
{
x_115 = x_121;
goto block_119;
}
else
{
uint32_t x_122; uint8_t x_123; 
x_122 = 122;
x_123 = lean_uint32_dec_le(x_32, x_122);
x_115 = x_123;
goto block_119;
}
}
}
}
else
{
lean_object* x_189; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_189 = l_Lean_ParseImports_State_mkEOIError(x_4);
return x_189;
}
block_20:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec(x_5);
x_16 = lean_apply_3(x_2, x_11, x_1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_7);
x_17 = lean_string_utf8_next(x_1, x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 4, x_12);
x_3 = x_11;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_7 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 2, x_4);
x_8 = l_Lean_ParseImports_State_pushImport(x_7, x_3);
x_9 = l_Lean_ParseImports_whitespace(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_15 = x_9;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_17; 
x_17 = 0;
if (x_14 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
if (x_16 == 0)
{
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_14);
x_19 = x_21;
goto block_20;
}
block_20:
{
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 3, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 4, x_17);
return x_19;
}
}
else
{
lean_object* x_22; 
if (x_16 == 0)
{
x_22 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_13);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_14);
x_22 = x_24;
goto block_23;
}
block_23:
{
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 3, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 4, x_17);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_moduleIdent___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Lean_ParseImports_moduleIdent___closed__0));
x_4 = lean_box(0);
x_5 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_atomic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_apply_2(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 4);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_dec(x_21);
x_13 = x_5;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_4);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 3, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 4, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_2(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 4);
x_13 = lean_nat_dec_eq(x_8, x_4);
lean_dec(x_4);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
return x_5;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_14 = x_5;
x_15 = x_22;
goto block_21;
}
else
{
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 2, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 3, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 4, x_12);
x_18 = x_20;
goto block_19;
}
block_19:
{
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_16);
return x_18;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
if (x_26 == 0)
{
lean_dec(x_4);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_41; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 3);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_5, 1);
lean_dec(x_43);
x_33 = x_5;
x_34 = x_41;
goto block_40;
}
else
{
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 0;
x_36 = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (x_34 == 0)
{
lean_ctor_set(x_33, 2, x_36);
lean_ctor_set(x_33, 1, x_4);
x_37 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 3, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 4, x_32);
x_37 = x_39;
goto block_38;
}
block_38:
{
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_35);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
x_9 = x_2;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
if (x_10 == 0)
{
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_8);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 3, x_11);
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
x_23 = x_2;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
if (x_24 == 0)
{
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 2, x_21);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 4, x_22);
x_26 = x_28;
goto block_27;
}
block_27:
{
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_1);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 3, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_ParseImports_setIsModule___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_setIsModule___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_ParseImports_setIsModule(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_10 = x_1;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_12; 
x_12 = 1;
if (x_6 == 0)
{
lean_object* x_13; 
if (x_11 == 0)
{
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
return x_13;
}
}
else
{
lean_object* x_16; 
if (x_11 == 0)
{
x_16 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 4, x_9);
x_16 = x_18;
goto block_17;
}
block_17:
{
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setMeta___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setMeta___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setMeta(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_10 = x_1;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_12; 
x_12 = 1;
if (x_6 == 0)
{
lean_object* x_13; 
if (x_11 == 0)
{
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
return x_13;
}
}
else
{
lean_object* x_16; 
if (x_11 == 0)
{
x_16 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 4, x_9);
x_16 = x_18;
goto block_17;
}
block_17:
{
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 3, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setExported___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setExported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setExported(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_10 = x_1;
x_11 = x_20;
goto block_19;
}
else
{
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_12; 
x_12 = 1;
if (x_6 == 0)
{
lean_object* x_13; 
if (x_11 == 0)
{
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
return x_13;
}
}
else
{
lean_object* x_16; 
if (x_11 == 0)
{
x_16 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 3, x_8);
x_16 = x_18;
goto block_17;
}
block_17:
{
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 4, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setImportAll___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_setImportAll(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; uint8_t x_13; 
x_7 = 1;
x_13 = lean_string_utf8_at_end(x_2, x_5);
if (x_13 == 0)
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_string_utf8_get_fast(x_1, x_4);
x_15 = lean_string_utf8_get_fast(x_2, x_5);
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_3;
goto block_12;
}
else
{
if (x_13 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_18 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_3;
goto block_12;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_3;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1));
x_10 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 2, x_6);
x_11 = l_Lean_ParseImports_State_pushImport(x_10, x_8);
return x_11;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_34; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_3, 1);
lean_dec(x_35);
x_27 = x_3;
x_28 = x_34;
goto block_33;
}
else
{
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
x_29 = x_27;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 1, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 2, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 3, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 4, x_26);
x_29 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_ParseImports_whitespace(x_2, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_24; 
x_24 = lean_string_utf8_at_end(x_1, x_4);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_string_utf8_at_end(x_2, x_5);
if (x_25 == 0)
{
uint32_t x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_string_utf8_get_fast(x_1, x_4);
x_27 = lean_string_utf8_get_fast(x_2, x_5);
x_28 = lean_uint32_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_6 = x_3;
goto block_23;
}
else
{
if (x_25 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_30 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_29;
x_5 = x_30;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_6 = x_3;
goto block_23;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_6 = x_3;
goto block_23;
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_46; 
lean_dec(x_4);
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_3, 1);
lean_dec(x_47);
x_39 = x_3;
x_40 = x_46;
goto block_45;
}
else
{
lean_inc(x_34);
lean_inc(x_32);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_5);
x_41 = x_39;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_33);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 2, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 3, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 4, x_38);
x_41 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_42; 
x_42 = l_Lean_ParseImports_whitespace(x_2, x_41);
return x_42;
}
}
}
block_23:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 2);
x_12 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 3);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 4);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_6, 2);
lean_dec(x_22);
x_14 = x_6;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = ((lean_object*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1));
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_10);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 2, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 3, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 4, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
else
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_12 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_21 = x_3;
x_22 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_5);
x_23 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 3, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 4, x_20);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_ParseImports_whitespace(x_2, x_23);
x_25 = l_Lean_ParseImports_setImportAll___redArg(x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
else
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_12 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_21 = x_3;
x_22 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_5);
x_23 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 3, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 4, x_20);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_ParseImports_whitespace(x_2, x_23);
x_25 = l_Lean_ParseImports_setExported___redArg(x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
else
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_12 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_21 = x_3;
x_22 = x_29;
goto block_28;
}
else
{
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_5);
x_23 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 3, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 4, x_20);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_ParseImports_whitespace(x_2, x_23);
x_25 = l_Lean_ParseImports_setMeta___redArg(x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_16; lean_object* x_43; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_73 = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1));
x_74 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_75 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(x_73, x_1, x_2, x_74, x_3);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 1)
{
lean_dec_ref(x_76);
x_43 = x_75;
goto block_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
x_78 = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2));
x_79 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(x_78, x_1, x_75, x_74, x_77);
x_80 = lean_ctor_get(x_79, 2);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 1)
{
lean_dec_ref(x_80);
x_43 = x_79;
goto block_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3));
x_83 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(x_82, x_1, x_79, x_74, x_81);
x_43 = x_83;
goto block_72;
}
}
block_15:
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_6, x_3);
lean_dec(x_3);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_4;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_4);
x_12 = 0;
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_9);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_10);
return x_14;
}
}
block_42:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 2);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 3);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 4);
x_4 = x_16;
x_5 = x_18;
x_6 = x_19;
x_7 = x_20;
x_8 = x_21;
x_9 = x_22;
x_10 = x_23;
goto block_15;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
if (x_24 == 0)
{
lean_dec(x_3);
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint8_t x_39; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 2);
x_29 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 3);
x_30 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 4);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_16, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_dec(x_41);
x_31 = x_16;
x_32 = x_39;
goto block_38;
}
else
{
lean_inc(x_26);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = x_39;
goto block_38;
}
block_38:
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = ((lean_object*)(l_Lean_ParseImports_manyImports___closed__1));
if (x_32 == 0)
{
lean_ctor_set(x_31, 2, x_34);
lean_ctor_set(x_31, 1, x_3);
x_35 = x_31;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 2, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 3, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 4, x_30);
x_35 = x_37;
goto block_36;
}
block_36:
{
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_33);
return x_35;
}
}
}
}
}
block_72:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 2);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_inc_ref(x_44);
lean_dec_ref(x_1);
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get_uint8(x_43, sizeof(void*)*3);
x_47 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 1);
x_48 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 2);
x_49 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 3);
x_50 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 4);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_43, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_43, 1);
lean_dec(x_59);
x_51 = x_43;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_45);
lean_dec(x_43);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
lean_inc(x_3);
lean_inc_ref(x_45);
if (x_52 == 0)
{
lean_ctor_set(x_51, 1, x_3);
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_47);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 3, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 4, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
lean_inc(x_3);
x_4 = x_53;
x_5 = x_45;
x_6 = x_3;
x_7 = x_47;
x_8 = x_48;
x_9 = x_49;
x_10 = x_50;
goto block_15;
}
}
}
else
{
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; 
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 1);
x_63 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 2);
x_64 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 3);
x_65 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 4);
x_4 = x_43;
x_5 = x_60;
x_6 = x_61;
x_7 = x_62;
x_8 = x_63;
x_9 = x_64;
x_10 = x_65;
goto block_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
x_67 = ((lean_object*)(l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0));
x_68 = lean_unsigned_to_nat(0u);
x_69 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(x_67, x_1, x_43, x_68, x_66);
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 1)
{
lean_dec_ref(x_70);
x_16 = x_69;
goto block_42;
}
else
{
lean_object* x_71; 
lean_dec(x_70);
lean_inc_ref(x_1);
x_71 = l_Lean_ParseImports_moduleIdent(x_1, x_69);
x_16 = x_71;
goto block_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_setIsModule___redArg(x_6, x_3);
return x_11;
}
else
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lean_ParseImports_setIsModule___redArg(x_6, x_3);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_ParseImports_setIsModule___redArg(x_6, x_3);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_32; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 3);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_24 = x_3;
x_25 = x_32;
goto block_31;
}
else
{
lean_inc(x_19);
lean_inc(x_17);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_26; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_5);
x_26 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 2, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 3, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 4, x_23);
x_26 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_ParseImports_whitespace(x_2, x_26);
x_28 = l_Lean_ParseImports_setIsModule___redArg(x_6, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = ((lean_object*)(l_Lean_ParseImports_main___closed__0));
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(x_4, x_1, x_2, x_5, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = ((lean_object*)(l_Lean_ParseImports_main___closed__1));
x_10 = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(x_9, x_1, x_6, x_5, x_8);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(x_1, x_10);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = ((lean_object*)(l_Lean_parseImports_x27___closed__1));
x_5 = l_Lean_ParseImports_whitespace(x_1, x_4);
lean_inc_ref(x_1);
x_6 = l_Lean_ParseImports_main(x_1, x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_31; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
x_10 = x_7;
x_11 = x_31;
goto block_30;
}
else
{
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = l_String_toFileMap(x_1);
x_13 = l_Lean_FileMap_toPosition(x_12, x_8);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = ((lean_object*)(l_Lean_parseImports_x27___closed__2));
x_17 = lean_string_append(x_2, x_16);
x_18 = l_Nat_reprFast(x_14);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_string_append(x_19, x_16);
x_21 = l_Nat_reprFast(x_15);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l_Lean_parseImports_x27___closed__3));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 18);
lean_ctor_set(x_10, 0, x_25);
x_26 = x_10;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_25);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
lean_dec_ref(x_6);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_parseImports_x27(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_instToJsonModuleHeader_toJson(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_21; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
x_4 = x_1;
x_5 = x_21;
goto block_20;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__0));
x_7 = l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(x_6, x_2);
x_8 = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__1));
x_9 = l_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(x_3);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
x_10 = x_4;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_10 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_instToJsonPrintImportResult_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(l_Lean_instToJsonPrintImportsResult_toJson___closed__0));
x_3 = l_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = ((lean_object*)(l_Lean_instToJsonPrintImportResult_toJson___closed__2));
x_9 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(x_7, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_24; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_24 = l_IO_FS_readFile(x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_parseImports_x27(x_25, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_36; 
x_27 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_28 = x_26;
x_29 = x_36;
goto block_35;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
x_30 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_27);
x_30 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0));
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_10 = x_32;
goto block_15;
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec_ref(x_26);
x_16 = x_37;
goto block_23;
}
}
else
{
lean_object* x_38; 
lean_dec(x_7);
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_38);
lean_dec_ref(x_24);
x_16 = x_38;
goto block_23;
}
block_15:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_box(0);
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_array_push(x_20, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_10 = x_22;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00Lean_printImportsJson_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson(lean_object* x_1) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_instToJsonPrintImportsResult_toJson(x_6);
x_8 = l_Lean_Json_compress(x_7);
x_9 = l_IO_println___at___00Lean_printImportsJson_spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 0);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
x_11 = x_5;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_printImportsJson___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_printImportsJson(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin)
;
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
res = initialize_Lean_Parser_Module(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ParseImportsFast(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ParseImportsFast(builtin);
}
#ifdef __cplusplus
}
#endif
